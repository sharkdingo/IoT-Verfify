import path from 'node:path'
import { type APIRequestContext, type Page } from '@playwright/test'
import { apiBaseURL, createAuthenticatedUser, expect, test, type AuthUser } from './support/auth'

/**
 * Verifies the board's URL contract against a real backend: which state is deep-linkable,
 * that refresh and Back/Forward restore the same surface, and that a dead link degrades to
 * the plain board instead of a fabricated empty result.
 *
 * Rules under test: docs/guides/frontend-ui-conventions.md
 */

test.describe.configure({ mode: 'serial' })
test.setTimeout(180_000)

const seedSession = async (page: Page, auth: AuthUser) => {
  await page.addInitScript(({ token, user }) => {
    window.localStorage.setItem('iot_verify_token', token)
    window.localStorage.setItem('iot_verify_user', JSON.stringify(user))
    window.localStorage.setItem('locale', 'en')
    window.localStorage.setItem('iot_verify_theme', 'light')
  }, {
    token: auth.token,
    user: { userId: auth.userId, phone: auth.phone, username: auth.username }
  })
}

const openBoard = async (page: Page, auth: AuthUser, target = '/#/board') => {
  await seedSession(page, auth)
  await page.goto(target)
  await expect(page.locator('.iot-board')).toBeVisible({ timeout: 60_000 })
}

/** The query string of the current hash route, e.g. `run=verification:12`. */
const boardQuery = (page: Page) => new URL(page.url()).hash.split('?')[1] ?? ''

/**
 * Imports a violating scene and runs one synchronous verification saved to history, so the
 * tests have a real persisted run id to address.
 */
const seedVerificationRun = async (
  page: Page,
  request: APIRequestContext,
  auth: AuthUser
): Promise<number> => {
  const scenePath = path.resolve(
    process.cwd(), '..', 'docs', 'examples', 'default-climate-conflict-scene.json'
  )
  await page.getByTestId('scene-import-file').setInputFiles(scenePath)
  await page.getByRole('dialog', { name: 'Confirm Full Scene Replacement' })
    .getByRole('button', { name: 'Replace in full' })
    .click()
  await expect.poll(async () => {
    const response = await request.get(`${apiBaseURL}/api/board/rules`, {
      headers: { Authorization: `Bearer ${auth.token}` }
    })
    return (await response.json())?.data?.length ?? 0
  }, { timeout: 60_000 }).toBeGreaterThan(0)

  const verifyResponse = page.waitForResponse(response =>
    response.request().method() === 'POST'
      && new URL(response.url()).pathname === '/api/verify')
  await page.getByTestId('open-verification-panel').click()
  await page.getByTestId('verification-mode-sync').click()
  await page.getByTestId('run-verification').click()
  const body = await (await verifyResponse).json()
  await expect(page.getByTestId('verification-result-dialog')).toBeVisible({ timeout: 90_000 })

  const runId = body?.data?.historyPersistence?.runId
  expect(runId, JSON.stringify(body?.data?.historyPersistence)).toBeTruthy()
  return runId as number
}

const replaceBoardWithEmptyScene = async (request: APIRequestContext, auth: AuthUser) => {
  const headers = { Authorization: `Bearer ${auth.token}` }
  const previewResponse = await request.get(`${apiBaseURL}/api/board/replacement-preview`, { headers })
  expect(previewResponse.ok(), await previewResponse.text()).toBeTruthy()
  const preview = await previewResponse.json()
  expect(preview?.data?.impactToken, JSON.stringify(preview)).toBeTruthy()

  const replaceResponse = await request.post(`${apiBaseURL}/api/board/batch`, {
    headers,
    data: {
      impactToken: preview.data.impactToken,
      nodes: [],
      environmentVariables: [],
      rules: [],
      specs: [],
      templateSnapshots: []
    }
  })
  expect(replaceResponse.ok(), await replaceResponse.text()).toBeTruthy()
}

test.describe('board run deep links', () => {
  test('deep-links a verification run and survives refresh, Back, and Forward', async ({ page, request }) => {
    const auth = await createAuthenticatedUser(request)
    await openBoard(page, auth)
    const runId = await seedVerificationRun(page, request, auth)

    // A fresh run is addressable once saved, and closing clears the params.
    await page.getByTestId('close-verification-result').click()
    await expect(page.getByTestId('verification-result-dialog')).toBeHidden()
    expect(boardQuery(page)).not.toContain('run=')

    // A pasted link reopens the same run from a cold load.
    await page.goto(`/#/board?run=verification:${runId}`)
    await expect(page.getByTestId('verification-result-dialog')).toBeVisible({ timeout: 60_000 })

    // Refresh keeps it open: the URL, not component state, is the authority.
    await page.reload()
    await expect(page.getByTestId('verification-result-dialog')).toBeVisible({ timeout: 60_000 })
    expect(boardQuery(page)).toContain(`run=verification:${runId}`)

    // Opening from history is a push, so Back closes and Forward reopens.
    await page.goto('/#/board')
    await expect(page.locator('.iot-board')).toBeVisible({ timeout: 60_000 })
    await expect(page.getByTestId('verification-result-dialog')).toHaveCount(0)

    await page.getByTestId('open-history-panel').click()
    // Completed runs live in the History Results layer, not the active-task layer.
    await page.getByTestId('history-layer-results').click()
    await page.getByTestId(`open-verification-run-${runId}`).click()
    await expect(page.getByTestId('verification-result-dialog')).toBeVisible({ timeout: 60_000 })
    expect(boardQuery(page)).toContain(`run=verification:${runId}`)

    await page.goBack()
    await expect(page.getByTestId('verification-result-dialog')).toHaveCount(0)
    await page.goForward()
    await expect(page.getByTestId('verification-result-dialog')).toBeVisible({ timeout: 60_000 })
  })

  test('degrades malformed deep links to the plain board without inventing a result', async ({ page, request }) => {
    const auth = await createAuthenticatedUser(request)

    for (const query of [
      'run=verification:abc',
      'run=nonsense:1',
      'run=verification:0',
      'trace=5',
      'run=exploration:3&trace=9',
      'run=simulation:2&finding=4'
    ]) {
      await openBoard(page, auth, `/#/board?${query}`)
      await expect(page.getByTestId('verification-result-dialog')).toHaveCount(0)
      // Dead params are stripped so a refresh stays clean.
      expect(boardQuery(page), query).not.toContain('run=')
      expect(boardQuery(page), query).not.toContain('trace=')
      expect(boardQuery(page), query).not.toContain('finding=')
    }
  })

  test('explains a link naming a run this account cannot open', async ({ page, request }) => {
    const auth = await createAuthenticatedUser(request)
    await openBoard(page, auth, '/#/board?run=verification:999999')

    const banner = page.getByTestId('board-deep-link-unavailable')
    await expect(banner).toBeVisible({ timeout: 60_000 })
    // Persistent and dismissible, and never a fabricated empty verdict.
    await expect(banner).toHaveAttribute('role', 'alert')
    await expect(page.getByTestId('verification-result-dialog')).toHaveCount(0)
    expect(boardQuery(page)).not.toContain('run=')

    await page.getByTestId('dismiss-deep-link-unavailable').click()
    await expect(banner).toHaveCount(0)
    // The board stays fully usable after a dead link.
    await page.getByTestId('open-verification-panel').click()
    await expect(page.getByTestId('verification-panel')).toBeVisible()
  })

  test('deep-links a counterexample trace under its owning run', async ({ page, request }) => {
    const auth = await createAuthenticatedUser(request)
    await openBoard(page, auth)
    const runId = await seedVerificationRun(page, request, auth)

    // The trace id comes from the run's own persisted counterexamples, which is what a
    // shared link would reference.
    const tracesResponse = await request.get(`${apiBaseURL}/api/verify/runs/${runId}/traces`, {
      headers: { Authorization: `Bearer ${auth.token}` }
    })
    const traces = (await tracesResponse.json())?.data ?? []
    const traceId = traces[0]?.id
    expect(traceId, JSON.stringify(traces).slice(0, 200)).toBeTruthy()

    // The current board is deliberately replaced after the run completes. Replay must use the
    // persisted run snapshot, then return to this new empty board when the user closes it.
    await replaceBoardWithEmptyScene(request, auth)

    await page.goto(`/#/board?run=verification:${runId}&trace=${traceId}`)
    await expect(page.getByTestId('trace-timeline')).toBeVisible({ timeout: 90_000 })
    expect(boardQuery(page)).toContain(`trace=${traceId}`)
    await expect(page.locator('[data-node-id="temperature_1"]')).toBeVisible()
    await expect(page.locator('[data-node-id="ac_1"]')).toBeVisible()
    await expect(page.getByTestId('canvas-board')).toContainText('Living-room Temperature Sensor')

    // Refresh restores the same replay, not just the run.
    await page.reload()
    await expect(page.getByTestId('trace-timeline')).toBeVisible({ timeout: 90_000 })
    expect(boardQuery(page)).toContain(`run=verification:${runId}`)
    expect(boardQuery(page)).toContain(`trace=${traceId}`)

    // Closing the replay leaves the artifact entirely, so the whole deep link goes with it.
    // Leaving `run=` behind would let the sync reopen the result surface the user just left.
    await page.getByTestId('trace-timeline-close').click()
    await expect(page.getByTestId('trace-timeline')).toBeHidden()
    expect(boardQuery(page)).not.toContain('trace=')
    expect(boardQuery(page)).not.toContain('run=')
    await expect(page.getByTestId('verification-result-dialog')).toHaveCount(0)
    await expect(page.locator('[data-node-id="temperature_1"]')).toHaveCount(0)
    await expect(page.locator('[data-node-id="ac_1"]')).toHaveCount(0)
  })

  test('keeps server-persisted layout state out of the URL', async ({ page, request }) => {
    const auth = await createAuthenticatedUser(request)
    await openBoard(page, auth)

    // Panel layout and canvas transform are persisted per user server-side; putting them in
    // the URL would create a second authority for the same value.
    await page.getByTestId('control-tab-rules').click()
    await expect(page.getByTestId('control-section-rules')).toBeVisible()
    await page.getByTestId('open-verification-panel').click()
    await expect(page.getByTestId('verification-panel')).toBeVisible()

    expect(boardQuery(page)).toBe('')
  })

  test('restores a deep-linked run at a narrow width and from the keyboard', async ({ page, request }) => {
    const auth = await createAuthenticatedUser(request)
    await page.setViewportSize({ width: 800, height: 720 })
    await openBoard(page, auth)
    const runId = await seedVerificationRun(page, request, auth)

    await page.goto(`/#/board?run=verification:${runId}`)
    const dialog = page.getByTestId('verification-result-dialog')
    await expect(dialog).toBeVisible({ timeout: 60_000 })
    // A deep-linked modal must be a real modal at every width (the testid is on the
    // overlay; the focus-trapped surface inside it carries the dialog semantics).
    await expect(dialog.locator('[role="dialog"]')).toHaveAttribute('aria-modal', 'true')

    // Escape is enough to leave, and it clears the deep link rather than stranding the URL.
    await page.keyboard.press('Escape')
    await expect(dialog).toBeHidden()
    expect(boardQuery(page)).not.toContain('run=')
  })
})

test.describe('destructive confirmation behaviour', () => {
  test('treats cancel as an ordinary no and survives repeated clicks', async ({ page, request }) => {
    const auth = await createAuthenticatedUser(request)
    await openBoard(page, auth)

    const clearScene = page.getByTestId('scene-clear')
    await clearScene.click()
    const box = page.locator('.el-message-box')
    await expect(box).toBeVisible()

    // Cancelling must not raise an error toast: declining is a normal outcome.
    await box.getByRole('button', { name: /Cancel|取消/ }).click()
    await expect(box).toBeHidden()
    await expect(page.locator('.el-message--error')).toHaveCount(0)

    // Re-opening works, and a second trigger click does not stack a second confirmation.
    await clearScene.click()
    await expect(box).toBeVisible()
    expect(await page.locator('.el-message-box').count()).toBe(1)

    // Escape dismisses it exactly like Cancel, leaving the board untouched and usable.
    await page.keyboard.press('Escape')
    await expect(box).toBeHidden()
    await page.getByTestId('open-verification-panel').click()
    await expect(page.getByTestId('verification-panel')).toBeVisible()
  })
})

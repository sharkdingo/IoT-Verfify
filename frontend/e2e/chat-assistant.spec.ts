import path from 'node:path'
import { type APIRequestContext, type Page } from '@playwright/test'
import {
  apiBaseURL,
  createAuthenticatedUser,
  expect,
  test,
  type AuthUser
} from './support/auth'
import type { PersistedChatMessage, StreamProgress } from '../src/types/chat'

const rgba = (value: string): [number, number, number, number] => {
  const channels = value.match(/[\d.]+/g)?.map(Number)
  if (!channels || channels.length < 3 || channels.slice(0, 3).some(Number.isNaN)) {
    throw new Error(`Expected an RGB color, received: ${value}`)
  }
  return [channels[0], channels[1], channels[2], channels[3] ?? 1]
}

const relativeLuminance = (channels: [number, number, number]): number => {
  const linear = channels.map(channel => {
    const normalized = channel / 255
    return normalized <= 0.04045
      ? normalized / 12.92
      : ((normalized + 0.055) / 1.055) ** 2.4
  })
  return 0.2126 * linear[0] + 0.7152 * linear[1] + 0.0722 * linear[2]
}

const contrastRatio = (foreground: string, background: string): number => {
  const [red, green, blue, alpha] = rgba(foreground)
  const [backgroundRed, backgroundGreen, backgroundBlue] = rgba(background)
  const foregroundLuminance = relativeLuminance([
    red * alpha + backgroundRed * (1 - alpha),
    green * alpha + backgroundGreen * (1 - alpha),
    blue * alpha + backgroundBlue * (1 - alpha)
  ])
  const backgroundLuminance = relativeLuminance([
    backgroundRed,
    backgroundGreen,
    backgroundBlue
  ])
  const lighter = Math.max(foregroundLuminance, backgroundLuminance)
  const darker = Math.min(foregroundLuminance, backgroundLuminance)
  return (lighter + 0.05) / (darker + 0.05)
}

const surfaceLuminance = (color: string) => {
  const [red, green, blue] = rgba(color)
  return relativeLuminance([red, green, blue])
}

const unwrap = async <T>(response: Awaited<ReturnType<APIRequestContext['get']>>): Promise<T> => {
  expect(response.ok(), await response.text()).toBeTruthy()
  const body = await response.json()
  expect(body.code, JSON.stringify(body)).toBe(200)
  return body.data as T
}

const openWorkspace = async (page: Page, auth: AuthUser, theme: 'light' | 'dark' = 'light') => {
  await page.addInitScript(({ token, user, themeMode }) => {
    window.localStorage.setItem('iot_verify_token', token)
    window.localStorage.setItem('iot_verify_user', JSON.stringify(user))
    window.localStorage.setItem('iot_verify_theme', themeMode)
    window.localStorage.setItem('locale', 'zh-CN')
  }, {
    token: auth.token,
    themeMode: theme,
    user: {
      userId: auth.userId,
      phone: auth.phone,
      username: auth.username
    }
  })

  await page.goto('/#/board')
  await expect(page.getByTestId('board-root')).toBeVisible({ timeout: 30_000 })
}

const installPersistedPartialChatMock = async (
  page: Page,
  sessionId: string,
  assistantContent: string,
  beforeResponse?: () => Promise<void>
) => {
  let messages: PersistedChatMessage[] = []

  await page.route(`**/api/chat/sessions/${sessionId}/messages**`, async route => {
    await route.fulfill({
      status: 200,
      contentType: 'application/json; charset=UTF-8',
      body: JSON.stringify({
        code: 200,
        data: { messages, nextBeforeId: null, hasMore: false }
      })
    })
  })
  await page.route('**/api/chat/completions', async route => {
    await beforeResponse?.()
    const request = route.request().postDataJSON() as {
      sessionId: string
      content: string
      turnId: string
    }
    expect(request.sessionId).toBe(sessionId)
    expect(request.turnId.trim()).not.toBe('')
    const executionTrace: StreamProgress[] = [
      { stage: 'CONTEXT_READY' },
      { stage: 'PLANNING', round: 1 },
      { stage: 'WRITING_RESPONSE', round: 1 }
    ]
    const createdAt = new Date().toISOString()
    messages = [
      {
        id: 1,
        sessionId,
        role: 'user',
        content: request.content,
        turnId: request.turnId,
        createdAt
      },
      {
        id: 2,
        sessionId,
        role: 'assistant',
        content: assistantContent,
        turnId: request.turnId,
        createdAt,
        executionStatus: 'PARTIAL',
        executionTrace
      }
    ]
    const frames = [
      ...executionTrace.map(progress => ({ progress })),
      { content: assistantContent },
      { terminal: { turnId: request.turnId, executionStatus: 'PARTIAL' } }
    ]
    await route.fulfill({
      status: 200,
      contentType: 'text/event-stream; charset=UTF-8',
      body: `${frames.map(frame => `data: ${JSON.stringify(frame)}`).join('\n\n')}\n\n`
    })
  })
}

test('reopening the assistant exposes existing history without creating or sending a chat', async ({ page, request }) => {
  const auth = await createAuthenticatedUser(request)
  const session = await unwrap<{ id: string; title: string }>(
    await request.post(`${apiBaseURL}/api/chat/sessions`, {
      headers: { Authorization: `Bearer ${auth.token}` }
    })
  )

  await openWorkspace(page, auth)

  await page.getByTestId('open-ai-assistant').click()
  await expect(page.getByTestId('chat-panel')).toBeVisible()
  await page.getByTestId('chat-sidebar-toggle').click()
  await expect(page.getByTestId(`chat-session-${session.id}`)).toBeVisible()

  await page.getByTestId('chat-sidebar-scrim').click()
  await page.getByTestId('chat-close').click()
  await expect(page.getByTestId('chat-panel')).toBeHidden()

  await page.getByTestId('open-ai-assistant').click()
  await expect(page.getByTestId('chat-panel')).toBeVisible()
  await page.getByTestId('chat-sidebar-toggle').click()
  await expect(page.getByTestId(`chat-session-${session.id}`)).toBeVisible()
})

test('keeps the pending reply status inside a compact assistant bubble', async ({ page, request }) => {
  const auth = await createAuthenticatedUser(request)
  const session = await unwrap<{ id: string }>(
    await request.post(`${apiBaseURL}/api/chat/sessions`, {
      headers: { Authorization: `Bearer ${auth.token}` }
    })
  )
  let releaseResponse!: () => void
  const responseGate = new Promise<void>(resolve => {
    releaseResponse = resolve
  })

  await installPersistedPartialChatMock(page, session.id, '已完成检查。', () => responseGate)
  await openWorkspace(page, auth)

  await page.getByTestId('open-ai-assistant').click()
  await page.getByTestId('chat-sidebar-toggle').click()
  await page.getByTestId(`chat-session-${session.id}`).click()
  await page.getByTestId('chat-input').fill('请检查当前画布')
  await page.getByTestId('chat-send').click()

  const pending = page.getByTestId('chat-assistant-pending')
  await expect(pending).toBeVisible()
  const layout = await pending.evaluate(element => {
    const bubble = element.closest('article')
    const row = element.closest('.msg-row')
    const bubbleRect = bubble?.getBoundingClientRect()
    const rowRect = row?.getBoundingClientRect()
    return {
      tagName: bubble?.tagName,
      compactClass: bubble?.classList.contains('assistant-pending-body'),
      bubbleWidth: bubbleRect?.width ?? 0,
      rowWidth: rowRect?.width ?? 0
    }
  })

  expect(layout).toMatchObject({ tagName: 'ARTICLE', compactClass: true })
  expect(layout.bubbleWidth).toBeGreaterThan(100)
  expect(layout.bubbleWidth).toBeLessThan(260)
  expect(layout.bubbleWidth).toBeLessThan(layout.rowWidth / 2)

  releaseResponse()
  await expect(pending).toBeHidden()
  const executionDetails = page.locator('details.chat-execution-trace')
  await expect(executionDetails).toBeVisible()
  // The newest completed turn keeps its reasoning open, so the trace is readable without a click;
  // a deliberate collapse is then honoured rather than being re-expanded.
  await expect(page.getByTestId('chat-execution-trace')).toBeVisible()
  await executionDetails.locator('summary').click()
  await expect(page.getByTestId('chat-execution-trace')).toBeHidden()
  await expect(page.getByTestId('chat-reconciliation-required')).toHaveCount(0)
  await expect(page.getByTestId('chat-history-retry')).toHaveCount(0)
})

test('renders assistant code blocks on a readable dark surface', async ({ page, request }) => {
  const auth = await createAuthenticatedUser(request)
  const session = await unwrap<{ id: string }>(
    await request.post(`${apiBaseURL}/api/chat/sessions`, {
      headers: { Authorization: `Bearer ${auth.token}` }
    })
  )
  const markdown = '```json\n{"status":"ok"}\n```'
  await installPersistedPartialChatMock(page, session.id, markdown)
  await openWorkspace(page, auth, 'dark')

  await page.getByTestId('open-ai-assistant').click()
  await page.getByTestId('chat-sidebar-toggle').click()
  await page.getByTestId(`chat-session-${session.id}`).click()
  await page.getByTestId('chat-input').fill('show status')
  await page.getByTestId('chat-send').click()

  const codeBlock = page.locator('.code-block-container')
  await expect(codeBlock).toBeVisible()
  await expect(codeBlock).toContainText('{"status":"ok"}')
  const executionDetails = page.locator('details.chat-execution-trace')
  await expect(executionDetails).toBeVisible()
  await expect(page.getByTestId('chat-execution-trace')).toBeVisible()
  await expect(page.getByTestId('chat-reconciliation-required')).toHaveCount(0)
  await expect(page.getByTestId('chat-history-retry')).toHaveCount(0)

  const surfaces = await codeBlock.evaluate(element => {
    const canvas = document.createElement('canvas')
    canvas.width = 1
    canvas.height = 1
    const context = canvas.getContext('2d', { willReadFrequently: true })
    if (!context) throw new Error('Canvas color normalization is unavailable')
    const toSrgb = (color: string) => {
      context.clearRect(0, 0, 1, 1)
      context.fillStyle = '#000'
      context.fillStyle = color
      context.fillRect(0, 0, 1, 1)
      const [red, green, blue, alpha] = context.getImageData(0, 0, 1, 1).data
      return `rgba(${red}, ${green}, ${blue}, ${alpha / 255})`
    }
    const bodyStyle = getComputedStyle(element)
    const header = element.querySelector<HTMLElement>('.code-header')
    const language = element.querySelector<HTMLElement>('.lang-label')
    const copy = element.querySelector<HTMLElement>('.copy-btn')
    if (!header || !language || !copy) throw new Error('Code block controls are missing')
    const headerStyle = getComputedStyle(header)
    const codeColors = [...element.querySelectorAll<HTMLElement>('.code-content code span')]
      .filter(token => token.textContent?.trim())
      .map(token => toSrgb(getComputedStyle(token).color))
    return {
      bodyBackground: toSrgb(bodyStyle.backgroundColor),
      headerBackground: toSrgb(headerStyle.backgroundColor),
      headerColors: [
        toSrgb(getComputedStyle(language).color),
        toSrgb(getComputedStyle(copy).color)
      ],
      codeColors
    }
  })
  expect(surfaceLuminance(surfaces.bodyBackground)).toBeLessThan(0.18)
  expect(surfaceLuminance(surfaces.headerBackground)).toBeLessThan(0.18)
  expect(surfaces.codeColors.length).toBeGreaterThan(0)
  for (const color of surfaces.codeColors) {
    expect(contrastRatio(color, surfaces.bodyBackground)).toBeGreaterThanOrEqual(4.5)
  }
  for (const color of surfaces.headerColors) {
    expect(contrastRatio(color, surfaces.headerBackground)).toBeGreaterThanOrEqual(4.5)
  }
})

// Scoped deliberately: this drives the REFRESH_DATA path with a mocked stream, so it verifies the
// *client* re-reads undo availability. The assistant's own journalling is covered end-to-end in
// live-ai-no-mock.spec.ts, which must stay the authority for that claim.
test('a rule_list refresh command makes the workspace re-read undo availability', async ({ page, request }) => {
  const auth = await createAuthenticatedUser(request)
  const headers = { Authorization: `Bearer ${auth.token}` }
  const rulesUrl = `${apiBaseURL}/api/board/rules`

  await openWorkspace(page, auth)

  // A real scene gives us device-referencing rules to delete.
  await page.getByTestId('scene-import-file').setInputFiles(path.resolve(
    process.cwd(), '..', 'docs', 'examples', 'default-climate-conflict-scene.json'))
  // The disabled state is applied locally the instant the journal is cleared, while confirming
  // availability GETs are still in flight — and a full scene replacement triggers several (the
  // journal-cleared re-read, the snapshot reload, the data-ready hook). Any of them can resolve after
  // the out-of-band delete below, legitimately report canUndo=true, and re-enable the button — failing
  // the negative assertion for a fixture-ordering reason rather than a product one. Waiting on the
  // *server's* view of availability is the deterministic barrier: once it reports an empty journal,
  // every in-flight read can only be reporting the same thing.
  await page.getByRole('dialog').getByRole('button', { name: /Replace in full|全量替换/ }).click()
  // Scene replacement clears the journal, so this is a clean baseline.
  await expect(page.getByTestId('board-undo')).toBeDisabled({ timeout: 60_000 })
  await expect.poll(async () => (await unwrap<{ canUndo: boolean }>(
    await request.get(`${apiBaseURL}/api/board/edits/availability`, { headers }))).canUndo,
    { timeout: 60_000 }).toBe(false)
  await expect.poll(async () => (await unwrap<any[]>(await request.get(rulesUrl, { headers }))).length,
    { timeout: 60_000 }).toBeGreaterThan(0)
  const rules = await unwrap<any[]>(await request.get(rulesUrl, { headers }))

  // Delete through the same journal-recording endpoint the assistant's tools use. The model's
  // wording is not under test here; the contract is that an assistant-path edit is as reversible
  // as a user-path one.
  const deleted = await request.delete(`${rulesUrl}/${rules[0].id}`, { headers, data: rules[0] })
  expect(deleted.ok(), await deleted.text()).toBeTruthy()

  // The board has not been told anything yet, so it still shows no history.
  await expect(page.getByTestId('board-undo')).toBeDisabled()

  // Now deliver exactly the REFRESH_DATA command the backend emits after a rule tool runs.
  // Scoped to this test's freshly registered account: the backend allows only one active stream
  // request per chat session across all instances, so a hard-coded id made two parallel workers
  // collide — the second got a 409, its stream never delivered REFRESH_DATA, and the failure looked
  // like a broken refresh rather than a colliding fixture.
  const sessionId = `assistant-undo-session-${auth.userId}`
  await page.route('**/api/chat/sessions**', async route => {
    if (route.request().method() === 'POST') {
      await route.fulfill({
        status: 200,
        contentType: 'application/json; charset=UTF-8',
        // Full ChatSessionDto shape. The client validates every field, because `active` gates whether
        // a second assistant mutation may start — an absent flag would read as idle. A partial fixture
        // is rejected at the boundary, exactly as a partial server response would be.
        body: JSON.stringify({
          code: 200,
          data: {
            id: sessionId,
            userId: auth.userId,
            title: 'undo parity',
            createdAt: new Date().toISOString(),
            updatedAt: new Date().toISOString(),
            active: false
          }
        })
      })
      return
    }
    if (route.request().url().includes('/messages')) {
      await route.fulfill({
        status: 200,
        contentType: 'application/json; charset=UTF-8',
        body: JSON.stringify({ code: 200, data: { messages: [], nextBeforeId: null, hasMore: false } })
      })
      return
    }
    // GET /api/chat/sessions — the list, which must also be a well-formed session array.
    await route.fulfill({
      status: 200,
      contentType: 'application/json; charset=UTF-8',
      body: JSON.stringify({ code: 200, data: [] })
    })
  })
  await page.route('**/api/chat/completions', async route => {
    const { turnId } = route.request().postDataJSON() as { turnId: string }
    // A COMPLETED terminal must be backed by a paired usable tool result — the client rejects an
    // unproven completion, and the backend's own `hasCompletedToolEvidence` guarantees it never sends
    // one. So the mock carries the execution/result pair a real rule deletion would report.
    const frames = [
      { progress: { stage: 'CONTEXT_READY' } },
      { progress: { stage: 'TOOL_EXECUTION', toolName: 'manage_rule', round: 1 } },
      { progress: { stage: 'TOOL_RESULT', toolName: 'manage_rule', round: 1, outcome: 'USABLE' } },
      { command: { type: 'REFRESH_DATA', payload: { target: 'rule_list' } } },
      { content: 'Removed one rule.' },
      { terminal: { turnId, executionStatus: 'COMPLETED' } }
    ]
    await route.fulfill({
      status: 200,
      contentType: 'text/event-stream; charset=UTF-8',
      body: `${frames.map(frame => `data: ${JSON.stringify(frame)}`).join('\n\n')}\n\n`
    })
  })

  await page.getByTestId('open-ai-assistant').click()
  const composer = page.getByTestId('chat-input')
  await expect(composer).toBeVisible({ timeout: 30_000 })
  await composer.fill('Delete one rule.')
  await page.getByTestId('chat-send').click()

  // The refresh must re-read the journal, or the same edit would be undoable when the user made it
  // and not when the assistant did.
  await expect(page.getByTestId('board-undo')).toBeEnabled({ timeout: 60_000 })

  await page.getByTestId('board-undo').click()
  await expect.poll(async () => (await unwrap<any[]>(await request.get(rulesUrl, { headers }))).length,
    { timeout: 60_000 }).toBe(rules.length)
})

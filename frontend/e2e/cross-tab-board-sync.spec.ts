import { type Page } from '@playwright/test'
import { createAuthenticatedUser, expect, test, type AuthUser } from './support/auth'

test.describe.configure({ timeout: 120_000 })

const openWorkspace = async (page: Page, auth: AuthUser) => {
  await page.setViewportSize({ width: 1440, height: 900 })
  await page.addInitScript(({ token, user }) => {
    window.localStorage.setItem('iot_verify_token', token)
    window.localStorage.setItem('iot_verify_user', JSON.stringify(user))
    window.localStorage.setItem('iot_verify_theme', 'light')
    window.localStorage.setItem('locale', 'en')
  }, {
    token: auth.token,
    user: {
      userId: auth.userId,
      phone: auth.phone,
      username: auth.username
    }
  })
  await page.goto('/#/board')
  // New contexts may need to resolve the development server's eager icon URL modules.
  await expect(page.getByTestId('board-root')).toBeVisible({ timeout: 60_000 })
  await expect(page.getByTestId('scene-import')).toBeEnabled({ timeout: 60_000 })
}

const createDevice = async (page: Page, label: string) => {
  await page.getByTestId('control-tab-devices').click()
  await expect(page.getByTestId('control-section-devices')).toBeVisible()
  const templateSelect = page.getByTestId('single-device-template')
  await expect.poll(async () => templateSelect.locator('option').count()).toBeGreaterThan(1)
  const templateName = await templateSelect.locator('option').evaluateAll(options =>
    options.map(option => (option as HTMLOptionElement).value).find(Boolean) || '')
  expect(templateName).not.toBe('')
  await templateSelect.selectOption(templateName)
  await page.getByTestId('single-device-name').fill(label)
  await page.getByTestId('single-device-create').click()
  await expect(page.locator('.device-node').filter({ hasText: label })).toBeVisible({ timeout: 15_000 })
}

test('a successful Board mutation actively refreshes another visible tab', async ({ browser, request }) => {
  const auth = await createAuthenticatedUser(request, { usernamePrefix: 'tabsync' })
  const context = await browser.newContext()
  const writer = await context.newPage()
  await openWorkspace(writer, auth)
  const observer = await context.newPage()
  await openWorkspace(observer, auth)

  try {
    const label = `Cross tab ${Date.now()}`
    const observerRefresh = Promise.all([
      observer.waitForResponse(response =>
        response.request().method() === 'GET'
          && new URL(response.url()).pathname === '/api/board/snapshot'),
      observer.waitForResponse(response =>
        response.request().method() === 'GET'
          && new URL(response.url()).pathname === '/api/fuzz/model-fingerprint')
    ])
    await createDevice(writer, label)
    await observerRefresh

    await expect(observer.locator('.device-node').filter({ hasText: label })).toBeVisible({ timeout: 15_000 })
  } finally {
    await context.close()
  }
})

test('a delayed initial snapshot cannot suppress a newer cross-tab invalidation', async ({ browser, request }) => {
  const auth = await createAuthenticatedUser(request, { usernamePrefix: 'tabsyncrace' })
  const context = await browser.newContext()
  const writer = await context.newPage()
  await openWorkspace(writer, auth)
  const observer = await context.newPage()

  let snapshotRequestCount = 0
  let fingerprintRequestCount = 0
  let markInitialCaptured!: () => void
  const initialCaptured = new Promise<void>(resolve => { markInitialCaptured = resolve })
  let releaseInitialSnapshot!: () => void
  const initialSnapshotRelease = new Promise<void>(resolve => { releaseInitialSnapshot = resolve })
  await observer.route('**/api/board/snapshot', async route => {
    snapshotRequestCount += 1
    if (snapshotRequestCount !== 1) {
      await route.continue()
      return
    }
    const oldResponse = await route.fetch()
    markInitialCaptured()
    await initialSnapshotRelease
    await route.fulfill({ response: oldResponse })
  })
  observer.on('request', request => {
    if (request.method() === 'GET'
      && new URL(request.url()).pathname === '/api/fuzz/model-fingerprint') {
      fingerprintRequestCount += 1
    }
  })

  const openingObserver = openWorkspace(observer, auth)
  await initialCaptured

  try {
    const label = `Cross tab race ${Date.now()}`
    await createDevice(writer, label)
    releaseInitialSnapshot()
    await openingObserver

    await expect.poll(() => snapshotRequestCount).toBeGreaterThanOrEqual(2)
    await expect.poll(() => fingerprintRequestCount).toBeGreaterThanOrEqual(2)
    await expect(observer.locator('.device-node').filter({ hasText: label }))
      .toBeVisible({ timeout: 15_000 })
  } finally {
    releaseInitialSnapshot()
    await context.close()
  }
})

test('a hidden-tab invalidation is consumed by one foreground snapshot refresh', async ({ browser, request }) => {
  const auth = await createAuthenticatedUser(request, { usernamePrefix: 'tabsynchidden' })
  const context = await browser.newContext()
  const writer = await context.newPage()
  await openWorkspace(writer, auth)
  const observer = await context.newPage()
  await openWorkspace(observer, auth)

  let snapshotRequestCount = 0
  observer.on('request', request => {
    if (request.method() === 'GET'
      && new URL(request.url()).pathname === '/api/board/snapshot') {
      snapshotRequestCount += 1
    }
  })

  try {
    await observer.evaluate(() => {
      const state = window as Window & { __testVisibilityState?: DocumentVisibilityState }
      state.__testVisibilityState = 'hidden'
      Object.defineProperty(document, 'visibilityState', {
        configurable: true,
        get: () => state.__testVisibilityState
      })
      document.dispatchEvent(new Event('visibilitychange'))
    })

    const label = `Cross tab hidden ${Date.now()}`
    await createDevice(writer, label)
    await observer.waitForTimeout(300)
    expect(snapshotRequestCount).toBe(0)

    const foregroundRefresh = observer.waitForResponse(response =>
      response.request().method() === 'GET'
        && new URL(response.url()).pathname === '/api/board/snapshot')
    await observer.evaluate(() => {
      const state = window as Window & { __testVisibilityState?: DocumentVisibilityState }
      state.__testVisibilityState = 'visible'
      document.dispatchEvent(new Event('visibilitychange'))
      window.dispatchEvent(new Event('focus'))
    })
    await foregroundRefresh

    await expect(observer.locator('.device-node').filter({ hasText: label }))
      .toBeVisible({ timeout: 15_000 })
    await observer.waitForTimeout(300)
    expect(snapshotRequestCount).toBe(1)
  } finally {
    await context.close()
  }
})

test('switching accounts remounts the workspace and rebinds board invalidations', async ({ browser, request }) => {
  const alice = await createAuthenticatedUser(request, { usernamePrefix: 'tabsyncalice' })
  const bob = await createAuthenticatedUser(request, { usernamePrefix: 'tabsyncbob' })
  const context = await browser.newContext()
  const observer = await context.newPage()
  await openWorkspace(observer, alice)
  const storageController = await context.newPage()
  await storageController.goto('/')

  try {
    const aliceLabel = `Alice private ${Date.now()}`
    await createDevice(observer, aliceLabel)

    const bobSnapshot = observer.waitForResponse(response =>
      response.request().method() === 'GET'
        && new URL(response.url()).pathname === '/api/board/snapshot')
    await storageController.evaluate(({ token, user }) => {
      localStorage.setItem('iot_verify_token', token)
      localStorage.setItem('iot_verify_user', JSON.stringify(user))
      localStorage.setItem('iot_verify_auth_sync', JSON.stringify({
        token,
        user,
        updatedAt: Date.now()
      }))
    }, {
      token: bob.token,
      user: {
        userId: bob.userId,
        phone: bob.phone,
        username: bob.username
      }
    })
    await bobSnapshot

    await expect(observer.locator('.device-node').filter({ hasText: aliceLabel })).toHaveCount(0)
    await expect(observer.getByTestId('scene-import')).toBeEnabled({ timeout: 30_000 })

    const writer = await context.newPage()
    await openWorkspace(writer, bob)
    const bobLabel = `Bob synchronized ${Date.now()}`
    const observerRefresh = observer.waitForResponse(response =>
      response.request().method() === 'GET'
        && new URL(response.url()).pathname === '/api/board/snapshot')
    await createDevice(writer, bobLabel)
    await observerRefresh

    await expect(observer.locator('.device-node').filter({ hasText: bobLabel }))
      .toBeVisible({ timeout: 15_000 })
  } finally {
    await context.close()
  }
})

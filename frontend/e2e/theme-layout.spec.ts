import { type Locator, type Page } from '@playwright/test'
import {
  createAuthenticatedUser,
  createTestAccountCredentials,
  expect,
  test,
  trackTestAccount,
  type AuthUser
} from './support/auth'

type ThemeMode = 'light' | 'dark'

const parseRgb = (color: string) => {
  const rgbMatch = color.match(/rgba?\((\d+),\s*(\d+),\s*(\d+)/)
  if (rgbMatch) {
    return {
      r: Number(rgbMatch[1]),
      g: Number(rgbMatch[2]),
      b: Number(rgbMatch[3])
    }
  }

  const srgbMatch = color.match(/color\(srgb\s+([\d.]+)\s+([\d.]+)\s+([\d.]+)/)
  if (srgbMatch) {
    return {
      r: Number(srgbMatch[1]) * 255,
      g: Number(srgbMatch[2]) * 255,
      b: Number(srgbMatch[3]) * 255
    }
  }

  {
    throw new Error(`Unsupported color format: ${color}`)
  }
}

const brightnessOf = (color: string) => {
  const { r, g, b } = parseRgb(color)
  return (r * 299 + g * 587 + b * 114) / 1000
}

const backgroundOf = (locator: Locator) =>
  locator.evaluate((element) => window.getComputedStyle(element).backgroundColor)

const expectDarkSurface = async (locator: Locator) => {
  await expect(locator).toBeVisible()
  expect(brightnessOf(await backgroundOf(locator))).toBeLessThan(90)
}

const expectLightSurface = async (locator: Locator) => {
  await expect(locator).toBeVisible()
  expect(brightnessOf(await backgroundOf(locator))).toBeGreaterThan(210)
}

const openPublicRoute = async (page: Page, route: string, theme: ThemeMode = 'light') => {
  await page.addInitScript((mode) => {
    window.localStorage.removeItem('token')
    window.localStorage.removeItem('user')
    window.localStorage.removeItem('iot_verify_token')
    window.localStorage.removeItem('iot_verify_user')
    window.localStorage.setItem('iot_verify_theme', mode)
  }, theme)

  await page.goto(route)
  await expect(page.locator('.public-header')).toBeVisible({ timeout: 60_000 })
}

const expectAuthHeaderActionsOnRight = async (page: Page) => {
  const actions = page.locator('.public-header__actions')
  await expect(actions).toBeVisible()

  const viewport = page.viewportSize()
  const box = await actions.boundingBox()
  expect(viewport).not.toBeNull()
  expect(box).not.toBeNull()

  if (!viewport || !box) return
  expect(box.x).toBeGreaterThan(viewport.width * 0.62)
  expect(viewport.width - (box.x + box.width)).toBeLessThan(96)
}

const openWorkspace = async (page: Page, auth: AuthUser) => {
  await page.addInitScript(({ token, user }) => {
    window.localStorage.setItem('iot_verify_token', token)
    window.localStorage.setItem('iot_verify_user', JSON.stringify(user))
    window.localStorage.setItem('iot_verify_theme', 'dark')
  }, {
    token: auth.token,
    user: {
      userId: auth.userId,
      phone: auth.phone,
      username: auth.username
    }
  })

  await page.goto('/#/board')
  await expect(page.locator('.iot-board')).toBeVisible()
}

test.describe('public theme and layout', () => {
  test('register validation blocks invalid input before any network request', async ({ page }) => {
    await openPublicRoute(page, '/#/?mode=register', 'light')

    let registerCalls = 0
    await page.route('**/api/auth/register', async (route) => {
      registerCalls += 1
      await route.abort()
    })

    await page.locator('.auth-submit').click()

    await expect(page.locator('.auth-form small')).toHaveCount(4)
    expect(registerCalls).toBe(0)
  })

  test('user can register and reach the workspace through the UI', async ({ page, request }) => {
    const credentials = createTestAccountCredentials({ usernamePrefix: 'ui' })
    const { phone, username, password } = credentials
    trackTestAccount(request, credentials)

    await openPublicRoute(page, '/#/?mode=register', 'light')
    const registerInputs = page.locator('.auth-form input')
    await registerInputs.nth(0).fill(phone)
    await registerInputs.nth(1).fill(username)
    await registerInputs.nth(2).fill(password)
    await registerInputs.nth(3).fill(password)
    await page.locator('.auth-submit').click()

    await expect(page.locator('.iot-board')).toBeVisible({ timeout: 15_000 })
    const token = await page.evaluate(() => window.localStorage.getItem('iot_verify_token'))
    expect(token).toBeTruthy()
  })

  test('landing keeps only the meaningful public controls', async ({ page }) => {
    await openPublicRoute(page, '/', 'dark')

    await expect(page.locator('.public-header')).toBeVisible()
    await expect(page.locator('.language-toggle')).toHaveCount(1)
    await expect(page.locator('.theme-toggle')).toHaveCount(0)
    await expect(page.locator('.global-chat-wrapper')).toHaveCount(0)
    await expect(page.locator('.hero-title')).toBeVisible()
    await expect(page.locator('.auth-panel')).toBeHidden()
  })

  test('landing login state opens the right floating auth card in light theme', async ({ page }) => {
    await openPublicRoute(page, '/#/?mode=login', 'light')

    await expectAuthHeaderActionsOnRight(page)
    await expect(page.locator('.hero-title')).toBeVisible()
    await expect(page.locator('.auth-panel')).toBeVisible()
    await expectDarkSurface(page.locator('.auth-panel'))
    await expect(page.locator('.global-chat-wrapper')).toHaveCount(0)
  })

  test('login dark theme keeps the integrated auth card readable', async ({ page }) => {
    await openPublicRoute(page, '/#/?mode=login', 'dark')

    await expect(page.locator('html')).toHaveAttribute('data-theme', 'dark')
    await expectAuthHeaderActionsOnRight(page)
    await expectDarkSurface(page.locator('.auth-panel'))
    await expect(page.locator('.auth-form input').first()).toBeVisible()
  })

  test('login mobile layout keeps header controls and form usable', async ({ page }) => {
    await page.setViewportSize({ width: 390, height: 844 })
    await openPublicRoute(page, '/#/?mode=login', 'dark')

    const actions = page.locator('.public-header__actions')
    const formPanel = page.locator('.auth-panel')
    await expect(actions).toBeVisible()
    await expect(formPanel).toBeVisible()
    await expect(page.locator('.public-header__button')).toBeHidden()

    const actionsBox = await actions.boundingBox()
    const formBox = await formPanel.boundingBox()
    expect(actionsBox).not.toBeNull()
    expect(formBox).not.toBeNull()

    if (!actionsBox || !formBox) return
    expect(actionsBox.x).toBeGreaterThan(190)
    expect(actionsBox.x + actionsBox.width).toBeLessThanOrEqual(376)
    expect(formBox.y).toBeGreaterThanOrEqual(210)
    expect(formBox.y + formBox.height).toBeLessThanOrEqual(844)
  })

  test('register dark theme uses the same auth layout system', async ({ page }) => {
    await openPublicRoute(page, '/#/?mode=register', 'dark')

    await expectAuthHeaderActionsOnRight(page)
    await expectDarkSurface(page.locator('.auth-panel'))
    await expect(page.locator('.auth-form input')).toHaveCount(4)
  })

  test('workspace dark theme keeps floating panel surfaces coherent', async ({ page, request }) => {
    const auth = await createAuthenticatedUser(request)
    await openWorkspace(page, auth)

    await expectDarkSurface(page.locator('.board-nav-bar'))
    await expectDarkSurface(page.locator('.modern-panel'))
    await expectDarkSurface(page.locator('.glass-panel'))
    await expectDarkSurface(page.locator('.modern-panel input:not(.hidden)').first())
    await expectDarkSurface(page.locator('.canvas-map'))
    await expectDarkSurface(page.locator('.canvas-map__viewport'))
    await page.locator('[data-testid="open-simulation-panel"]').click()

    const panel = page.locator('[data-testid="simulation-panel"]')
    await expectDarkSurface(panel)
    await expectDarkSurface(panel.locator(':scope > .p-3'))
    await expectDarkSurface(panel.locator(':scope > .p-3 > .bg-white').first())

    await page.locator('[data-testid="close-simulation-panel"]').click()
    await page.locator('[data-testid="open-history-panel"]').click()
    const historyPanel = page.locator('[data-testid="trace-history-panel"]')
    await expectDarkSurface(historyPanel)
    await expectDarkSurface(historyPanel.locator(':scope > div.p-3').nth(0))
    await expectDarkSurface(historyPanel.locator(':scope > div.p-3').nth(1))

    await page.keyboard.press('Escape')
    await page.locator('.ai-assistant-btn').click({ force: true })
    await expect(page.locator('.chat-panel')).toBeVisible({ timeout: 15_000 })
  })

  test('workspace keeps account actions reachable at mid width and low height', async ({ page, request }) => {
    const auth = await createAuthenticatedUser(request)
    await page.setViewportSize({ width: 720, height: 720 })
    await openWorkspace(page, auth)

    const logoutButton = page.locator('.nav-logout-btn')
    const sceneActions = page.locator('details.scene-actions-menu')
    await expect(logoutButton).toBeVisible()
    await expect(sceneActions).toBeVisible()
    await expect(page.getByTestId('scene-import')).toBeHidden()

    const logoutBox = await logoutButton.boundingBox()
    expect(logoutBox).not.toBeNull()
    expect(logoutBox!.x).toBeGreaterThanOrEqual(0)
    expect(logoutBox!.x + logoutBox!.width).toBeLessThanOrEqual(720)

    await logoutButton.click()
    await page.locator('.delete-account-link').click()
    const accountDialog = page.locator('.account-delete-dialog')
    await expect(accountDialog).toBeVisible()

    await page.setViewportSize({ width: 720, height: 360 })
    const dialogMetrics = await accountDialog.evaluate(element => {
      const rect = element.getBoundingClientRect()
      const style = getComputedStyle(element)
      return {
        top: rect.top,
        bottom: rect.bottom,
        viewportHeight: window.innerHeight,
        overflowY: style.overflowY,
        scrollHeight: element.scrollHeight,
        clientHeight: element.clientHeight
      }
    })
    expect(dialogMetrics.top).toBeGreaterThanOrEqual(0)
    expect(dialogMetrics.bottom).toBeLessThanOrEqual(dialogMetrics.viewportHeight)
    expect(dialogMetrics.overflowY).toBe('auto')
    expect(dialogMetrics.scrollHeight).toBeGreaterThan(dialogMetrics.clientHeight)

    const confirmButton = accountDialog.locator('button[type="submit"]')
    await confirmButton.scrollIntoViewIfNeeded()
    await expect(confirmButton).toBeVisible()
  })
})

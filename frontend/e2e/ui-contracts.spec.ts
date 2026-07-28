import { type Page } from '@playwright/test'
import { expect, test, type AuthUser } from './support/auth'

/**
 * Covers the routing, session, and accessibility contracts that unit tests can only
 * assert structurally: real hash-history navigation, real `localStorage` session state,
 * real focus movement, and real computed scroll state.
 */

const seedSession = async (page: Page, auth: AuthUser, extra: Record<string, string> = {}) => {
  await page.addInitScript(({ token, user, extraEntries }) => {
    window.localStorage.setItem('iot_verify_token', token)
    window.localStorage.setItem('iot_verify_user', JSON.stringify(user))
    window.localStorage.setItem('locale', 'en')
    for (const [key, value] of Object.entries(extraEntries)) {
      window.localStorage.setItem(key, value)
    }
  }, {
    token: auth.token,
    user: { userId: auth.userId, phone: auth.phone, username: auth.username },
    extraEntries: extra
  })
}

const openBoard = async (page: Page, auth: AuthUser) => {
  await seedSession(page, auth, { iot_verify_theme: 'light' })
  await page.goto('/#/board')
  await expect(page.locator('.iot-board')).toBeVisible({ timeout: 60_000 })
}

// Every test here is read-only with respect to account state, so they all share the
// worker-scoped account rather than each registering one (the backend caps registrations
// per hour, and per-test cleanup would delete an account the next test still needs).
const expiredToken = () => {
  const payload = Buffer.from(JSON.stringify({ exp: Math.floor(Date.now() / 1000) - 60 }))
    .toString('base64').replace(/=/g, '').replace(/\+/g, '-').replace(/\//g, '_')
  return `header.${payload}.signature`
}

test.describe('routing and session', () => {
  test('sends an anonymous deep link to login and returns to it after signing in', async ({ page, sharedReadOnlyAccount: auth }) => {

    await page.goto('/#/board')
    await expect(page).toHaveURL(/#\/\?mode=login&redirect=%2Fboard|#\/\?mode=login&redirect=\/board/)
    await expect(page.locator('#auth-tab-login')).toBeVisible()

    await page.fill('#login-panel input[autocomplete="username"]', auth.username)
    await page.fill('#login-panel input[type="password"]', 'Pass1234!!')
    await page.click('#login-panel button[type="submit"]')

    await expect(page.locator('.iot-board')).toBeVisible({ timeout: 60_000 })
    // The login surface must hand over a clean workspace URL: a lingering ?redirect=
    // used to re-key the route and remount the freshly mounted board.
    expect(new URL(page.url()).hash).toBe('#/board')
  })

  test('rewrites a no-hash deep link and titles each route', async ({ page, sharedReadOnlyAccount: auth }) => {
    await seedSession(page, auth)

    await page.goto('/board')
    await expect(page.locator('.iot-board')).toBeVisible({ timeout: 60_000 })
    expect(new URL(page.url()).hash).toBe('#/board')
    await expect(page).toHaveTitle('IoT-Verify')
  })

  test('routes an unknown path to a 404 page whose home link works', async ({ page }) => {
    await page.goto('/#/no-such-page')
    await expect(page).toHaveURL(/#\/404$/)
    await expect(page).toHaveTitle('IoT-Verify · 404')

    await page.click('.el-result a')
    await expect(page).toHaveURL(/#\/$/)
    await expect(page.locator('#landing-title')).toBeVisible()
  })

  test('refuses a private route when the stored token has already expired', async ({ page }) => {
    await page.addInitScript(token => {
      window.localStorage.setItem('iot_verify_token', token)
      window.localStorage.setItem('iot_verify_user', JSON.stringify({
        userId: 1, phone: '13800138000', username: 'expired'
      }))
      window.localStorage.setItem('locale', 'en')
    }, expiredToken())

    await page.goto('/#/board')
    await expect(page.locator('#auth-tab-login')).toBeVisible()
    await expect(page.locator('.iot-board')).toHaveCount(0)
    expect(await page.evaluate(() => window.localStorage.getItem('iot_verify_token'))).toBeNull()
  })

  test('exposes exactly one h1 on each route', async ({ page, sharedReadOnlyAccount: auth }) => {
    // Seed before the first navigation: addInitScript only affects later loads.
    await seedSession(page, auth, { iot_verify_theme: 'light' })

    await page.goto('/#/404')
    await expect(page.locator('.el-result')).toBeVisible()
    expect(await page.locator('h1').count()).toBe(0)

    await page.goto('/#/board')
    await expect(page.locator('.iot-board')).toBeVisible({ timeout: 60_000 })
    expect(await page.locator('h1').count()).toBe(1)
    await expect(page.locator('h1 .logo-left')).toBeVisible()
  })
})

test.describe('theme control', () => {
  test('cycles light, dark, and follow-system, persisting only explicit choices', async ({ page, sharedReadOnlyAccount: auth }) => {
    await openBoard(page, auth)

    const toggle = page.locator('.board-nav-bar .theme-toggle')
    const storedTheme = () => page.evaluate(() => window.localStorage.getItem('iot_verify_theme'))

    await expect(page.locator('html')).toHaveAttribute('data-theme', 'light')

    await toggle.click()
    await expect(page.locator('html')).toHaveAttribute('data-theme', 'dark')
    expect(await storedTheme()).toBe('dark')

    // Third state: following the OS clears the stored override entirely.
    await toggle.click()
    expect(await storedTheme()).toBeNull()
    await expect(toggle).toHaveAccessibleName(/follow system/i)

    await toggle.click()
    await expect(page.locator('html')).toHaveAttribute('data-theme', 'light')
    expect(await storedTheme()).toBe('light')
  })

  test('follows the OS preference on a first visit with no stored choice', async ({ page, sharedReadOnlyAccount: auth }) => {
    await page.emulateMedia({ colorScheme: 'dark' })
    await seedSession(page, auth)

    await page.goto('/#/board')
    await expect(page.locator('.iot-board')).toBeVisible({ timeout: 60_000 })
    await expect(page.locator('html')).toHaveAttribute('data-theme', 'dark')
    expect(await page.evaluate(() => window.localStorage.getItem('iot_verify_theme'))).toBeNull()
  })
})

test.describe('board accessibility contracts', () => {
  test('exposes run settings as named switches that report their state', async ({ page, sharedReadOnlyAccount: auth }) => {
    await openBoard(page, auth)

    await page.getByTestId('open-verification-panel').click()
    const panel = page.getByTestId('verification-panel')
    await expect(panel).toBeVisible()

    // Non-modal tool panel: it must not claim to be a dialog, because focus is not trapped.
    await expect(panel).toHaveAttribute('role', 'region')
    expect(await panel.getAttribute('aria-modal')).toBeNull()

    // The attack switch is disabled until the board models an attack effect, but it must
    // still expose its role, name, and state rather than being an anonymous <button>.
    const attack = page.getByTestId('verification-attack-toggle')
    await expect(attack).toHaveRole('switch')
    await expect(attack).toHaveAccessibleName(/compromised/i)
    await expect(attack).toHaveAttribute('aria-checked', 'false')
    await expect(attack).toBeDisabled()

    const privacy = page.getByTestId('verification-privacy-toggle')
    await expect(privacy).toHaveRole('switch')
    await expect(privacy).toHaveAccessibleName(/private-data/i)
    await expect(privacy).toHaveAttribute('aria-checked', 'false')

    await privacy.click()
    await expect(privacy).toHaveAttribute('aria-checked', 'true')
    await privacy.click()
    await expect(privacy).toHaveAttribute('aria-checked', 'false')
  })

  test('keeps focus escapable from a non-modal panel and closes it with Escape', async ({ page, sharedReadOnlyAccount: auth }) => {
    await openBoard(page, auth)

    await page.getByTestId('open-verification-panel').click()
    const panel = page.getByTestId('verification-panel')
    await expect(panel).toBeVisible()

    await page.keyboard.press('Escape')
    await expect(panel).toBeHidden()
    // Focus returns to the control that opened the panel.
    await expect(page.getByTestId('open-verification-panel')).toBeFocused()
  })

  test('drives both side panel tab strips from the keyboard', async ({ page, sharedReadOnlyAccount: auth }) => {
    await openBoard(page, auth)

    const controlTemplates = page.getByTestId('control-tab-templates')
    await controlTemplates.click()
    await expect(controlTemplates).toHaveAttribute('aria-selected', 'true')

    await controlTemplates.press('ArrowRight')
    const controlDevices = page.getByTestId('control-tab-devices')
    await expect(controlDevices).toHaveAttribute('aria-selected', 'true')
    await expect(controlDevices).toBeFocused()
    await expect(page.getByTestId('control-section-devices')).toHaveAttribute('role', 'tabpanel')

    await controlDevices.press('End')
    await expect(page.getByTestId('control-tab-specs')).toHaveAttribute('aria-selected', 'true')

    const inspectorDevices = page.getByTestId('inspector-tab-devices')
    await inspectorDevices.click()
    await inspectorDevices.press('ArrowRight')
    const inspectorRules = page.getByTestId('inspector-tab-rules')
    await expect(inspectorRules).toHaveAttribute('aria-selected', 'true')
    await expect(inspectorRules).toBeFocused()
  })

  test('locks background scroll while a real modal is open', async ({ page, sharedReadOnlyAccount: auth }) => {
    await openBoard(page, auth)

    const bodyOverflow = () => page.evaluate(() => document.body.style.overflow)
    expect(await bodyOverflow()).not.toBe('hidden')

    await page.getByTestId('control-tab-rules').click()
    await expect(page.getByTestId('control-section-rules')).toBeVisible()
    await page.getByTestId('open-rule-builder').click()
    const dialog = page.locator('[role="dialog"][aria-modal="true"]')
    await expect(dialog.first()).toBeVisible()
    expect(await bodyOverflow()).toBe('hidden')

    await page.keyboard.press('Escape')
    await expect(dialog).toHaveCount(0)
    expect(await bodyOverflow()).not.toBe('hidden')
  })

  test('gives every board control an accessible name', async ({ page, sharedReadOnlyAccount: auth }) => {
    await openBoard(page, auth)

    const unnamed = await page.evaluate(() => {
      const describes = (element: Element) => {
        const id = element.getAttribute('aria-labelledby')
        return id ? id.split(/\s+/).some(part => document.getElementById(part)?.textContent?.trim()) : false
      }
      return [...document.querySelectorAll('button:not([disabled])')]
        .filter(button => {
          const style = getComputedStyle(button)
          if (style.display === 'none' || style.visibility === 'hidden') return false
          if (!button.getClientRects().length) return false
          const text = (button.textContent || '').replace(/\s+/g, ' ').trim()
          const iconOnly = [...button.querySelectorAll('.material-symbols-outlined, .material-icons-round')]
            .map(icon => (icon.textContent || '').trim())
          const visibleText = iconOnly.reduce((acc, icon) => acc.replace(icon, ''), text).trim()
          return !visibleText
            && !button.getAttribute('aria-label')?.trim()
            && !button.getAttribute('title')?.trim()
            && !describes(button)
        })
        .map(button => button.outerHTML.slice(0, 120))
    })

    expect(unnamed, `Unnamed buttons:\n${unnamed.join('\n')}`).toEqual([])
  })
})

test.describe('responsive boundaries', () => {
  /**
   * Complementary media queries must split at the same value. When they were written as
   * `max-width: 1023px` / `min-width: 1024px`, a fractional viewport width — normal on a
   * scaled display — matched neither rule, so the nav showed both layouts' gaps.
   */
  for (const width of [1023, 1024]) {
    test(`shows exactly one nav layout at ${width}px`, async ({ page, sharedReadOnlyAccount: auth }) => {
      await page.setViewportSize({ width, height: 800 })
      await openBoard(page, auth)

      const inlineActions = page.locator('.board-nav-bar .scene-action-btn').first()
      const overflowMenu = page.locator('.board-nav-bar .scene-actions-menu')

      if (width >= 1024) {
        await expect(inlineActions).toBeVisible()
        await expect(overflowMenu).toBeHidden()
      } else {
        await expect(inlineActions).toBeHidden()
        await expect(overflowMenu).toBeVisible()
      }
      // Either way the scene commands stay reachable, never hidden by both rules at once.
      await expect(page.getByTestId('scene-export').or(overflowMenu)).not.toHaveCount(0)
    })
  }

  test('keeps the device dialog padding and sm: utilities mutually exclusive at 640px', async ({ page, sharedReadOnlyAccount: auth }) => {
    await page.setViewportSize({ width: 640, height: 900 })
    await openBoard(page, auth)

    // At exactly 640px Tailwind's `sm:` is active, so the compact overlay padding must not be.
    const padding = await page.evaluate(() => {
      const probe = document.createElement('div')
      probe.className = 'device-dialog-overlay'
      document.body.append(probe)
      const value = getComputedStyle(probe).padding
      probe.remove()
      return value
    })
    expect(padding).not.toBe('12px')
  })
})

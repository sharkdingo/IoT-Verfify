import { type Page } from '@playwright/test'
import { createAuthenticatedUser, expect, test, type AuthUser } from './support/auth'

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
  await expect(page.getByTestId('board-root')).toBeVisible({ timeout: 30_000 })
  await expect(page.getByTestId('scene-import')).toBeEnabled({ timeout: 30_000 })
}

test('a rejected recommendation stop converges when status becomes terminal', async ({ page, request }) => {
  const auth = await createAuthenticatedUser(request, { usernamePrefix: 'recommendstop' })
  let releaseRecommendation!: () => void
  const recommendationRelease = new Promise<void>(resolve => { releaseRecommendation = resolve })
  let markRecommendationStarted!: () => void
  const recommendationStarted = new Promise<void>(resolve => { markRecommendationStarted = resolve })
  let cancelRequested = false
  let postCancelStatusReads = 0

  await page.route('**/api/board/rules/recommend', async route => {
    markRecommendationStarted()
    await recommendationRelease
    await route.fulfill({
      status: 503,
      contentType: 'application/json',
      body: JSON.stringify({ code: 503, message: 'released test request', data: null })
    }).catch(() => undefined)
  })
  await page.route('**/api/board/recommendations/**', async route => {
    const method = route.request().method()
    const requestId = decodeURIComponent(new URL(route.request().url()).pathname.split('/').pop() || '')
    if (method === 'DELETE') {
      cancelRequested = true
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ code: 200, message: 'success', data: false })
      })
      return
    }
    if (method === 'GET') {
      if (cancelRequested) postCancelStatusReads += 1
      if (cancelRequested && postCancelStatusReads === 1) {
        await route.fulfill({
          status: 404,
          contentType: 'application/json',
          body: JSON.stringify({ code: 404, message: 'request registration not visible yet', data: null })
        })
        return
      }
      const finished = cancelRequested && postCancelStatusReads >= 3
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          code: 200,
          message: 'success',
          data: {
            requestId,
            state: finished ? 'FINISHED' : 'RUNNING',
            stage: finished ? 'CANCELLING' : 'REQUESTING_MODEL',
            elapsedMs: 1000
          }
        })
      })
      return
    }
    await route.fallback()
  })

  try {
    await openWorkspace(page, auth)
    await page.getByTestId('open-rule-recommendations').click()
    const action = page.getByTestId('generate-rule-recommendations')
    await action.click()
    await recommendationStarted
    await expect(action).toContainText('Stop', { timeout: 5_000 })

    await action.click()
    await expect.poll(() => cancelRequested).toBe(true)
    await expect(action).toContainText('Generate', { timeout: 10_000 })
    await expect.poll(() => postCancelStatusReads).toBeGreaterThanOrEqual(3)
  } finally {
    releaseRecommendation()
  }
})

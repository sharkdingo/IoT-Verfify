import { expect, type APIRequestContext, type Page, test } from '@playwright/test'

const apiBaseURL = process.env.E2E_API_BASE_URL || 'http://127.0.0.1:8080'

type AuthUser = {
  userId: number
  phone: string
  username: string
  token: string
}

const unwrap = async <T>(response: Awaited<ReturnType<APIRequestContext['get']>>): Promise<T> => {
  expect(response.ok(), await response.text()).toBeTruthy()
  const body = await response.json()
  expect(body.code, JSON.stringify(body)).toBe(200)
  return body.data as T
}

const createAuthenticatedUser = async (request: APIRequestContext): Promise<AuthUser> => {
  const suffix = String(Date.now() % 100_000_000).padStart(8, '0')
  const phone = `139${suffix}`
  const password = 'Pass1234'
  const username = `chat${Date.now().toString(36).slice(-10)}`

  const registerResponse = await request.post(`${apiBaseURL}/api/auth/register`, {
    data: { phone, username, password }
  })
  expect(registerResponse.ok(), await registerResponse.text()).toBeTruthy()

  return unwrap<AuthUser>(await request.post(`${apiBaseURL}/api/auth/login`, {
    data: { identifier: username, password }
  }))
}

const openWorkspace = async (page: Page, auth: AuthUser) => {
  await page.addInitScript(({ token, user }) => {
    window.localStorage.setItem('iot_verify_token', token)
    window.localStorage.setItem('iot_verify_user', JSON.stringify(user))
    window.localStorage.setItem('iot_verify_theme', 'light')
    window.localStorage.setItem('locale', 'zh-CN')
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

  await page.route('**/api/chat/completions', async route => {
    await responseGate
    await route.fulfill({
      status: 200,
      contentType: 'text/event-stream; charset=UTF-8',
      body: 'data: {"content":"已完成检查。"}\n\n'
    })
  })
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
})

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
  await executionDetails.locator('summary').click()
  await expect(page.getByTestId('chat-execution-trace')).toBeVisible()
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
  await executionDetails.locator('summary').click()
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

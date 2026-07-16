import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

const authMocks = vi.hoisted(() => ({
  logout: vi.fn(),
  getToken: vi.fn(() => null as string | null)
}))

const routerMocks = vi.hoisted(() => ({
  push: vi.fn(),
  currentRoute: { value: { path: '/board', fullPath: '/board' } }
}))

vi.mock('@/stores/auth', () => ({
  useAuth: () => ({
    getToken: authMocks.getToken,
    logout: authMocks.logout
  })
}))

vi.mock('@/router', () => ({ router: routerMocks }))

vi.mock('@/api/http', () => ({
  default: {
    get: vi.fn()
  }
}))

import http from '@/api/http'
import { getSessionActivity, getSessionHistory, sendStreamChat } from './chat'

describe('chat stream lifecycle semantics', () => {
  beforeEach(() => {
    vi.clearAllMocks()
    authMocks.getToken.mockReturnValue(null)
    routerMocks.currentRoute.value = { path: '/board', fullPath: '/board' }
    routerMocks.push.mockResolvedValue(undefined)
  })

  afterEach(() => {
    vi.unstubAllGlobals()
  })

  it('does not report a user-aborted stream as normally finished', async () => {
    const abortError = Object.assign(new Error('aborted'), { name: 'AbortError' })
    vi.stubGlobal('fetch', vi.fn().mockRejectedValue(abortError))
    const onFinish = vi.fn()
    const onError = vi.fn()

    await sendStreamChat(
      'session-1',
      'hello',
      { onMessage: vi.fn(), onError, onFinish },
      new AbortController()
    )

    expect(onFinish).not.toHaveBeenCalled()
    expect(onError).not.toHaveBeenCalled()
  })

  it('binds a conversation-history load to its caller abort signal', async () => {
    vi.mocked(http.get).mockResolvedValue({ data: { data: [] } })
    const controller = new AbortController()

    await getSessionHistory('session-1', controller.signal)

    expect(http.get).toHaveBeenCalledWith(
      '/chat/sessions/session-1/messages',
      { signal: controller.signal }
    )
  })

  it('uses a short independent timeout and abort signal for activity checks', async () => {
    vi.mocked(http.get).mockResolvedValue({
      data: { data: { sessionId: 'session-1', active: false } }
    })
    const controller = new AbortController()

    await getSessionActivity('session-1', { timeoutMs: 1500, signal: controller.signal })

    expect(http.get).toHaveBeenCalledWith(
      '/chat/sessions/session-1/activity',
      { timeout: 1500, signal: controller.signal }
    )
  })

  it('redirects an expired SSE session through the same login route as axios', async () => {
    vi.stubGlobal('fetch', vi.fn().mockResolvedValue({
      ok: false,
      status: 401,
      statusText: 'Unauthorized',
      text: vi.fn().mockResolvedValue('{"message":"Authentication required"}')
    }))

    await expect(sendStreamChat(
      'session-1',
      'hello',
      { onMessage: vi.fn() }
    )).rejects.toMatchObject({ status: 401 })

    expect(authMocks.logout).toHaveBeenCalledOnce()
    expect(routerMocks.push).toHaveBeenCalledWith({
      path: '/',
      query: { mode: 'login', redirect: '/board' }
    })
  })

  it('reports SSE authorization failures without logging the user out', async () => {
    vi.stubGlobal('fetch', vi.fn().mockResolvedValue({
      ok: false,
      status: 403,
      statusText: 'Forbidden',
      text: vi.fn().mockResolvedValue('{"message":"Access denied"}')
    }))

    await expect(sendStreamChat(
      'session-1',
      'hello',
      { onMessage: vi.fn() }
    )).rejects.toMatchObject({ status: 403 })

    expect(authMocks.logout).not.toHaveBeenCalled()
    expect(routerMocks.push).not.toHaveBeenCalled()
  })

  it('classifies a missing response body without exposing its English parser message as UI text', async () => {
    vi.stubGlobal('fetch', vi.fn().mockResolvedValue({ ok: true, body: null }))
    const onError = vi.fn()

    await expect(sendStreamChat(
      'session-1',
      'hello',
      { onMessage: vi.fn(), onError }
    )).rejects.toMatchObject({ kind: 'MISSING_BODY' })

    expect(onError).toHaveBeenCalledWith(expect.objectContaining({ kind: 'MISSING_BODY' }))
  })

  it('classifies a completed stream with no frames', async () => {
    const reader = { read: vi.fn().mockResolvedValue({ done: true, value: undefined }) }
    vi.stubGlobal('fetch', vi.fn().mockResolvedValue({
      ok: true,
      body: { getReader: () => reader }
    }))

    await expect(sendStreamChat(
      'session-1',
      'hello',
      { onMessage: vi.fn() }
    )).rejects.toMatchObject({ kind: 'EMPTY_STREAM' })
  })
})

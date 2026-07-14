import { afterEach, describe, expect, it, vi } from 'vitest'

vi.mock('@/stores/auth', () => ({
  useAuth: () => ({
    getToken: () => null,
    logout: vi.fn()
  })
}))

vi.mock('@/api/http', () => ({
  default: {
    get: vi.fn()
  }
}))

import http from '@/api/http'
import { getSessionHistory, sendStreamChat } from './chat'

describe('chat stream lifecycle semantics', () => {
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

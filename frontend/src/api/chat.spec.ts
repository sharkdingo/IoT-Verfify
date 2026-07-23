import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

const authMocks = vi.hoisted(() => ({
  logoutIfTokenMatches: vi.fn(() => true),
  getToken: vi.fn(() => null as string | null)
}))

const routerMocks = vi.hoisted(() => ({
  push: vi.fn(),
  currentRoute: { value: { path: '/board', fullPath: '/board' } }
}))

vi.mock('@/stores/auth', () => ({
  useAuth: () => ({
    getToken: authMocks.getToken,
    logoutIfTokenMatches: authMocks.logoutIfTokenMatches
  })
}))

vi.mock('@/router', () => ({ router: routerMocks }))

vi.mock('@/api/http', () => ({
  default: {
    get: vi.fn(),
    post: vi.fn()
  }
}))

import http from '@/api/http'
import {
  getPendingConfirmation,
  getSessionActivity,
  getSessionHistory,
  requestSessionStop,
  sendStreamChat
} from './chat'

const successfulStreamResponse = (payload: string) => {
  const reader = {
    read: vi.fn()
      .mockResolvedValueOnce({ done: false, value: new TextEncoder().encode(payload) })
      .mockResolvedValue({ done: true, value: undefined })
  }
  return { ok: true, body: { getReader: () => reader } }
}

describe('chat stream lifecycle semantics', () => {
  beforeEach(() => {
    vi.clearAllMocks()
    authMocks.getToken.mockReturnValue(null)
    authMocks.logoutIfTokenMatches.mockReturnValue(true)
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
    vi.mocked(http.get).mockResolvedValue({
      data: { data: { messages: [], nextBeforeId: null, hasMore: false } }
    })
    const controller = new AbortController()

    await getSessionHistory('session-1', controller.signal)

    expect(http.get).toHaveBeenCalledWith(
      '/chat/sessions/session-1/messages',
      { signal: controller.signal }
    )
  })

  it('rejects an unknown persisted execution status at the history boundary', async () => {
    vi.mocked(http.get).mockResolvedValue({
      data: {
        data: {
          messages: [{
            sessionId: 'session-1',
            role: 'assistant',
            content: 'A future server response.',
            turnId: 'turn-1',
            executionStatus: 'FUTURE_STATUS'
          }],
          nextBeforeId: null,
          hasMore: false
        }
      }
    })

    await expect(getSessionHistory('session-1')).rejects.toThrow(
      'Chat history message 0 has an unknown execution status'
    )
  })

  it('rejects completed history without persisted usable tool evidence', async () => {
    vi.mocked(http.get).mockResolvedValue({
      data: {
        data: {
          messages: [{
            sessionId: 'session-1',
            role: 'assistant',
            content: 'Unproven completion.',
            turnId: 'turn-1',
            executionStatus: 'COMPLETED'
          }],
          nextBeforeId: null,
          hasMore: false
        }
      }
    })

    await expect(getSessionHistory('session-1')).rejects.toThrow(
      'Chat history message 0 has unproven completed status'
    )
  })

  it('rejects malformed persisted message content and execution traces', async () => {
    vi.mocked(http.get).mockResolvedValueOnce({
      data: {
        data: {
          messages: [{
            sessionId: 'session-1',
            role: 'assistant',
            content: { text: 'not a string' }
          }],
          nextBeforeId: null,
          hasMore: false
        }
      }
    })

    await expect(getSessionHistory('session-1')).rejects.toThrow(
      'Chat history message 0 is incomplete'
    )

    vi.mocked(http.get).mockResolvedValueOnce({
      data: {
        data: {
          messages: [{
            sessionId: 'session-1',
            role: 'assistant',
            content: 'Saved response',
            executionTrace: [{ stage: 'FUTURE_STAGE' }]
          }],
          nextBeforeId: null,
          hasMore: false
        }
      }
    })

    await expect(getSessionHistory('session-1')).rejects.toThrow(
      'Chat history message 0 is incomplete'
    )
  })

  it('rejects a history page containing a message from another session', async () => {
    vi.mocked(http.get).mockResolvedValue({
      data: {
        data: {
          messages: [{
            sessionId: 'session-2',
            role: 'assistant',
            content: 'Do not render this in session 1.'
          }],
          nextBeforeId: null,
          hasMore: false
        }
      }
    })

    await expect(getSessionHistory('session-1')).rejects.toThrow(
      'Chat history message 0 is incomplete'
    )
  })

  it('rejects an unusable history cursor instead of paginating with corrupted state', async () => {
    vi.mocked(http.get).mockResolvedValue({
      data: {
        data: {
          messages: [{ sessionId: 'session-1', role: 'assistant', content: 'Saved response' }],
          nextBeforeId: null,
          hasMore: true
        }
      }
    })

    await expect(getSessionHistory('session-1')).rejects.toThrow(
      'Chat history response is incomplete'
    )
  })

  it('rejects obsolete array history and internal tool messages', async () => {
    vi.mocked(http.get).mockResolvedValueOnce({ data: { data: [] } })
    await expect(getSessionHistory('session-1')).rejects.toThrow(
      'Chat history response is incomplete'
    )

    vi.mocked(http.get).mockResolvedValueOnce({
      data: {
        data: {
          messages: [{ sessionId: 'session-1', role: 'tool', content: '{"secret":true}' }],
          nextBeforeId: null,
          hasMore: false
        }
      }
    })
    await expect(getSessionHistory('session-1')).rejects.toThrow(
      'Chat history message 0 is incomplete'
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

  it('loads server-authoritative pending protected-action kinds', async () => {
    vi.mocked(http.get).mockResolvedValue({
      data: { data: { sessionId: 'session-1', kinds: ['DESTRUCTIVE'] } }
    })
    const controller = new AbortController()

    await expect(getPendingConfirmation('session-1', controller.signal)).resolves.toEqual({
      sessionId: 'session-1',
      kinds: ['DESTRUCTIVE']
    })
    expect(http.get).toHaveBeenCalledWith(
      '/chat/sessions/session-1/confirmation',
      { signal: controller.signal }
    )
  })

  it('sends an explicit idempotent stop request for the active session', async () => {
    vi.mocked(http.post).mockResolvedValue({ data: { data: null } })

    await requestSessionStop('session-1')

    expect(http.post).toHaveBeenCalledWith(
      '/chat/sessions/session-1/stop',
      null,
      { timeout: 2500 }
    )
  })

  it('includes the client turn id in the streaming request body', async () => {
    const fetchMock = vi.fn().mockResolvedValue({
      ok: true,
      body: null
    })
    vi.stubGlobal('fetch', fetchMock)

    await expect(sendStreamChat(
      'session-1',
      'hello',
      { onMessage: vi.fn() },
      undefined,
      'turn-1'
    )).rejects.toMatchObject({ kind: 'MISSING_BODY' })

    expect(JSON.parse(fetchMock.mock.calls[0][1].body)).toEqual({
      sessionId: 'session-1',
      content: 'hello',
      turnId: 'turn-1'
    })
  })

  it('sends protected authority only through the structured confirmation field', async () => {
    const fetchMock = vi.fn().mockResolvedValue({ ok: true, body: null })
    vi.stubGlobal('fetch', fetchMock)

    await expect(sendStreamChat(
      'session-1',
      'I confirmed with the button',
      { onMessage: vi.fn() },
      undefined,
      'turn-2',
      { action: 'CONFIRM', kind: 'DESTRUCTIVE' }
    )).rejects.toMatchObject({ kind: 'MISSING_BODY' })

    expect(JSON.parse(fetchMock.mock.calls[0][1].body)).toEqual({
      sessionId: 'session-1',
      content: 'I confirmed with the button',
      turnId: 'turn-2',
      confirmation: { action: 'CONFIRM', kind: 'DESTRUCTIVE' }
    })
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

    expect(authMocks.logoutIfTokenMatches).toHaveBeenCalledWith(null)
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

    expect(authMocks.logoutIfTokenMatches).not.toHaveBeenCalled()
    expect(routerMocks.push).not.toHaveBeenCalled()
  })

  it('does not let a delayed Alice SSE 401 redirect Bob to login', async () => {
    authMocks.getToken.mockReturnValue('alice-token')
    authMocks.logoutIfTokenMatches.mockReturnValue(false)
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

    expect(authMocks.logoutIfTokenMatches).toHaveBeenCalledWith('alice-token')
    expect(routerMocks.push).not.toHaveBeenCalled()
  })

  it('preserves a structured chat-history quota reason from an HTTP error', async () => {
    vi.stubGlobal('fetch', vi.fn().mockResolvedValue({
      ok: false,
      status: 429,
      statusText: 'Too Many Requests',
      text: vi.fn().mockResolvedValue(JSON.stringify({
        message: 'Conversation limit reached',
        data: { reasonCode: 'CHAT_HISTORY_LIMIT_REACHED' }
      }))
    }))

    await expect(sendStreamChat(
      'session-1',
      'hello',
      { onMessage: vi.fn() }
    )).rejects.toMatchObject({
      kind: 'HTTP_ERROR',
      status: 429,
      reasonCode: 'CHAT_HISTORY_LIMIT_REACHED'
    })
  })

  it('classifies a missing response body without exposing its English parser message as UI text', async () => {
    vi.stubGlobal('fetch', vi.fn().mockResolvedValue({ ok: true, body: null }))
    const onError = vi.fn()
    const onAccepted = vi.fn()

    await expect(sendStreamChat(
      'session-1',
      'hello',
      { onMessage: vi.fn(), onError, onAccepted }
    )).rejects.toMatchObject({ kind: 'MISSING_BODY' })

    expect(onAccepted).toHaveBeenCalledOnce()
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

  it('rejects malformed structured progress before it reaches the UI', async () => {
    vi.stubGlobal('fetch', vi.fn().mockResolvedValue(successfulStreamResponse(
      'data: {"progress":{"stage":"FUTURE_STAGE"}}\n\n'
    )))
    const onProgress = vi.fn()
    const onError = vi.fn()

    await expect(sendStreamChat(
      'session-1',
      'hello',
      { onMessage: vi.fn(), onProgress, onError }
    )).rejects.toMatchObject({ kind: 'INVALID_FRAME' })

    expect(onProgress).not.toHaveBeenCalled()
    expect(onError).toHaveBeenCalledWith(expect.objectContaining({ kind: 'INVALID_FRAME' }))
  })

  it('requires an outcome that matches each progress stage', async () => {
    const invalidPayloads = [
      { progress: { stage: 'TOOL_RESULT' } },
      { progress: { stage: 'TOOL_RESULT', outcome: 'EMERGENCY_LIMIT' } },
      { progress: { stage: 'EXECUTION_GUARD', outcome: 'USABLE' } },
      { progress: { stage: 'PLANNING', outcome: 'USABLE' } }
    ]

    for (const payload of invalidPayloads) {
      vi.stubGlobal('fetch', vi.fn().mockResolvedValue(successfulStreamResponse(
        `data: ${JSON.stringify(payload)}\n\n`
      )))
      await expect(sendStreamChat(
        'session-1',
        'hello',
        { onMessage: vi.fn(), onProgress: vi.fn() }
      )).rejects.toMatchObject({ kind: 'INVALID_FRAME' })
    }
  })

  it('rejects empty, non-object, and non-JSON stream frames without completing', async () => {
    const invalidPayloads = ['{}', '{"content":42}', '[]', 'plain assistant text']

    for (const payload of invalidPayloads) {
      vi.stubGlobal('fetch', vi.fn().mockResolvedValue(successfulStreamResponse(
        `data: ${payload}\n\n`
      )))
      const onFinish = vi.fn()
      await expect(sendStreamChat(
        'session-1',
        'hello',
        { onMessage: vi.fn(), onFinish }
      )).rejects.toMatchObject({ kind: 'INVALID_FRAME' })
      expect(onFinish).not.toHaveBeenCalled()
    }
  })

  it('validates the complete structured frame before invoking any callback', async () => {
    vi.stubGlobal('fetch', vi.fn().mockResolvedValue(successfulStreamResponse(
      'data: {"command":{"type":"REFRESH_DATA"},"progress":{"stage":"TOOL_RESULT"}}\n\n'
    )))
    const onCommand = vi.fn()

    await expect(sendStreamChat(
      'session-1',
      'hello',
      { onMessage: vi.fn(), onCommand }
    )).rejects.toMatchObject({ kind: 'INVALID_FRAME' })
    expect(onCommand).not.toHaveBeenCalled()
  })

  it('accepts only documented refresh commands and targets', async () => {
    for (const command of [
      { type: 'NAVIGATE', payload: { target: 'board_state' } },
      { type: 'REFRESH_DATA', payload: { target: 'future_target' } },
      { type: 'REFRESH_DATA', payload: { target: 'board_state', extra: true } }
    ]) {
      vi.stubGlobal('fetch', vi.fn().mockResolvedValue(successfulStreamResponse(
        `data: ${JSON.stringify({ command })}\n\n`
      )))
      await expect(sendStreamChat(
        'session-1',
        'hello',
        { onMessage: vi.fn(), onCommand: vi.fn() }
      )).rejects.toMatchObject({ kind: 'INVALID_FRAME' })
    }

    vi.stubGlobal('fetch', vi.fn().mockResolvedValue(successfulStreamResponse(
      'data: {"command":{"type":"REFRESH_DATA","payload":{"target":"board_state"}}}\n\n'
    )))
    const onCommand = vi.fn()
    await sendStreamChat('session-1', 'hello', { onMessage: vi.fn(), onCommand })
    expect(onCommand).toHaveBeenCalledWith({
      type: 'REFRESH_DATA',
      payload: { target: 'board_state' }
    })
  })

  it('accepts a complete structured progress frame', async () => {
    vi.stubGlobal('fetch', vi.fn().mockResolvedValue(successfulStreamResponse(
      'data: {"progress":{"stage":"TOOL_RESULT","toolName":"get_board","round":1,"outcome":"USABLE","successfulSteps":1,"failedSteps":0,"unconfirmedSteps":0}}\n\n'
    )))
    const onProgress = vi.fn()
    const onFinish = vi.fn()

    await sendStreamChat(
      'session-1',
      'hello',
      { onMessage: vi.fn(), onProgress, onFinish }
    )

    expect(onProgress).toHaveBeenCalledWith(expect.objectContaining({
      stage: 'TOOL_RESULT',
      outcome: 'USABLE',
      successfulSteps: 1
    }))
    expect(onFinish).toHaveBeenCalledOnce()
  })

  it('accepts the documented partial tool-result outcome', async () => {
    vi.stubGlobal('fetch', vi.fn().mockResolvedValue(successfulStreamResponse(
      'data: {"progress":{"stage":"TOOL_RESULT","outcome":"PARTIAL","successfulSteps":1,"failedSteps":0,"unconfirmedSteps":0}}\n\n'
    )))
    const onProgress = vi.fn()

    await sendStreamChat('session-1', 'hello', { onMessage: vi.fn(), onProgress })

    expect(onProgress).toHaveBeenCalledWith(expect.objectContaining({ outcome: 'PARTIAL' }))
  })

  it('reports transport acceptance before parsing a successful stream', async () => {
    const reader = { read: vi.fn().mockResolvedValue({ done: true, value: undefined }) }
    vi.stubGlobal('fetch', vi.fn().mockResolvedValue({
      ok: true,
      body: { getReader: () => reader }
    }))
    const onAccepted = vi.fn()

    await expect(sendStreamChat(
      'session-1',
      'hello',
      { onMessage: vi.fn(), onAccepted }
    )).rejects.toMatchObject({ kind: 'EMPTY_STREAM' })

    expect(onAccepted).toHaveBeenCalledOnce()
  })
})

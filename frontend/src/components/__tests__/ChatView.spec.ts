// @vitest-environment jsdom
import { flushPromises, mount } from '@vue/test-utils'
import { ElMessage } from 'element-plus'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

import { i18n } from '@/assets/i18n'
import { useChatStore } from '@/stores/chat'
import { useAuth } from '@/stores/auth'
import type { ChatHistoryPage, ChatMessage } from '@/types/chat'

const chatApi = vi.hoisted(() => ({
  createSession: vi.fn(),
  deleteSession: vi.fn(),
  getSessionActivity: vi.fn(),
  getSessionHistory: vi.fn(),
  getSessionList: vi.fn(),
  getPendingConfirmation: vi.fn(),
  requestSessionStop: vi.fn(),
  sendStreamChat: vi.fn()
}))

vi.mock('element-plus/es/components/message/style/css', () => ({}))
vi.mock('element-plus/es/components/message-box/style/css', () => ({}))

vi.mock('@/api/chat', async importOriginal => {
  const actual = await importOriginal<typeof import('@/api/chat')>()
  return {
    ChatStreamError: class ChatStreamError extends Error {
      readonly serverFrame: boolean
      readonly kind: string
      readonly status?: number
      readonly reasonCode?: string

      constructor(message: string, options: Record<string, any> = {}) {
        super(message)
        this.serverFrame = options.serverFrame ?? false
        this.kind = options.kind ?? 'UNKNOWN'
        this.status = options.status
        this.reasonCode = options.reasonCode
      }
    },
    hasCompletedToolEvidence: actual.hasCompletedToolEvidence,
    ...chatApi
  }
})

import { ChatStreamError } from '@/api/chat'
import ChatView from '../ChatView.vue'

const chatStore = useChatStore()
const authStore = useAuth()
const validToken = (signature: string) => {
  const payload = btoa(JSON.stringify({ exp: Math.floor(Date.now() / 1000) + 3600 }))
    .replace(/=/g, '').replace(/\+/g, '-').replace(/\//g, '_')
  return `header.${payload}.${signature}`
}
const session = {
  id: 'session-1',
  userId: 1,
  title: '玄关场景检查',
  updatedAt: '2026-07-13T12:00:00Z',
  active: false
}

const historyPage = (
    messages: ChatMessage[] = [],
    sessionId = session.id
): ChatHistoryPage => ({
  messages: messages.map((message, index) => ({
    ...message,
    id: message.id ?? index + 1,
    sessionId,
    turnId: message.turnId ?? `fixture-turn-${Math.floor(index / 2) + 1}`,
    createdAt: message.createdAt ?? '2026-07-13T12:00:00Z'
  })),
  nextBeforeId: null,
  hasMore: false
})

const notFoundError = () => Object.assign(new Error('session not found'), {
  response: { status: 404 }
})

const acceptAndFinishStream = (
    args: any[],
    executionStatus: 'COMPLETED' | 'PARTIAL' = 'PARTIAL'
) => {
  const callbacks = args[2]
  callbacks.onAccepted?.()
  callbacks.onFinish?.({ turnId: args[4], executionStatus })
}

const mountChat = (props: Record<string, unknown> = {}) => mount(ChatView, {
  props: { boardMode: true, ...props },
  global: {
    plugins: [i18n],
    stubs: {
      ChatMarkdown: { props: ['source'], template: '<div class="chat-markdown-stub">{{ source }}</div>' }
    }
  }
})

describe('ChatView', () => {
  beforeEach(() => {
    vi.clearAllMocks()
    authStore.logout()
    chatStore.closeChat()
    chatStore.setStreaming(false)
    i18n.global.locale.value = 'zh-CN'
    chatApi.getSessionList.mockResolvedValue([])
    chatApi.getSessionActivity.mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.getSessionHistory.mockResolvedValue(historyPage())
    chatApi.getPendingConfirmation.mockResolvedValue({ sessionId: 'session-1', kinds: [] })
    chatApi.deleteSession.mockResolvedValue(undefined)
    chatApi.requestSessionStop.mockResolvedValue(undefined)
  })

  afterEach(() => {
    authStore.logout()
    chatStore.closeChat()
    chatStore.setStreaming(false)
  })

  it('loads existing sessions when mounted after the assistant is already open', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()

    expect(chatApi.getSessionList).toHaveBeenCalledTimes(1)
    expect(wrapper.get('[data-testid="chat-session-session-1"]').text()).toContain('玄关场景检查')

    wrapper.unmount()
  })

  it('clears Alice messages and loads Bob sessions when the auth subject changes', async () => {
    const bobSession = {
      ...session,
      id: 'session-2',
      userId: 2,
      title: 'Bob 的会话'
    }
    chatApi.getSessionList
      .mockResolvedValueOnce([session])
      .mockResolvedValueOnce([bobSession])
    chatApi.getSessionHistory.mockResolvedValue(historyPage([
      { role: 'assistant', content: 'Alice 的私密消息' }
    ]))
    authStore.login(validToken('alice'), {
      userId: 1,
      phone: '13800138000',
      username: 'alice'
    })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    expect(wrapper.text()).toContain('Alice 的私密消息')

    authStore.login(validToken('bob'), {
      userId: 2,
      phone: '13900139000',
      username: 'bob'
    })
    await flushPromises()

    expect(wrapper.text()).not.toContain('Alice 的私密消息')
    expect(wrapper.find('[data-testid="chat-session-session-1"]').exists()).toBe(false)
    expect(wrapper.get('[data-testid="chat-session-session-2"]').text()).toContain('Bob 的会话')
    wrapper.unmount()
  })

  it('ignores an Alice session-list response that arrives after switching to Bob', async () => {
    const bobSession = {
      ...session,
      id: 'session-2',
      userId: 2,
      title: 'Bob 的会话'
    }
    let resolveAliceSessions!: (sessions: Array<typeof session>) => void
    chatApi.getSessionList
      .mockReturnValueOnce(new Promise(resolve => { resolveAliceSessions = resolve }))
      .mockResolvedValueOnce([bobSession])
    authStore.login(validToken('alice'), {
      userId: 1,
      phone: '13800138000',
      username: 'alice'
    })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    authStore.login(validToken('bob'), {
      userId: 2,
      phone: '13900139000',
      username: 'bob'
    })
    await flushPromises()
    resolveAliceSessions([session])
    await flushPromises()

    expect(wrapper.find('[data-testid="chat-session-session-1"]').exists()).toBe(false)
    expect(wrapper.get('[data-testid="chat-session-session-2"]').text()).toContain('Bob 的会话')
    wrapper.unmount()
  })

  it('ignores a delayed Alice stop failure after switching to Bob', async () => {
    const bobSession = {
      ...session,
      id: 'session-2',
      userId: 2,
      title: 'Bob 的会话'
    }
    let rejectStop!: (reason: Error) => void
    let streamSignal: AbortSignal | undefined
    chatApi.getSessionList
      .mockResolvedValueOnce([session])
      .mockResolvedValueOnce([bobSession])
    chatApi.getSessionHistory.mockResolvedValue(historyPage())
    chatApi.requestSessionStop.mockImplementation(() => new Promise<void>((_, reject) => {
      rejectStop = reject
    }))
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      args[2].onAccepted?.()
      streamSignal = args[3]?.signal
      return new Promise<void>(resolve => {
        streamSignal?.addEventListener('abort', () => resolve(), { once: true })
      })
    })
    const warning = vi.spyOn(ElMessage, 'warning').mockImplementation(() => undefined as any)
    authStore.login(validToken('alice'), {
      userId: 1,
      phone: '13800138000',
      username: 'alice'
    })
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
      await flushPromises()
      await wrapper.get('[data-testid="chat-input"]').setValue('Alice 的停止请求')
      await wrapper.get('[data-testid="chat-send"]').trigger('click')
      await flushPromises()
      await wrapper.get('[data-testid="chat-stop"]').trigger('click')
      await flushPromises()

      authStore.login(validToken('bob'), {
        userId: 2,
        phone: '13900139000',
        username: 'bob'
      })
      await flushPromises()
      rejectStop(new Error('late Alice stop failure'))
      await flushPromises()

      expect(streamSignal?.aborted).toBe(true)
      expect(wrapper.find('[data-testid="chat-session-session-1"]').exists()).toBe(false)
      expect(wrapper.get('[data-testid="chat-session-session-2"]').text()).toContain('Bob 的会话')
      expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
      expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeUndefined()
      expect(chatStore.state.streaming).toBe(false)
      expect(warning).not.toHaveBeenCalled()
    } finally {
      wrapper.unmount()
      warning.mockRestore()
    }
  })

  it('ignores a delayed Alice settlement-history failure after switching to Bob', async () => {
    const bobSession = {
      ...session,
      id: 'session-2',
      userId: 2,
      title: 'Bob 的会话'
    }
    let rejectSettlementHistory!: (reason: Error) => void
    let streamSignal: AbortSignal | undefined
    chatApi.getSessionList
      .mockResolvedValueOnce([session])
      .mockResolvedValueOnce([bobSession])
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockImplementationOnce(() => new Promise<ChatHistoryPage>((_, reject) => {
        rejectSettlementHistory = reject
      }))
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      args[2].onAccepted?.()
      streamSignal = args[3]?.signal
      return new Promise<void>(resolve => {
        streamSignal?.addEventListener('abort', () => resolve(), { once: true })
      })
    })
    const warning = vi.spyOn(ElMessage, 'warning').mockImplementation(() => undefined as any)
    const executeCommand = vi.fn().mockResolvedValue(true)
    authStore.login(validToken('alice'), {
      userId: 1,
      phone: '13800138000',
      username: 'alice'
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
      await flushPromises()
      await wrapper.get('[data-testid="chat-input"]').setValue('等待 Alice 的历史结算')
      await wrapper.get('[data-testid="chat-send"]').trigger('click')
      await flushPromises()
      await wrapper.get('[data-testid="chat-stop"]').trigger('click')
      await flushPromises()
      expect(chatApi.getSessionHistory).toHaveBeenCalledTimes(2)

      authStore.login(validToken('bob'), {
        userId: 2,
        phone: '13900139000',
        username: 'bob'
      })
      await flushPromises()
      rejectSettlementHistory(new Error('late Alice history failure'))
      await flushPromises()

      expect(streamSignal?.aborted).toBe(true)
      expect(wrapper.find('[data-testid="chat-session-session-1"]').exists()).toBe(false)
      expect(wrapper.get('[data-testid="chat-session-session-2"]').text()).toContain('Bob 的会话')
      expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
      expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeUndefined()
      expect(chatStore.state.streaming).toBe(false)
      expect(warning).not.toHaveBeenCalled()
    } finally {
      wrapper.unmount()
      warning.mockRestore()
    }
  })

  it('ignores delayed idle confirmation from a completed Alice stream after switching to Bob', async () => {
    const bobSession = {
      ...session,
      id: 'session-2',
      userId: 2,
      title: 'Bob 的会话'
    }
    let resolveAliceActivity!: (activity: { sessionId: string; active: boolean }) => void
    chatApi.getSessionList
      .mockResolvedValueOnce([session])
      .mockResolvedValueOnce([session])
      .mockResolvedValue([bobSession])
    chatApi.getSessionActivity
      .mockResolvedValueOnce({ sessionId: 'session-1', active: false })
      .mockImplementationOnce(() => new Promise(resolve => {
        resolveAliceActivity = resolve
      }))
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      args[2].onAccepted?.()
      args[2].onMessage('Alice 的临时回复')
      args[2].onFinish?.({ turnId: args[4], executionStatus: 'PARTIAL' })
    })
    const warning = vi.spyOn(ElMessage, 'warning').mockImplementation(() => undefined as any)
    authStore.login(validToken('alice'), {
      userId: 1,
      phone: '13800138000',
      username: 'alice'
    })
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
      await flushPromises()
      await wrapper.get('[data-testid="chat-input"]').setValue('等待 Alice 的 idle 确认')
      await wrapper.get('[data-testid="chat-send"]').trigger('click')
      await flushPromises()
      expect(chatApi.getSessionActivity).toHaveBeenCalledTimes(2)

      authStore.login(validToken('bob'), {
        userId: 2,
        phone: '13900139000',
        username: 'bob'
      })
      await flushPromises()
      resolveAliceActivity({ sessionId: 'session-1', active: false })
      await flushPromises()

      expect(wrapper.text()).not.toContain('Alice 的临时回复')
      expect(wrapper.find('[data-testid="chat-session-session-1"]').exists()).toBe(false)
      expect(wrapper.get('[data-testid="chat-session-session-2"]').text()).toContain('Bob 的会话')
      expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
      expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeUndefined()
      expect(chatStore.state.streaming).toBe(false)
      expect(chatApi.getSessionHistory).toHaveBeenCalledTimes(1)
      expect(warning).not.toHaveBeenCalled()
    } finally {
      wrapper.unmount()
      warning.mockRestore()
    }
  })

  it('ignores delayed terminal history from a completed Alice stream after switching to Bob', async () => {
    const bobSession = {
      ...session,
      id: 'session-2',
      userId: 2,
      title: 'Bob 的会话'
    }
    let resolveAliceHistory!: (history: ChatHistoryPage) => void
    let aliceTurnId = ''
    chatApi.getSessionList
      .mockResolvedValueOnce([session])
      .mockResolvedValueOnce([session])
      .mockResolvedValue([bobSession])
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockImplementationOnce(() => new Promise(resolve => {
        resolveAliceHistory = resolve
      }))
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      aliceTurnId = args[4]
      args[2].onAccepted?.()
      args[2].onMessage('Alice 的临时回复')
      args[2].onFinish?.({ turnId: aliceTurnId, executionStatus: 'PARTIAL' })
    })
    const warning = vi.spyOn(ElMessage, 'warning').mockImplementation(() => undefined as any)
    authStore.login(validToken('alice'), {
      userId: 1,
      phone: '13800138000',
      username: 'alice'
    })
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
      await flushPromises()
      await wrapper.get('[data-testid="chat-input"]').setValue('等待 Alice 的历史确认')
      await wrapper.get('[data-testid="chat-send"]').trigger('click')
      await flushPromises()
      expect(chatApi.getSessionHistory).toHaveBeenCalledTimes(2)

      authStore.login(validToken('bob'), {
        userId: 2,
        phone: '13900139000',
        username: 'bob'
      })
      await flushPromises()
      resolveAliceHistory(historyPage([
        { role: 'user', content: 'Alice 的旧问题', turnId: aliceTurnId },
        {
          role: 'assistant',
          content: 'Alice 的延迟终态',
          turnId: aliceTurnId,
          executionStatus: 'PARTIAL'
        }
      ]))
      await flushPromises()

      expect(wrapper.text()).not.toContain('Alice 的临时回复')
      expect(wrapper.text()).not.toContain('Alice 的延迟终态')
      expect(wrapper.find('[data-testid="chat-session-session-1"]').exists()).toBe(false)
      expect(wrapper.get('[data-testid="chat-session-session-2"]').text()).toContain('Bob 的会话')
      expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
      expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeUndefined()
      expect(chatStore.state.streaming).toBe(false)
      expect(warning).not.toHaveBeenCalled()
    } finally {
      wrapper.unmount()
      warning.mockRestore()
    }
  })

  it('renders an untitled backend session with the localized new-chat label', async () => {
    chatApi.getSessionList.mockResolvedValue([{ ...session, title: null }])
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()

    const item = wrapper.get('[data-testid="chat-session-session-1"]')
    expect(item.text()).toContain('新对话')
    expect(item.text()).not.toContain('New Chat')

    wrapper.unmount()
  })

  it('shows localized feedback when an explicit new-session request is rejected', async () => {
    const errorMessage = vi.spyOn(ElMessage, 'error').mockImplementation(() => undefined as any)
    chatApi.createSession.mockRejectedValue(new Error('session limit reached'))
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await wrapper.get('.new-chat-btn').trigger('click')
      await flushPromises()

      expect(errorMessage).toHaveBeenCalledWith('创建会话失败')
    } finally {
      wrapper.unmount()
      errorMessage.mockRestore()
    }
  })

  it('treats an incomplete new-session response as a visible failure', async () => {
    const errorMessage = vi.spyOn(ElMessage, 'error').mockImplementation(() => undefined as any)
    chatApi.createSession.mockResolvedValue({})
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await wrapper.get('.new-chat-btn').trigger('click')
      await flushPromises()

      expect(errorMessage).toHaveBeenCalledWith('创建会话失败')
      expect(wrapper.findAll('[data-testid^="chat-session-session-"]')).toHaveLength(0)
    } finally {
      wrapper.unmount()
      errorMessage.mockRestore()
    }
  })

  it('creates only one session when the new-chat button is clicked twice quickly', async () => {
    let resolveSession!: (value: typeof session) => void
    chatApi.createSession.mockReturnValue(new Promise<typeof session>(resolve => { resolveSession = resolve }))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    const button = wrapper.get('.new-chat-btn')
    await Promise.all([button.trigger('click'), button.trigger('click')])

    expect(chatApi.createSession).toHaveBeenCalledTimes(1)
    expect(button.attributes('disabled')).toBeDefined()

    resolveSession(session)
    await flushPromises()
    wrapper.unmount()
  })

  it('shows a retryable error instead of an empty conversation when history loading fails', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory
      .mockRejectedValueOnce(new Error('history unavailable'))
      .mockResolvedValueOnce(historyPage([{ role: 'assistant', content: '已恢复的历史消息' }]))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()

    expect(wrapper.find('[data-testid="chat-history-retry"]').exists()).toBe(true)
    expect(wrapper.find('.welcome-screen').exists()).toBe(false)
    expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeDefined()

    await wrapper.get('[data-testid="chat-history-retry"] button').trigger('click')
    await flushPromises()

    expect(chatApi.getSessionHistory).toHaveBeenCalledTimes(2)
    expect(wrapper.find('[data-testid="chat-history-retry"]').exists()).toBe(false)
    expect(wrapper.text()).toContain('已恢复的历史消息')
    wrapper.unmount()
  })

  it('submits protected approval as a structured command from the confirmation button', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getPendingConfirmation.mockResolvedValue({
      sessionId: 'session-1',
      kinds: ['DESTRUCTIVE']
    })
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      acceptAndFinishStream(args)
    })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('.protected-confirmation__button.is-confirm').trigger('click')
    await flushPromises()

    expect(chatApi.sendStreamChat).toHaveBeenCalledTimes(1)
    expect(chatApi.sendStreamChat.mock.calls[0][5]).toEqual({
      action: 'CONFIRM',
      kind: 'DESTRUCTIVE'
    })
    expect(chatApi.sendStreamChat.mock.calls[0][1]).toContain('确认按钮')

    wrapper.unmount()
  })

  it('renders every independently pending protected action in the flow layout', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getPendingConfirmation.mockResolvedValue({
      sessionId: 'session-1',
      kinds: ['DESTRUCTIVE', 'SCENE_REPLACEMENT']
    })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()

    expect(wrapper.findAll('[data-testid="chat-protected-confirmation"]')).toHaveLength(2)
    expect(wrapper.get('.input-floating-area').element.previousElementSibling)
      .toBe(wrapper.get('.messages-viewport').element)

    wrapper.unmount()
  })

  it('shows a retry state instead of treating a confirmation lookup failure as empty', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getPendingConfirmation
      .mockRejectedValueOnce(new Error('network unavailable'))
      .mockResolvedValueOnce({ sessionId: 'session-1', kinds: ['DESTRUCTIVE'] })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()

    expect(wrapper.find('[data-testid="chat-confirmation-load-error"]').exists()).toBe(true)
    await wrapper.get('[data-testid="chat-confirmation-load-error"] button').trigger('click')
    await flushPromises()

    expect(wrapper.find('[data-testid="chat-confirmation-load-error"]').exists()).toBe(false)
    expect(wrapper.findAll('[data-testid="chat-protected-confirmation"]')).toHaveLength(1)

    wrapper.unmount()
  })

  it('reattaches to an active server execution after reload', async () => {
    chatApi.getSessionList.mockResolvedValue([{ ...session, active: true }])
    chatApi.getSessionActivity.mockResolvedValue({ sessionId: 'session-1', active: true })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()

    expect(chatApi.getSessionHistory).toHaveBeenCalledWith('session-1', expect.any(AbortSignal))
    expect(wrapper.get('[data-testid="chat-session-active"]').attributes('title')).toBe('后台任务执行中')
    expect(wrapper.get('[data-testid="chat-remote-execution"]').text()).toContain('已重新连接到后台执行')
    expect(wrapper.get('[data-testid="chat-stop"]').attributes('title')).toBe('停止仍在后台运行的助手任务')
    expect(chatStore.state.streaming).toBe(true)

    wrapper.unmount()
  })

  it('prioritizes the selected active session when another active session appears first', async () => {
    const sessionA = { ...session, id: 'session-a', title: '会话 A', active: false }
    const sessionB = { ...session, id: 'session-b', title: '会话 B', active: false }
    chatApi.getSessionList
      .mockResolvedValueOnce([sessionA, sessionB])
      .mockResolvedValue([
        { ...sessionA, active: true },
        { ...sessionB, active: true }
      ])
    chatApi.getSessionHistory.mockImplementation(async (sessionId: string) =>
      historyPage([], sessionId))
    chatApi.getPendingConfirmation.mockImplementation(async (sessionId: string) => ({
      sessionId,
      kinds: []
    }))
    chatApi.getSessionActivity
      .mockResolvedValueOnce({ sessionId: 'session-b', active: false })
      .mockImplementation(async (sessionId: string) => ({ sessionId, active: true }))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-b"]').trigger('click')
    await flushPromises()

    chatStore.closeChat()
    await flushPromises()
    chatStore.openChat()
    await flushPromises()

    expect(chatApi.getSessionActivity.mock.calls.at(-1)?.[0]).toBe('session-b')
    expect(wrapper.get('[data-testid="chat-session-session-b"]')
      .element.parentElement?.classList.contains('active')).toBe(true)
    expect(wrapper.find('[data-testid="chat-remote-execution"]').exists()).toBe(true)
    expect(chatStore.state.streaming).toBe(true)

    wrapper.unmount()
  })

  it('switches from an idle selection to authoritative active work and keeps the Board locked', async () => {
    const sessionA = { ...session, id: 'session-a', title: '会话 A', active: false }
    const sessionB = { ...session, id: 'session-b', title: '会话 B', active: false }
    chatApi.getSessionList
      .mockResolvedValueOnce([sessionA, sessionB])
      .mockResolvedValue([
        { ...sessionA, active: true },
        sessionB
      ])
    chatApi.getSessionHistory.mockImplementation(async (sessionId: string) =>
      historyPage([], sessionId))
    chatApi.getPendingConfirmation.mockImplementation(async (sessionId: string) => ({
      sessionId,
      kinds: []
    }))
    chatApi.getSessionActivity
      .mockResolvedValueOnce({ sessionId: 'session-b', active: false })
      .mockImplementation(async (sessionId: string) => ({
        sessionId,
        active: sessionId === 'session-a'
      }))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-b"]').trigger('click')
    await flushPromises()

    chatStore.closeChat()
    await flushPromises()
    chatStore.openChat()
    await flushPromises()

    expect(chatApi.getSessionActivity.mock.calls.at(-1)?.[0]).toBe('session-a')
    expect(chatApi.getSessionHistory.mock.calls.at(-1)?.[0]).toBe('session-a')
    expect(wrapper.get('[data-testid="chat-session-session-a"]')
      .element.parentElement?.classList.contains('active')).toBe(true)
    expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeDefined()
    expect(wrapper.find('[data-testid="chat-remote-execution"]').exists()).toBe(true)
    expect(chatStore.state.streaming).toBe(true)

    wrapper.unmount()
  })

  it('keeps a known active session locked when history loading fails', async () => {
    chatApi.getSessionList.mockResolvedValue([{ ...session, active: true }])
    chatApi.getSessionHistory.mockRejectedValue(new Error('history unavailable'))
    chatApi.getSessionActivity.mockResolvedValue({ sessionId: 'session-1', active: true })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()

    expect(wrapper.find('[data-testid="chat-remote-execution"]').exists()).toBe(true)
    expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeDefined()
    expect(chatStore.state.streaming).toBe(true)

    wrapper.unmount()
  })

  it('stops a reattached execution and reloads its persisted terminal result', async () => {
    const terminalHistory = historyPage([
      { role: 'user', content: '运行验证', turnId: 'remote-turn' },
      {
        role: 'assistant',
        content: '用户已停止。',
        turnId: 'remote-turn',
        executionStatus: 'STOPPED'
      }
    ])
    chatApi.getSessionList
      .mockResolvedValueOnce([{ ...session, active: true }])
      .mockResolvedValue([{ ...session, active: false }])
    chatApi.getSessionActivity
      .mockResolvedValueOnce({ sessionId: 'session-1', active: true })
      .mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockResolvedValue(terminalHistory)
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-stop"]').trigger('click')
    await flushPromises()

    expect(chatApi.requestSessionStop).toHaveBeenCalledWith('session-1', undefined)
    expect(executeCommand).toHaveBeenCalledWith({
      type: 'REFRESH_DATA',
      payload: { target: 'board_state' }
    })
    expect(wrapper.text()).toContain('用户已停止。')
    expect(wrapper.find('[data-testid="chat-remote-execution"]').exists()).toBe(false)
    expect(chatStore.state.streaming).toBe(false)

    wrapper.unmount()
  })

  it('automatically reloads a reattached execution when it finishes remotely', async () => {
    vi.useFakeTimers()
    const terminalHistory = historyPage([
      { role: 'user', content: '检查场景', turnId: 'remote-turn' },
      {
        role: 'assistant',
        content: '后台检查已完成。',
        turnId: 'remote-turn',
        executionStatus: 'COMPLETED',
        executionTrace: [
          { stage: 'TOOL_EXECUTION', toolName: 'board_overview', round: 1 },
          { stage: 'TOOL_RESULT', toolName: 'board_overview', round: 1, outcome: 'USABLE' }
        ]
      }
    ])
    chatApi.getSessionList
      .mockResolvedValueOnce([{ ...session, active: true }])
      .mockResolvedValue([{ ...session, active: false }])
    chatApi.getSessionActivity
      .mockResolvedValueOnce({ sessionId: 'session-1', active: true })
      .mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockResolvedValue(terminalHistory)
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    try {
      await flushPromises()
      expect(wrapper.find('[data-testid="chat-remote-execution"]').exists()).toBe(true)

      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()

      expect(wrapper.text()).toContain('后台检查已完成。')
      expect(wrapper.find('[data-testid="chat-remote-execution"]').exists()).toBe(false)
      expect(executeCommand).toHaveBeenCalledWith({
        type: 'REFRESH_DATA',
        payload: { target: 'board_state' }
      })
    } finally {
      wrapper.unmount()
      vi.useRealTimers()
    }
  })

  it('unlocks after a reattached execution ends with authoritative user-only history', async () => {
    vi.useFakeTimers()
    const warning = vi.spyOn(ElMessage, 'warning').mockImplementation(() => undefined as any)
    const userOnlyHistory = historyPage([
      { role: 'user', content: '检查后台状态', turnId: 'remote-turn' }
    ])
    chatApi.getSessionList
      .mockResolvedValueOnce([{ ...session, active: true }])
      .mockResolvedValue([{ ...session, active: false }])
    chatApi.getSessionActivity
      .mockResolvedValueOnce({ sessionId: 'session-1', active: true })
      .mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.getSessionHistory.mockResolvedValue(userOnlyHistory)
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    try {
      await flushPromises()
      expect(wrapper.find('[data-testid="chat-remote-execution"]').exists()).toBe(true)

      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()

      expect(wrapper.text()).toContain('检查后台状态')
      expect(wrapper.find('[data-testid="chat-remote-execution"]').exists()).toBe(false)
      expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
      expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeUndefined()
      expect(chatStore.state.streaming).toBe(false)
      expect(warning).toHaveBeenCalledWith(
        '回复流不完整，已恢复服务端保存的会话历史；未保存的临时回复已移除。'
      )
    } finally {
      wrapper.unmount()
      warning.mockRestore()
      vi.useRealTimers()
    }
  })

  it('does not let a stale initial history response overwrite remote settlement history', async () => {
    vi.useFakeTimers()
    let resolveInitialHistory!: (page: ChatHistoryPage) => void
    const initialHistory = new Promise<ChatHistoryPage>(resolve => {
      resolveInitialHistory = resolve
    })
    const terminalHistory = historyPage([
      { role: 'user', content: '检查场景', turnId: 'remote-turn' },
      {
        role: 'assistant',
        content: '最新的后台终态。',
        turnId: 'remote-turn',
        executionStatus: 'PARTIAL'
      }
    ])
    chatApi.getSessionList
      .mockResolvedValueOnce([{ ...session, active: true }])
      .mockResolvedValue([{ ...session, active: false }])
    chatApi.getSessionActivity
      .mockResolvedValueOnce({ sessionId: 'session-1', active: true })
      .mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.getSessionHistory
      .mockImplementationOnce(() => initialHistory)
      .mockResolvedValue(terminalHistory)
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    try {
      await flushPromises()
      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()

      expect(wrapper.text()).toContain('最新的后台终态。')

      resolveInitialHistory(historyPage([
        { role: 'assistant', content: '过期的初始历史。', executionStatus: 'PARTIAL' }
      ]))
      await flushPromises()

      expect(wrapper.text()).toContain('最新的后台终态。')
      expect(wrapper.text()).not.toContain('过期的初始历史。')
    } finally {
      wrapper.unmount()
      vi.useRealTimers()
    }
  })

  it('clears an initial history failure after remote settlement reloads authoritative history', async () => {
    vi.useFakeTimers()
    const terminalHistory = historyPage([
      { role: 'user', content: '检查场景', turnId: 'remote-turn' },
      {
        role: 'assistant',
        content: '后台恢复后的结果。',
        turnId: 'remote-turn',
        executionStatus: 'PARTIAL'
      }
    ])
    chatApi.getSessionList
      .mockResolvedValueOnce([{ ...session, active: true }])
      .mockResolvedValue([{ ...session, active: false }])
    chatApi.getSessionActivity
      .mockResolvedValueOnce({ sessionId: 'session-1', active: true })
      .mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.getSessionHistory
      .mockRejectedValueOnce(new Error('initial history unavailable'))
      .mockResolvedValue(terminalHistory)
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    try {
      await flushPromises()
      expect(wrapper.find('[data-testid="chat-history-retry"]').exists()).toBe(true)

      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()

      expect(wrapper.text()).toContain('后台恢复后的结果。')
      expect(wrapper.find('[data-testid="chat-history-retry"]').exists()).toBe(false)
      expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeUndefined()
    } finally {
      wrapper.unmount()
      vi.useRealTimers()
    }
  })

  it('reloads terminal history even when Board reconciliation must be retried', async () => {
    vi.useFakeTimers()
    const terminalHistory = historyPage([
      { role: 'user', content: '检查场景', turnId: 'remote-turn' },
      {
        role: 'assistant',
        content: '后台结果已持久化。',
        turnId: 'remote-turn',
        executionStatus: 'COMPLETED',
        executionTrace: [
          { stage: 'TOOL_EXECUTION', toolName: 'board_overview', round: 1 },
          { stage: 'TOOL_RESULT', toolName: 'board_overview', round: 1, outcome: 'USABLE' }
        ]
      }
    ])
    chatApi.getSessionList
      .mockResolvedValueOnce([{ ...session, active: true }])
      .mockResolvedValue([{ ...session, active: false }])
    chatApi.getSessionActivity
      .mockResolvedValueOnce({ sessionId: 'session-1', active: true })
      .mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockResolvedValue(terminalHistory)
    const executeCommand = vi.fn().mockResolvedValue(false)
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    try {
      await flushPromises()
      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()

      expect(wrapper.text()).toContain('后台结果已持久化。')
      expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(true)
      expect(chatStore.state.streaming).toBe(true)
    } finally {
      wrapper.unmount()
      vi.useRealTimers()
    }
  })

  it('shows a persisted disconnect status even when no progress frame reached the client', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue(historyPage([
      { role: 'user', content: '运行验证' },
      {
        role: 'assistant',
        content: '连接在任务完成前中断。',
        executionStatus: 'DISCONNECTED',
        executionElapsedSeconds: 4
      }
    ]))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()

    const status = wrapper.get('[data-testid="chat-terminal-status"]')
    expect(status.text()).toContain('连接中断')
    expect(status.text()).toContain('4 秒')

    wrapper.unmount()
  })

  it('shows a completed status after the same AI tool corrects its earlier partial result', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue(historyPage([
      { role: 'user', content: '生成完整场景', turnId: 'turn-recovered' },
      {
        role: 'assistant',
        content: '场景已补全。',
        turnId: 'turn-recovered',
        executionStatus: 'COMPLETED',
        executionTrace: [
          { stage: 'TOOL_EXECUTION', toolName: 'recommend_scenario', round: 1 },
          { stage: 'TOOL_RESULT', toolName: 'recommend_scenario', round: 1, outcome: 'PARTIAL' },
          { stage: 'TOOL_EXECUTION', toolName: 'recommend_scenario', round: 2 },
          { stage: 'TOOL_RESULT', toolName: 'recommend_scenario', round: 2, outcome: 'USABLE' }
        ]
      }
    ]))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()

    expect(wrapper.get('.chat-execution-state').text()).toBe('已完成')

    wrapper.unmount()
  })

  it('distinguishes no-tool replies and treats a missing terminal status as unconfirmed', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue(historyPage([
      { role: 'user', content: '解释一下 LTL' },
      {
        role: 'assistant',
        content: 'LTL 是线性时序逻辑。',
        executionStatus: 'PARTIAL',
        executionElapsedSeconds: 2,
        executionTrace: [
          { stage: 'CONTEXT_READY' },
          { stage: 'PLANNING', round: 1 },
          { stage: 'WRITING_RESPONSE' }
        ]
      },
      { role: 'user', content: '尝试检查画布' },
      {
        role: 'assistant',
        content: '工具启动后结果未确认。',
        executionStatus: 'PARTIAL',
        executionTrace: [{ stage: 'TOOL_EXECUTION', toolName: 'board_overview' }]
      },
      { role: 'user', content: '读取旧的部分结果' },
      {
        role: 'assistant',
        content: '旧记录没有执行轨迹。',
        executionStatus: 'PARTIAL'
      },
      { role: 'user', content: '检查画布' },
      {
        role: 'assistant',
        content: '服务端已移除无法证明的完成状态。',
        executionElapsedSeconds: 3
      },
      { role: 'user', content: '读取当前完成记录' },
      {
        role: 'assistant',
        content: '已有可验证的完成记录。',
        executionStatus: 'COMPLETED',
        executionElapsedSeconds: 3,
        executionTrace: [
          { stage: 'TOOL_EXECUTION', toolName: 'board_overview', round: 1 },
          { stage: 'TOOL_RESULT', toolName: 'board_overview', round: 1, outcome: 'USABLE' }
        ]
      }
    ]))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()

    const statuses = wrapper.findAll('.chat-execution-state')
    expect(statuses).toHaveLength(4)
    expect(statuses[0].text()).toContain('未执行平台工具')
    expect(statuses[0].text()).not.toContain('已完成')
    expect(statuses[1].text()).toContain('部分完成')
    expect(statuses[1].text()).not.toContain('未执行平台工具')
    expect(statuses[2].text()).toContain('部分完成')
    expect(statuses[2].text()).not.toContain('未执行平台工具')
    expect(wrapper.findAll('.ai-row')[3].text()).not.toContain('已完成')
    expect(statuses[3].text()).toContain('已完成')

    wrapper.unmount()
  })

  it('labels a reviewable incomplete tool result as partial rather than successful', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue(historyPage([
      { role: 'user', content: '生成完整场景' },
      {
        role: 'assistant',
        content: '返回了一个仍缺少规则的草案。',
        executionStatus: 'PARTIAL',
        executionTrace: [{
          stage: 'TOOL_RESULT',
          round: 1,
          toolName: 'recommend_scenario',
          outcome: 'PARTIAL',
          successfulSteps: 1,
          failedSteps: 0,
          unconfirmedSteps: 0
        }]
      }
    ]))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()

    expect(wrapper.get('.chat-execution-outcome').text()).toBe('部分结果')
    expect(wrapper.get('[data-testid="chat-execution-trace"]').text())
      .toContain('可审阅但不完整')
    expect(wrapper.get('.chat-execution-outcome').text()).not.toBe('成功')

    wrapper.unmount()
  })

  it('never renders a missing terminal status as completed', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue(historyPage([
      { role: 'user', content: '检查未来状态' },
      {
        role: 'assistant',
        content: '该记录没有可确认的终态。'
      }
    ]))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()

    expect(wrapper.text()).toContain('该记录没有可确认的终态。')
    expect(wrapper.find('[data-testid="chat-terminal-status"]').exists()).toBe(false)
    expect(wrapper.text()).not.toContain('已完成')

    wrapper.unmount()
  })

  it('shows user stop and confirmation-pending outcomes as distinct states', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue(historyPage([
      { role: 'user', content: '运行验证' },
      { role: 'assistant', content: '已停止。', executionStatus: 'STOPPED' },
      { role: 'user', content: '删除设备' },
      {
        role: 'assistant',
        content: '已完成前置步骤，请确认删除。',
        executionStatus: 'AWAITING_CONFIRMATION',
        executionTrace: [
          { stage: 'TOOL_RESULT', outcome: 'USABLE', successfulSteps: 1 }
        ]
      }
    ]))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()

    const statuses = wrapper.findAll('.chat-execution-state')
    expect(statuses[0].text()).toContain('用户已停止')
    expect(statuses[1].text()).toContain('部分完成，等待确认')

    wrapper.unmount()
  })

  it('prefers an explicit stopped outcome over an earlier execution guard', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue(historyPage([
      { role: 'user', content: '运行验证' },
      {
        role: 'assistant',
        content: '用户已停止。',
        executionStatus: 'STOPPED',
        executionTrace: [{ stage: 'EXECUTION_GUARD', outcome: 'NO_PROGRESS' }]
      }
    ]))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()

    expect(wrapper.get('.chat-execution-state').text()).toBe('用户已停止')

    wrapper.unmount()
  })

  it('registers an explicit stop before aborting and reconciling the active response', async () => {
    const clearIntervalSpy = vi.spyOn(window, 'clearInterval')
    let streamSignal: AbortSignal | undefined
    let activeTurnId = ''
    let resolveStop!: () => void
    const stopOrder: string[] = []
    chatApi.createSession.mockResolvedValue(session)
    chatApi.requestSessionStop.mockImplementation(() => new Promise<void>(resolve => {
      stopOrder.push('stop-request')
      resolveStop = resolve
    }))
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      args[2].onAccepted?.()
      streamSignal = args[3]?.signal
      activeTurnId = args[4]
      return new Promise<void>(resolve => {
        streamSignal?.addEventListener('abort', () => {
          stopOrder.push('transport-abort')
          resolve()
        }, { once: true })
      })
    })
    chatApi.getSessionHistory.mockImplementation(async () => historyPage([
      { role: 'user', content: '运行验证', turnId: activeTurnId },
      {
        role: 'assistant',
        content: '用户已停止。',
        turnId: activeTurnId,
        executionStatus: 'STOPPED'
      }
    ]))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('运行验证')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-stop"]').trigger('click')
    await flushPromises()

    expect(chatApi.requestSessionStop).toHaveBeenCalledWith('session-1', activeTurnId)
    expect(streamSignal?.aborted).toBe(false)
    expect(chatApi.getSessionActivity).not.toHaveBeenCalled()

    resolveStop()
    await flushPromises()

    expect(streamSignal?.aborted).toBe(true)
    expect(stopOrder).toEqual(['stop-request', 'transport-abort'])
    expect(clearIntervalSpy).toHaveBeenCalled()

    wrapper.unmount()
    clearIntervalSpy.mockRestore()
  })

  it('treats a stop 404 as an authoritative external deletion and unlocks', async () => {
    let streamSignal: AbortSignal | undefined
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue(historyPage())
    chatApi.requestSessionStop.mockRejectedValueOnce(notFoundError())
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      args[2].onAccepted?.()
      streamSignal = args[3]?.signal
      return new Promise<void>(resolve => {
        streamSignal?.addEventListener('abort', () => resolve(), { once: true })
      })
    })
    const warning = vi.spyOn(ElMessage, 'warning').mockImplementation(() => undefined as any)
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
      await flushPromises()
      await wrapper.get('[data-testid="chat-input"]').setValue('停止已删除的会话')
      await wrapper.get('[data-testid="chat-send"]').trigger('click')
      await flushPromises()
      await wrapper.get('[data-testid="chat-stop"]').trigger('click')
      await flushPromises()

      expect(streamSignal?.aborted).toBe(true)
      expect(wrapper.find('[data-testid="chat-session-session-1"]').exists()).toBe(false)
      expect(wrapper.findAll('.msg-row')).toHaveLength(0)
      expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
      expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeUndefined()
      expect(chatStore.state.streaming).toBe(false)
      expect(warning).toHaveBeenCalledWith(i18n.global.t('app.chat.sessionRemovedExternally'))
    } finally {
      wrapper.unmount()
      warning.mockRestore()
    }
  })

  it('keeps a failed stop locked and registers it again before retry recovery', async () => {
    let streamSignal: AbortSignal | undefined
    let activeTurnId = ''
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockImplementation(async () => historyPage([
        { role: 'user', content: '需要重试停止', turnId: activeTurnId },
        {
          role: 'assistant',
          content: '服务端已确认停止。',
          turnId: activeTurnId,
          executionStatus: 'STOPPED'
        }
      ]))
    chatApi.requestSessionStop
      .mockRejectedValueOnce(new Error('temporary stop failure'))
      .mockResolvedValueOnce(undefined)
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      args[2].onAccepted?.()
      activeTurnId = args[4]
      streamSignal = args[3]?.signal
      return new Promise<void>(resolve => {
        streamSignal?.addEventListener('abort', () => resolve(), { once: true })
      })
    })
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('需要重试停止')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-stop"]').trigger('click')
    await flushPromises()

    expect(streamSignal?.aborted).toBe(true)
    expect(chatApi.requestSessionStop).toHaveBeenCalledTimes(1)
    expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(true)
    expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeDefined()
    expect(chatStore.state.streaming).toBe(true)

    await wrapper.get('[data-testid="chat-reconciliation-retry"]').trigger('click')
    await flushPromises()

    expect(chatApi.requestSessionStop).toHaveBeenCalledTimes(2)
    expect(chatApi.requestSessionStop).toHaveBeenNthCalledWith(2, 'session-1', activeTurnId)
    expect(wrapper.text()).toContain('服务端已确认停止。')
    expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
    expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeUndefined()
    expect(chatStore.state.streaming).toBe(false)

    wrapper.unmount()
  })

  it('restores the draft when stopped before stream acceptance leaves no admitted turn', async () => {
    let streamSignal: AbortSignal | undefined
    let activeTurnId = ''
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue(historyPage())
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      streamSignal = args[3]?.signal
      activeTurnId = args[4]
      return new Promise<void>(resolve => {
        streamSignal?.addEventListener('abort', () => resolve(), { once: true })
      })
    })
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('停止前请保留这段草稿')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-stop"]').trigger('click')
    await flushPromises()

    expect(chatApi.requestSessionStop).toHaveBeenCalledWith('session-1', activeTurnId)
    expect(streamSignal?.aborted).toBe(true)
    expect(wrapper.findAll('.msg-row')).toHaveLength(0)
    expect((wrapper.get('[data-testid="chat-input"]').element as HTMLTextAreaElement).value)
      .toBe('停止前请保留这段草稿')
    expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
    expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeUndefined()
    expect(chatStore.state.streaming).toBe(false)

    wrapper.unmount()
  })

  it('cancels a send during initial session creation without leaving optimistic messages', async () => {
    let creationSignal: AbortSignal | undefined
    chatApi.createSession.mockImplementation((signal?: AbortSignal) => {
      creationSignal = signal
      return new Promise((_, reject) => {
        signal?.addEventListener('abort', () => reject(Object.assign(new Error('cancelled'), {
          name: 'CanceledError'
        })), { once: true })
      })
    })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('保留这条尚未发送的请求')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-stop"]').trigger('click')
    await flushPromises()

    expect(creationSignal?.aborted).toBe(true)
    expect(chatApi.sendStreamChat).not.toHaveBeenCalled()
    expect(wrapper.findAll('.msg-row')).toHaveLength(0)
    expect((wrapper.get('[data-testid="chat-input"]').element as HTMLTextAreaElement).value)
      .toBe('保留这条尚未发送的请求')
    expect(wrapper.text()).not.toContain('响应已停止')
    expect(chatStore.state.streaming).toBe(false)

    wrapper.unmount()
  })

  it('releases a completed turn when another window deletes its session before history reload', async () => {
    const warning = vi.spyOn(ElMessage, 'warning').mockImplementation(() => undefined as any)
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockRejectedValueOnce(notFoundError())
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      acceptAndFinishStream(args)
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('检查跨标签删除')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(executeCommand).toHaveBeenCalledWith({
      type: 'REFRESH_DATA',
      payload: { target: 'board_state' }
    })
    expect(wrapper.find('[data-testid="chat-session-session-1"]').exists()).toBe(false)
    expect(wrapper.findAll('.msg-row')).toHaveLength(0)
    expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
    expect(chatStore.state.streaming).toBe(false)
    expect(warning).toHaveBeenCalledWith(i18n.global.t('app.chat.sessionRemovedExternally'))

    wrapper.unmount()
    warning.mockRestore()
  })

  it('releases a stopped turn when another window deletes its session before settlement history', async () => {
    const executeCommand = vi.fn().mockResolvedValue(true)
    let streamSignal: AbortSignal | undefined
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockRejectedValueOnce(notFoundError())
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      args[2].onAccepted?.()
      streamSignal = args[3]?.signal
      return new Promise<void>(resolve => {
        streamSignal?.addEventListener('abort', () => resolve(), { once: true })
      })
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('停止后同步删除')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-stop"]').trigger('click')
    await flushPromises()

    expect(streamSignal?.aborted).toBe(true)
    expect(executeCommand).toHaveBeenCalledWith({
      type: 'REFRESH_DATA',
      payload: { target: 'board_state' }
    })
    expect(wrapper.find('[data-testid="chat-session-session-1"]').exists()).toBe(false)
    expect(wrapper.findAll('.msg-row')).toHaveLength(0)
    expect(chatStore.state.streaming).toBe(false)

    wrapper.unmount()
  })

  it('keeps the current local turn when history only contains an older terminal reply', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockResolvedValueOnce(historyPage([
        { role: 'user', content: '旧问题', turnId: 'old-turn' },
        {
          role: 'assistant',
          content: '旧回答',
          turnId: 'old-turn',
          executionStatus: 'PARTIAL'
        }
      ]))
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      acceptAndFinishStream(args)
    })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('当前问题')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(chatApi.sendStreamChat.mock.calls[0][4]).toEqual(expect.any(String))
    expect(wrapper.text()).toContain('当前问题')
    expect(wrapper.text()).not.toContain('旧回答')

    wrapper.unmount()
  })

  it('waits for idle, reconciles the Board, and replaces an incomplete accepted stream with server history', async () => {
    const warning = vi.spyOn(ElMessage, 'warning').mockImplementation(() => undefined as any)
    const executeCommand = vi.fn().mockResolvedValue(true)
    let activeTurnId = ''
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockImplementationOnce(async () => historyPage([{
        role: 'user',
        content: '检查服务端状态',
        turnId: activeTurnId
      }]))
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      const callbacks = args[2]
      activeTurnId = args[4]
      callbacks.onAccepted?.()
      callbacks.onMessage('未持久化的临时回答')
      const error = new ChatStreamError('missing terminal', { kind: 'INCOMPLETE_STREAM' })
      callbacks.onError?.(error)
      throw error
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('检查服务端状态')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(chatApi.getSessionActivity).toHaveBeenCalledWith('session-1', {})
    expect(executeCommand).toHaveBeenCalledWith({
      type: 'REFRESH_DATA',
      payload: { target: 'board_state' }
    })
    expect(chatApi.getSessionActivity.mock.invocationCallOrder[0])
      .toBeLessThan(executeCommand.mock.invocationCallOrder[0])
    expect(wrapper.text()).toContain('检查服务端状态')
    expect(wrapper.text()).not.toContain('未持久化的临时回答')
    expect(wrapper.text()).not.toContain('missing terminal')
    expect(warning).toHaveBeenCalledWith(
      '回复流不完整，已恢复服务端保存的会话历史；未保存的临时回复已移除。'
    )

    wrapper.unmount()
    warning.mockRestore()
  })

  it('treats a transport failure before response headers as an unknown admission outcome', async () => {
    const executeCommand = vi.fn().mockResolvedValue(true)
    let activeTurnId = ''
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockImplementationOnce(async () => historyPage([{
        role: 'user',
        content: '不要重复提交',
        turnId: activeTurnId
      }]))
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      activeTurnId = args[4]
      const error = new TypeError('connection reset before headers')
      args[2].onError?.(error)
      throw error
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('不要重复提交')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(chatApi.getSessionActivity).toHaveBeenCalledWith('session-1', {})
    expect(executeCommand).toHaveBeenCalledWith({
      type: 'REFRESH_DATA',
      payload: { target: 'board_state' }
    })
    expect(wrapper.text()).toContain('不要重复提交')
    expect(wrapper.text()).not.toContain('connection reset before headers')
    expect((wrapper.get('[data-testid="chat-input"]').element as HTMLTextAreaElement).value).toBe('')
    expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)

    wrapper.unmount()
  })

  it('restores the draft only after history proves an ambiguous turn was not admitted', async () => {
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockResolvedValueOnce(historyPage())
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      const error = new TypeError('connection reset before headers')
      args[2].onError?.(error)
      throw error
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('请保留这段草稿')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(wrapper.findAll('.msg-row')).toHaveLength(0)
    expect((wrapper.get('[data-testid="chat-input"]').element as HTMLTextAreaElement).value)
      .toBe('请保留这段草稿')
    expect(executeCommand).toHaveBeenCalledTimes(1)

    wrapper.unmount()
  })

  it('keeps interactions locked until terminal history can be reloaded', async () => {
    const executeCommand = vi.fn().mockResolvedValue(true)
    let activeTurnId = ''
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockRejectedValueOnce(new Error('history temporarily unavailable'))
      .mockImplementationOnce(async () => historyPage([
        { role: 'user', content: '检查最终状态', turnId: activeTurnId },
        {
          role: 'assistant',
          content: '已保存的最终回答',
          turnId: activeTurnId,
          executionStatus: 'PARTIAL'
        }
      ]))
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      activeTurnId = args[4]
      acceptAndFinishStream(args)
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('检查最终状态')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(true)
    expect(wrapper.get('[data-testid="chat-send"]').attributes('disabled')).toBeDefined()
    expect(chatStore.state.streaming).toBe(true)

    await wrapper.get('[data-testid="chat-reconciliation-retry"]').trigger('click')
    await flushPromises()

    expect(executeCommand).toHaveBeenCalledWith({
      type: 'REFRESH_DATA',
      payload: { target: 'board_state' }
    })
    expect(wrapper.text()).toContain('已保存的最终回答')
    expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
    expect(chatStore.state.streaming).toBe(false)

    wrapper.unmount()
  })

  it('keeps the settlement lock when history reload fails and replaces the draft on retry', async () => {
    vi.useFakeTimers()
    const warning = vi.spyOn(ElMessage, 'warning').mockImplementation(() => undefined as any)
    const executeCommand = vi.fn().mockResolvedValue(true)
    let activeTurnId = ''
    let sessionActive = false
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionActivity.mockImplementation(async () => ({
      sessionId: 'session-1',
      active: sessionActive
    }))
    chatApi.getSessionHistory
      .mockResolvedValueOnce(historyPage())
      .mockRejectedValueOnce(new Error('history temporarily unavailable'))
      .mockImplementationOnce(async () => historyPage([{
        role: 'user',
        content: '检查延迟结算状态',
        turnId: activeTurnId
      }]))
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      const callbacks = args[2]
      activeTurnId = args[4]
      callbacks.onAccepted?.()
      callbacks.onMessage('稍后必须移除的临时回答')
      const error = new ChatStreamError('missing terminal', { kind: 'INCOMPLETE_STREAM' })
      callbacks.onError?.(error)
      throw error
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
      await flushPromises()
      sessionActive = true
      await wrapper.get('[data-testid="chat-input"]').setValue('检查延迟结算状态')
      const sendPromise = wrapper.get('[data-testid="chat-send"]').trigger('click')
      await flushPromises()
      await vi.advanceTimersByTimeAsync(10_500)
      await sendPromise
      await flushPromises()

      expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(true)
      expect(wrapper.text()).toContain('稍后必须移除的临时回答')

      sessionActive = false
      await wrapper.get('[data-testid="chat-reconciliation-retry"]').trigger('click')
      await flushPromises()

      expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(true)
      expect(wrapper.text()).toContain('稍后必须移除的临时回答')
      expect(chatStore.state.streaming).toBe(true)

      await wrapper.get('[data-testid="chat-reconciliation-retry"]').trigger('click')
      await flushPromises()

      expect(executeCommand).toHaveBeenCalledWith({
        type: 'REFRESH_DATA',
        payload: { target: 'board_state' }
      })
      expect(wrapper.text()).toContain('检查延迟结算状态')
      expect(wrapper.text()).not.toContain('稍后必须移除的临时回答')
      expect(wrapper.text()).not.toContain('missing terminal')
      expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
      expect(warning).toHaveBeenCalledWith(
        '回复流不完整，已恢复服务端保存的会话历史；未保存的临时回复已移除。'
      )
    } finally {
      wrapper.unmount()
      warning.mockRestore()
      vi.useRealTimers()
    }
  })

  it('removes an optimistic turn and restores the draft when the server rejects before streaming', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.sendStreamChat.mockRejectedValue(new ChatStreamError('busy', {
      kind: 'HTTP_ERROR',
      status: 409
    }))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('不要留下虚假消息')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(wrapper.findAll('.msg-row')).toHaveLength(0)
    expect((wrapper.get('[data-testid="chat-input"]').element as HTMLTextAreaElement).value)
      .toBe('不要留下虚假消息')

    wrapper.unmount()
  })

  it('explains a stored-history limit instead of reporting a concurrency conflict', async () => {
    const errorMessage = vi.spyOn(ElMessage, 'error').mockImplementation(() => undefined as any)
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.sendStreamChat.mockRejectedValue(new ChatStreamError('limit', {
      kind: 'HTTP_ERROR',
      status: 429,
      reasonCode: 'CHAT_HISTORY_LIMIT_REACHED'
    }))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('继续检查')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(errorMessage).toHaveBeenCalledWith(
      '发送消息失败：当前对话已接近历史容量上限，请新建对话，或删除不再需要的旧对话。'
    )
    wrapper.unmount()
  })

  it('loads older history through the server cursor without replacing recent messages', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory
      .mockResolvedValueOnce({
        ...historyPage([
          { id: 2, role: 'user', content: '较新的问题' },
          { id: 3, role: 'assistant', content: '较新的回答' }
        ]),
        nextBeforeId: 2,
        hasMore: true
      })
      .mockResolvedValueOnce(historyPage([{ id: 1, role: 'user', content: '最早的问题' }]))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-load-older"]').trigger('click')
    await flushPromises()

    expect(chatApi.getSessionHistory).toHaveBeenLastCalledWith('session-1', { beforeId: 2, limit: 50 })
    expect(wrapper.text().indexOf('最早的问题')).toBeLessThan(wrapper.text().indexOf('较新的问题'))
    expect(wrapper.find('[data-testid="chat-load-older"]').exists()).toBe(false)

    wrapper.unmount()
  })

  it('renders the pending response inside one full-width assistant activity bubble', async () => {
    let finishStream!: () => void
    chatApi.createSession.mockResolvedValue(session)
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      args[2].onAccepted?.()
      return new Promise<void>(resolve => {
        finishStream = () => {
          args[2].onFinish?.({ turnId: args[4], executionStatus: 'PARTIAL' })
          resolve()
        }
      })
    })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('请检查当前画布')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    const pending = wrapper.get('[data-testid="chat-assistant-pending"]')
    const pendingBubble = wrapper.get('article.assistant-pending-body')
    expect(pendingBubble.element.contains(pending.element)).toBe(true)
    expect(pendingBubble.classes()).toContain('has-execution-trace')
    expect(pendingBubble.text()).toContain('思考与执行')
    expect(pendingBubble.text()).toContain('接收任务')
    expect(wrapper.find('.msg-content-wrapper > .thinking-state').exists()).toBe(false)

    finishStream()
    await flushPromises()
    wrapper.unmount()
  })

  it('keeps a visible execution trace through tool work and after the response completes', async () => {
    chatApi.createSession.mockResolvedValue(session)
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      const callbacks = args[2]
      callbacks.onAccepted?.()
      callbacks.onProgress({
        stage: 'CONTEXT_READY',
        toolName: null,
        round: null,
        outcome: null,
        successfulSteps: null,
        failedSteps: null,
        unconfirmedSteps: null
      })
      callbacks.onProgress({
        stage: 'PLANNING',
        round: 1,
        successfulSteps: 0,
        failedSteps: 0,
        unconfirmedSteps: 0
      })
      callbacks.onProgress({
        stage: 'REASONING',
        round: 1,
        detail: '当前目标是补齐客厅照明；模板已经确认可用，下一步先创建设备，再检查是否还需要规则。'
      })
      callbacks.onProgress({ stage: 'TOOL_EXECUTION', round: 1, toolName: 'add_device' })
      callbacks.onProgress({
        stage: 'TOOL_RESULT',
        round: 1,
        toolName: 'add_device',
        outcome: 'USABLE',
        successfulSteps: 1,
        failedSteps: 0,
        unconfirmedSteps: 0,
        detail: '已创建设备“客厅灯”。'
      })
      callbacks.onProgress({
        stage: 'WRITING_RESPONSE',
        successfulSteps: 1,
        failedSteps: 0,
        unconfirmedSteps: 0
      })
      callbacks.onMessage('设备已创建。')
      callbacks.onFinish?.({ turnId: args[4], executionStatus: 'COMPLETED' })
    })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('添加设备')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    const trace = wrapper.get('[data-testid="chat-execution-trace"]')
    expect(trace.findAll('li')).toHaveLength(6)
    expect(trace.text()).toContain('思考摘要')
    expect(trace.text()).toContain('当前目标是补齐客厅照明')
    expect(trace.text()).toContain('创建设备')
    expect(trace.text()).toContain('已启动工具 add_device')
    expect(trace.text()).toContain('已创建设备“客厅灯”。')
    expect(trace.text()).toContain('整理最终答复')
    expect(wrapper.text()).toContain('1 成功')
    expect(wrapper.text()).toContain('设备已创建。')
    expect(wrapper.get('.chat-execution-state').text()).toContain('已完成')
    const completedDetails = wrapper.get('details.chat-execution-trace')
    expect(completedDetails.attributes('open')).toBeUndefined()

    const completedEvents = completedDetails.get('.chat-execution-events').element as HTMLElement
    completedEvents.scrollTop = 80
    const completedDetailsElement = completedDetails.element as HTMLDetailsElement
    completedDetailsElement.open = true
    await completedDetails.trigger('toggle')
    await flushPromises()
    expect(completedEvents.scrollTop).toBe(0)

    wrapper.unmount()
  })

  it('labels an execution guard as stopped instead of completed', async () => {
    chatApi.createSession.mockResolvedValue(session)
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      const callbacks = args[2]
      callbacks.onAccepted?.()
      callbacks.onProgress({ stage: 'CONTEXT_READY' })
      callbacks.onProgress({ stage: 'PLANNING', round: 1 })
      callbacks.onProgress({ stage: 'EXECUTION_GUARD', round: 3, outcome: 'NO_PROGRESS' })
      callbacks.onMessage('重复调用已停止。')
      callbacks.onFinish?.({ turnId: args[4], executionStatus: 'PARTIAL' })
    })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('检查规则')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    const state = wrapper.get('.chat-execution-state')
    expect(state.text()).toBe('无进展，已停止')
    expect(state.classes()).toContain('is-stopped')
    expect(state.text()).not.toContain('已完成')

    wrapper.unmount()
  })

  it('shows the original objective when work resumes after confirmation', async () => {
    chatApi.createSession.mockResolvedValue(session)
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      const callbacks = args[2]
      callbacks.onAccepted?.()
      callbacks.onProgress({ stage: 'CONTEXT_READY' })
      callbacks.onProgress({
        stage: 'TASK_RESUMED',
        detail: '删除旧传感器，创建替代设备，然后运行正式验证'
      })
      callbacks.onProgress({ stage: 'WRITING_RESPONSE' })
      callbacks.onMessage('正在继续。')
      callbacks.onFinish?.({ turnId: args[4], executionStatus: 'PARTIAL' })
    })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('确认删除')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(wrapper.text()).toContain('继续原始任务')
    expect(wrapper.text()).toContain('删除旧传感器，创建替代设备，然后运行正式验证')

    wrapper.unmount()
  })

  it('awaits command confirmation and falls back to a full reconciliation', async () => {
    let resolveReconciliation!: (value: boolean) => void
    let activeTurnId = ''
    const executeCommand = vi.fn()
      .mockResolvedValueOnce(false)
      .mockImplementationOnce(() => new Promise<boolean>(resolve => {
        resolveReconciliation = resolve
      }))
    chatApi.createSession.mockResolvedValue(session)
    chatApi.getSessionHistory.mockImplementation(async () => historyPage([
      { role: 'user', content: '添加设备', turnId: activeTurnId },
      {
        role: 'assistant',
        content: '完成',
        turnId: activeTurnId,
        executionStatus: 'PARTIAL'
      }
    ]))
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      const callbacks = args[2]
      activeTurnId = args[4]
      callbacks.onAccepted?.()
      callbacks.onCommand({ type: 'REFRESH_DATA', payload: { target: 'device_list' } })
      callbacks.onMessage('完成')
      callbacks.onFinish?.({ turnId: args[4], executionStatus: 'PARTIAL' })
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('添加设备')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(executeCommand).toHaveBeenNthCalledWith(1, {
      type: 'REFRESH_DATA',
      payload: { target: 'device_list' }
    })
    expect(executeCommand).toHaveBeenNthCalledWith(2, {
      type: 'REFRESH_DATA',
      payload: { target: 'board_state' }
    })
    expect(chatStore.state.streaming).toBe(true)

    resolveReconciliation(true)
    await flushPromises()

    expect(chatStore.state.streaming).toBe(false)
    expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
    wrapper.unmount()
  })

  it('keeps interactions locked until a failed reconciliation is retried successfully', async () => {
    let activeTurnId = ''
    const executeCommand = vi.fn()
      .mockResolvedValueOnce(false)
      .mockResolvedValueOnce(false)
      .mockResolvedValueOnce(true)
    chatApi.createSession.mockResolvedValue(session)
    chatApi.getSessionHistory.mockImplementation(async () => historyPage([
      { role: 'user', content: '修改规则', turnId: activeTurnId },
      {
        role: 'assistant',
        content: '已处理',
        turnId: activeTurnId,
        executionStatus: 'PARTIAL'
      }
    ]))
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      const callbacks = args[2]
      activeTurnId = args[4]
      callbacks.onAccepted?.()
      callbacks.onCommand({ type: 'REFRESH_DATA', payload: { target: 'rule_list' } })
      callbacks.onMessage('已处理')
      callbacks.onFinish?.({ turnId: args[4], executionStatus: 'PARTIAL' })
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('修改规则')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(wrapper.get('[data-testid="chat-reconciliation-required"]').text())
      .toContain('需要重新同步当前状态')
    expect(wrapper.get('[data-testid="chat-send"]').attributes('disabled')).toBeDefined()
    expect(chatStore.state.streaming).toBe(true)

    await wrapper.get('[data-testid="chat-reconciliation-retry"]').trigger('click')
    await flushPromises()

    expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
    expect(chatStore.state.streaming).toBe(false)
    wrapper.unmount()
  })

  it('settles the active backend request before allowing logout', async () => {
    const executeCommand = vi.fn().mockResolvedValue(true)
    let activeTurnId = ''
    chatApi.createSession.mockResolvedValue(session)
    chatApi.getSessionHistory.mockImplementation(async () => historyPage([
      { role: 'user', content: '运行工具', turnId: activeTurnId },
      {
        role: 'assistant',
        content: '请求已停止。',
        turnId: activeTurnId,
        executionStatus: 'STOPPED'
      }
    ]))
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      activeTurnId = args[4]
      args[2].onAccepted?.()
      const controller = args[3] as AbortController
      return new Promise<void>(resolve => {
        controller.signal.addEventListener('abort', () => resolve(), { once: true })
      })
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('运行工具')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    const result = await (wrapper.vm as any).prepareForLogout()
    await flushPromises()

    expect(result).toBe('ready')
    expect(chatApi.getSessionActivity).toHaveBeenCalledWith(
      'session-1',
      expect.objectContaining({ signal: expect.any(AbortSignal) })
    )
    expect(executeCommand).toHaveBeenCalledWith({
      type: 'REFRESH_DATA',
      payload: { target: 'board_state' }
    })
    wrapper.unmount()
  })
})

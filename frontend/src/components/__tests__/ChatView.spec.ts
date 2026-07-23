// @vitest-environment jsdom
import { flushPromises, mount } from '@vue/test-utils'
import { ElMessage } from 'element-plus'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

import { i18n } from '@/assets/i18n'
import { useChatStore } from '@/stores/chat'
import { useAuth } from '@/stores/auth'

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

vi.mock('@/api/chat', () => ({
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
  ...chatApi
}))

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
    chatApi.getSessionHistory.mockResolvedValue([])
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
    chatApi.getSessionHistory.mockResolvedValue([
      { role: 'assistant', content: 'Alice 的私密消息' }
    ])
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
      .mockResolvedValueOnce([{ role: 'assistant', content: '已恢复的历史消息' }])
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
    chatApi.sendStreamChat.mockResolvedValue(undefined)
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
    const terminalHistory = [
      { role: 'user', content: '运行验证', turnId: 'remote-turn' },
      {
        role: 'assistant',
        content: '用户已停止。',
        turnId: 'remote-turn',
        executionStatus: 'STOPPED'
      }
    ]
    chatApi.getSessionList
      .mockResolvedValueOnce([{ ...session, active: true }])
      .mockResolvedValue([{ ...session, active: false }])
    chatApi.getSessionActivity
      .mockResolvedValueOnce({ sessionId: 'session-1', active: true })
      .mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.getSessionHistory
      .mockResolvedValueOnce([])
      .mockResolvedValue(terminalHistory)
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-stop"]').trigger('click')
    await flushPromises()

    expect(chatApi.requestSessionStop).toHaveBeenCalledWith('session-1')
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
    const terminalHistory = [
      { role: 'user', content: '检查场景', turnId: 'remote-turn' },
      {
        role: 'assistant',
        content: '后台检查已完成。',
        turnId: 'remote-turn',
        executionStatus: 'COMPLETED'
      }
    ]
    chatApi.getSessionList
      .mockResolvedValueOnce([{ ...session, active: true }])
      .mockResolvedValue([{ ...session, active: false }])
    chatApi.getSessionActivity
      .mockResolvedValueOnce({ sessionId: 'session-1', active: true })
      .mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.getSessionHistory
      .mockResolvedValueOnce([])
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

  it('reloads terminal history even when Board reconciliation must be retried', async () => {
    vi.useFakeTimers()
    const terminalHistory = [
      { role: 'user', content: '检查场景', turnId: 'remote-turn' },
      {
        role: 'assistant',
        content: '后台结果已持久化。',
        turnId: 'remote-turn',
        executionStatus: 'COMPLETED'
      }
    ]
    chatApi.getSessionList
      .mockResolvedValueOnce([{ ...session, active: true }])
      .mockResolvedValue([{ ...session, active: false }])
    chatApi.getSessionActivity
      .mockResolvedValueOnce({ sessionId: 'session-1', active: true })
      .mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.getSessionHistory
      .mockResolvedValueOnce([])
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
    chatApi.getSessionHistory.mockResolvedValue([
      { role: 'user', content: '运行验证' },
      {
        role: 'assistant',
        content: '连接在任务完成前中断。',
        executionStatus: 'DISCONNECTED',
        executionElapsedSeconds: 4
      }
    ])
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

  it('distinguishes no-tool replies and refuses unproven completed history', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue([
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
        content: '缺少工具证据的损坏完成记录。',
        executionStatus: 'COMPLETED',
        executionElapsedSeconds: 3
      },
      { role: 'user', content: '读取当前完成记录' },
      {
        role: 'assistant',
        content: '已有可验证的完成记录。',
        executionStatus: 'COMPLETED',
        executionElapsedSeconds: 3,
        executionTrace: [{ stage: 'TOOL_RESULT', outcome: 'USABLE' }]
      }
    ])
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()

    const statuses = wrapper.findAll('.chat-execution-state')
    expect(statuses).toHaveLength(5)
    expect(statuses[0].text()).toContain('未执行平台工具')
    expect(statuses[0].text()).not.toContain('已完成')
    expect(statuses[1].text()).toContain('部分完成')
    expect(statuses[1].text()).not.toContain('未执行平台工具')
    expect(statuses[2].text()).toContain('部分完成')
    expect(statuses[2].text()).not.toContain('未执行平台工具')
    expect(statuses[3].text()).toContain('终态未确认')
    expect(statuses[3].text()).not.toContain('已完成')
    expect(statuses[4].text()).toContain('已完成')

    wrapper.unmount()
  })

  it('labels a reviewable incomplete tool result as partial rather than successful', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue([
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
    ])
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

  it('never renders an unknown terminal status as completed', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue([
      { role: 'user', content: '检查未来状态' },
      {
        role: 'assistant',
        content: '该状态来自更新后的服务端。',
        executionStatus: 'FUTURE_STATUS'
      }
    ])
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()

    expect(wrapper.get('[data-testid="chat-terminal-status"]').text()).toContain('终态未确认')
    expect(wrapper.get('[data-testid="chat-terminal-status"]').text()).not.toContain('已完成')

    wrapper.unmount()
  })

  it('shows user stop and confirmation-pending outcomes as distinct states', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory.mockResolvedValue([
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
    ])
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
    chatApi.getSessionHistory.mockResolvedValue([
      { role: 'user', content: '运行验证' },
      {
        role: 'assistant',
        content: '用户已停止。',
        executionStatus: 'STOPPED',
        executionTrace: [{ stage: 'EXECUTION_GUARD', outcome: 'NO_PROGRESS' }]
      }
    ])
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
    const stopOrder: string[] = []
    chatApi.createSession.mockResolvedValue(session)
    chatApi.requestSessionStop.mockImplementation(async () => {
      stopOrder.push('stop-request')
    })
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      streamSignal = args[3]?.signal
      activeTurnId = args[4]
      return new Promise<void>(resolve => {
        streamSignal?.addEventListener('abort', () => {
          stopOrder.push('transport-abort')
          resolve()
        }, { once: true })
      })
    })
    chatApi.getSessionHistory.mockImplementation(async () => [
      { role: 'user', content: '运行验证', turnId: activeTurnId },
      {
        role: 'assistant',
        content: '用户已停止。',
        turnId: activeTurnId,
        executionStatus: 'STOPPED'
      }
    ])
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('运行验证')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-stop"]').trigger('click')
    await flushPromises()

    expect(chatApi.requestSessionStop).toHaveBeenCalledWith('session-1')
    expect(streamSignal?.aborted).toBe(true)
    expect(stopOrder).toEqual(['stop-request', 'transport-abort'])
    expect(clearIntervalSpy).toHaveBeenCalled()

    wrapper.unmount()
    clearIntervalSpy.mockRestore()
  })

  it('keeps the current local turn when history only contains an older terminal reply', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.getSessionHistory
      .mockResolvedValueOnce([])
      .mockResolvedValueOnce([
        { role: 'user', content: '旧问题', turnId: 'old-turn' },
        {
          role: 'assistant',
          content: '旧回答',
          turnId: 'old-turn',
          executionStatus: 'COMPLETED'
        }
      ])
    chatApi.sendStreamChat.mockResolvedValue(undefined)
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

  it('removes an optimistic turn and restores the draft when the server rejects before streaming', async () => {
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.sendStreamChat.mockRejectedValue(new Error('busy'))
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
        messages: [
          { id: 2, role: 'user', content: '较新的问题' },
          { id: 3, role: 'assistant', content: '较新的回答' }
        ],
        nextBeforeId: 2,
        hasMore: true
      })
      .mockResolvedValueOnce({
        messages: [{ id: 1, role: 'user', content: '最早的问题' }],
        nextBeforeId: null,
        hasMore: false
      })
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
    chatApi.sendStreamChat.mockImplementation(() => new Promise<void>(resolve => {
      finishStream = resolve
    }))
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
      callbacks.onFinish?.()
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
    expect(wrapper.get('.chat-execution-state').text()).toContain('终态未确认')
    expect(wrapper.get('.chat-execution-state').text()).not.toContain('已完成')
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
      callbacks.onProgress({ stage: 'CONTEXT_READY' })
      callbacks.onProgress({ stage: 'PLANNING', round: 1 })
      callbacks.onProgress({ stage: 'EXECUTION_GUARD', round: 3, outcome: 'NO_PROGRESS' })
      callbacks.onMessage('重复调用已停止。')
      callbacks.onFinish?.()
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
      callbacks.onProgress({ stage: 'CONTEXT_READY' })
      callbacks.onProgress({
        stage: 'TASK_RESUMED',
        detail: '删除旧传感器，创建替代设备，然后运行正式验证'
      })
      callbacks.onProgress({ stage: 'WRITING_RESPONSE' })
      callbacks.onMessage('正在继续。')
      callbacks.onFinish?.()
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
    const executeCommand = vi.fn()
      .mockResolvedValueOnce(false)
      .mockImplementationOnce(() => new Promise<boolean>(resolve => {
        resolveReconciliation = resolve
      }))
    chatApi.createSession.mockResolvedValue(session)
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      const callbacks = args[2]
      callbacks.onCommand({ type: 'REFRESH_DATA', payload: { target: 'device_list' } })
      callbacks.onMessage('完成')
      callbacks.onFinish?.()
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
    const executeCommand = vi.fn()
      .mockResolvedValueOnce(false)
      .mockResolvedValueOnce(false)
      .mockResolvedValueOnce(true)
    chatApi.createSession.mockResolvedValue(session)
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      const callbacks = args[2]
      callbacks.onCommand({ type: 'REFRESH_DATA', payload: { target: 'rule_list' } })
      callbacks.onMessage('已处理')
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
    chatApi.createSession.mockResolvedValue(session)
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
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

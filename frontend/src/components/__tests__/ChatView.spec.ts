// @vitest-environment jsdom
import { flushPromises, mount } from '@vue/test-utils'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

import { i18n } from '@/assets/i18n'
import { useChatStore } from '@/stores/chat'

const chatApi = vi.hoisted(() => ({
  createSession: vi.fn(),
  deleteSession: vi.fn(),
  getSessionActivity: vi.fn(),
  getSessionHistory: vi.fn(),
  getSessionList: vi.fn(),
  sendStreamChat: vi.fn()
}))

vi.mock('element-plus/es/components/message/style/css', () => ({}))
vi.mock('element-plus/es/components/message-box/style/css', () => ({}))

vi.mock('@/api/chat', () => ({
  ChatStreamError: class ChatStreamError extends Error {
    readonly serverFrame = false
  },
  ...chatApi
}))

import ChatView from '../ChatView.vue'

const chatStore = useChatStore()
const session = {
  id: 'session-1',
  userId: 1,
  title: '玄关场景检查',
  updatedAt: '2026-07-13T12:00:00Z'
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
    chatStore.closeChat()
    chatStore.setStreaming(false)
    i18n.global.locale.value = 'zh-CN'
    chatApi.getSessionList.mockResolvedValue([])
    chatApi.getSessionActivity.mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.getSessionHistory.mockResolvedValue([])
    chatApi.deleteSession.mockResolvedValue(undefined)
  })

  afterEach(() => {
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

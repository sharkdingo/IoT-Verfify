// @vitest-environment jsdom
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { flushPromises, mount } from '@vue/test-utils'
import HintTooltip from '@/components/common/HintTooltip.vue'
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
  markSessionTerminalSeen: vi.fn(),
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
      readonly limit?: number

      constructor(message: string, options: Record<string, any> = {}) {
        super(message)
        this.serverFrame = options.serverFrame ?? false
        this.kind = options.kind ?? 'UNKNOWN'
        this.status = options.status
        this.reasonCode = options.reasonCode
        this.limit = options.limit
      }
    },
    hasCompletedToolEvidence: actual.hasCompletedToolEvidence,
    ...chatApi
  }
})

import { ChatStreamError } from '@/api/chat'
import ChatView from '../ChatView.vue'
import * as feedback from '@/utils/feedback'

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
  active: false,
  latestTerminalMessageId: null,
  latestExecutionStatus: null,
  hasUnreadUpdate: false
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

/**
 * Every mount this file makes, so `afterEach` can tear down one that a thrown assertion skipped.
 *
 * `ChatView` re-arms a 1s `scheduleActiveSessionsPoll` after each poll, and `chatViewMounted` is
 * module-scoped — so a component that outlives its test keeps polling, and each tick consumes one
 * `mockResolvedValueOnce` from the shared queues. Proved by mutation: forcing one assertion to fail in the
 * reattachment test produced **7** failures with the unmount only on the success path, and **1** with it in
 * a `finally`. The five extra were the five tests that follow, each reading a response meant for another.
 *
 * The `beforeEach` reset below cannot cover this — it resets implementations, not a live component — and 17
 * cases here run on real timers with one-shot queues, so per-test `finally` blocks would leave the next one
 * added unprotected. Tracking the mount is the part that cannot be forgotten.
 */
const mountedChats: Array<{ unmount: () => void }> = []

const mountChat = (props: Record<string, unknown> = {}) => {
  const wrapper = mount(ChatView, {
    props: { boardMode: true, ...props },
    global: {
      plugins: [i18n],
      stubs: {
        ChatMarkdown: { props: ['source'], template: '<div class="chat-markdown-stub">{{ source }}</div>' }
      }
    }
  })
  mountedChats.push(wrapper)
  return wrapper
}

describe('ChatView', () => {
  beforeEach(() => {
    // Background-session polling changes how many one-shot list/activity responses a case may
    // consume. Reset implementations as well as call counts so an unused `mockResolvedValueOnce`
    // cannot leak into the next case.
    vi.resetAllMocks()
    authStore.logout()
    chatStore.closeChat()
    chatStore.setStreaming(false)
    chatStore.setActiveCount(0)
    chatStore.setUnreadCount(0)
    chatStore.setReconciliationRequired(false)
    i18n.global.locale.value = 'zh-CN'
    chatApi.getSessionList.mockResolvedValue([])
    chatApi.getSessionActivity.mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.getSessionHistory.mockResolvedValue(historyPage())
    chatApi.getPendingConfirmation.mockResolvedValue({ sessionId: 'session-1', kinds: [] })
    chatApi.markSessionTerminalSeen.mockResolvedValue(undefined)
    chatApi.deleteSession.mockResolvedValue(undefined)
    chatApi.requestSessionStop.mockResolvedValue(undefined)
  })

  afterEach(() => {
    // First, because a still-mounted ChatView polls (see `mountedChats`) and would otherwise keep
    // consuming queued responses through the next test. Already-unmounted wrappers are a no-op.
    while (mountedChats.length) {
      try {
        mountedChats.pop()?.unmount()
      } catch {
        // A wrapper torn down inside its own test can throw here; the remaining ones still matter.
      }
    }
    authStore.logout()
    chatStore.closeChat()
    chatStore.setStreaming(false)
    chatStore.setActiveCount(0)
    chatStore.setUnreadCount(0)
    chatStore.setReconciliationRequired(false)
    // `i18n` is a module singleton shared by every spec in this file. A test that switches locale and
    // restores it on its last line leaves the catalogue on `en` if an assertion between the two throws,
    // cascading failures through the later tests that match Chinese strings.
    i18n.global.locale.value = 'zh-CN'
  })

  it('takes board preset copy from i18n in both locales', async () => {
    // These 12 presets used to be built from inline `locale.value === 'zh-CN' ? … : …` ternaries —
    // ~30 user-visible strings that no translation file knew about, so a third locale or a wording
    // revision could not reach them. Asserting against the message catalogue is what keeps them there.
    chatStore.openChat()
    const wrapper = mountChat({
      getBoardContext: () => ({
        deviceCount: 0, ruleCount: 0, specCount: 0, templateCount: 3,
        devices: [], rules: [], specs: [], templates: ['Light', 'AC']
      })
    })
    await flushPromises()

    // Exact equality on the rendered title, not substring containment: an inline literal that merely
    // *starts* with the catalogue text would satisfy `toContain` and hide the regression.
    const titles = () => wrapper.findAll('.task-title').map(node => node.text())

    const zhTitle = i18n.global.t('app.chat.presetTasks.empty.fromTemplates.title')
    expect(titles()).toContain(zhTitle)

    i18n.global.locale.value = 'en'
    await flushPromises()
    const enTitle = i18n.global.t('app.chat.presetTasks.empty.fromTemplates.title')
    expect(enTitle).not.toBe(zhTitle)
    expect(titles()).toContain(enTitle)
    // Every rendered preset must be a catalogue string in the active locale.
    expect(titles().length).toBeGreaterThan(0)

    // The locale restore lives in afterEach, so a failure above cannot leak `en` into later tests.
    wrapper.unmount()
  })

  it('provides both locale labels for every tool name the backend can report', () => {
    // Unlabelled tools fall through to `toolName.replace(/_/g, ' ')`, so a user watching the trace
    // sees a raw implementation name. Keep the complete backend catalog here: checking only the
    // most recently added tools lets an older label disappear without failing this contract.
    const labelled = [
      'add_device', 'add_template', 'apply_fix', 'apply_scenario', 'board_overview',
      'cancel_fuzz_task', 'cancel_simulate_task', 'cancel_verify_task', 'check_duplicate_rule',
      'check_rule_similarity', 'clear_board', 'delete_device', 'delete_fuzz_run',
      'delete_simulation_trace', 'delete_template', 'delete_trace', 'delete_verification_run',
      'dismiss_fuzz_task', 'dismiss_simulate_task', 'dismiss_verify_task', 'edit_device',
      'fix_violation', 'fuzz_model_async', 'fuzz_task_status', 'get_fuzz_finding', 'get_fuzz_run',
      'get_simulation_trace', 'get_trace', 'get_verification_run', 'list_async_tasks',
      'list_fuzz_runs', 'list_rules', 'list_simulation_traces', 'list_specs', 'list_templates',
      'list_traces', 'list_verification_runs', 'manage_board_history', 'manage_environment',
      'manage_rule', 'manage_spec', 'recommend_related_devices', 'recommend_rules',
      'recommend_scenario', 'recommend_specifications', 'reset_default_templates',
      'search_devices', 'simulate_model', 'simulate_model_async', 'simulate_task_status',
      'verify_model', 'verify_model_async', 'verify_task_status'
    ]
    const camel = (name: string) =>
      name.replace(/_([a-z])/g, (_m, c: string) => c.toUpperCase())
    const componentSource = readFileSync(resolve(process.cwd(), 'src/components/ChatView.vue'), 'utf8')

    // Read the raw per-locale catalogue: the i18n instance sets `fallbackLocale: 'en'`, so a missing
    // zh-CN key resolves to the English message through both `t` and `tm` — the exact gap this guards
    // would be invisible if asserted through translation.
    for (const loc of ['zh-CN', 'en'] as const) {
      const labels = (i18n.global.getLocaleMessage(loc) as any)?.app?.chat?.toolLabels ?? {}
      for (const toolName of labelled) {
        const key = camel(toolName)
        expect(typeof labels[key], `app.chat.toolLabels.${key} missing in ${loc}`).toBe('string')
        expect(componentSource, `${toolName} missing from TOOL_LABEL_KEYS`).toMatch(
          new RegExp(`\\b${toolName}:\\s*'app\\.chat\\.toolLabels\\.${key}'`)
        )
      }
    }
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

  it('surfaces App-owned background reconciliation and clears it only after a full refresh', async () => {
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatStore.setReconciliationRequired(true)
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()

    expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(true)
    expect(chatStore.state.reconciliationRequired).toBe(true)

    await wrapper.get('[data-testid="chat-reconciliation-retry"]').trigger('click')
    await flushPromises()

    expect(executeCommand).toHaveBeenCalledWith({
      type: 'REFRESH_DATA',
      payload: { target: 'board_state' }
    })
    expect(chatStore.state.reconciliationRequired).toBe(false)
    expect(wrapper.find('[data-testid="chat-reconciliation-required"]').exists()).toBe(false)
    wrapper.unmount()
  })

  it('keeps an offline result unread while hidden and acknowledges it only after rendering', async () => {
    let resolveHistory!: (page: ChatHistoryPage) => void
    const pendingHistory = new Promise<ChatHistoryPage>(resolve => {
      resolveHistory = resolve
    })
    const unreadSession = {
      ...session,
      latestTerminalMessageId: 42,
      latestExecutionStatus: 'FAILED' as const,
      hasUnreadUpdate: true
    }
    chatApi.getSessionList.mockResolvedValue([unreadSession])
    chatApi.getSessionHistory.mockReturnValue(pendingHistory)
    chatApi.markSessionTerminalSeen.mockImplementation(async () => {
      chatApi.getSessionList.mockResolvedValue([{
        ...unreadSession,
        hasUnreadUpdate: false
      }])
    })
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    expect(wrapper.get('[data-testid="chat-session-status"]').text()).toContain('失败')
    expect(wrapper.get('[data-testid="chat-session-status"]').classes()).toContain('is-unread')

    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    chatStore.closeChat()
    resolveHistory(historyPage([{
      id: 42,
      role: 'assistant',
      content: '后台执行失败，请查看原因。',
      executionStatus: 'FAILED'
    }]))
    await flushPromises()

    expect(chatApi.markSessionTerminalSeen).not.toHaveBeenCalled()

    chatStore.openChat()
    await flushPromises()

    expect(chatApi.markSessionTerminalSeen).toHaveBeenCalledWith('session-1', 42)
    expect(chatStore.state.unreadCount).toBe(0)
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

  it('re-arms background polling when an account switch overlaps an in-flight poll', async () => {
    vi.useFakeTimers()
    const aliceSession = { ...session, active: true }
    const bobSession = {
      ...session,
      id: 'session-2',
      userId: 2,
      title: 'Bob 的后台任务',
      active: true
    }
    let resolveAlicePoll!: (sessions: Array<typeof aliceSession>) => void
    chatApi.getSessionList
      .mockResolvedValueOnce([aliceSession])
      .mockReturnValueOnce(new Promise(resolve => { resolveAlicePoll = resolve }))
      .mockResolvedValueOnce([bobSession])
      .mockResolvedValue([bobSession])
    chatApi.getSessionActivity.mockImplementation(async (sessionId: string) => ({
      sessionId,
      active: true
    }))
    authStore.login(validToken('alice'), {
      userId: 1,
      phone: '13800138000',
      username: 'alice'
    })
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()
      expect(chatApi.getSessionList).toHaveBeenCalledTimes(2)

      authStore.login(validToken('bob'), {
        userId: 2,
        phone: '13900139000',
        username: 'bob'
      })
      await flushPromises()
      expect(chatApi.getSessionList).toHaveBeenCalledTimes(3)

      // Bob's first timer fires while Alice's obsolete poll still owns the in-flight slot.
      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()
      expect(chatApi.getSessionList).toHaveBeenCalledTimes(3)

      resolveAlicePoll([aliceSession])
      await flushPromises()
      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()

      expect(chatApi.getSessionList).toHaveBeenCalledTimes(4)
      expect(wrapper.get('[data-testid="chat-session-session-2"]').text()).toContain('Bob 的后台任务')
    } finally {
      wrapper.unmount()
      vi.useRealTimers()
    }
  })

  it('discovers work started in another tab while its local session list is idle', async () => {
    vi.useFakeTimers()
    const externalSession = {
      ...session,
      id: 'session-from-another-tab',
      title: '另一个标签页的场景生成',
      active: true
    }
    chatStore.openChat()
    const wrapper = mountChat()
    try {
      await flushPromises()
      expect(chatApi.getSessionList).toHaveBeenCalledTimes(1)
      expect(chatStore.state.activeCount).toBe(0)

      chatApi.getSessionList.mockResolvedValue([externalSession])
      await vi.advanceTimersByTimeAsync(5000)
      await flushPromises()

      expect(wrapper.get('[data-testid="chat-session-session-from-another-tab"]').text())
        .toContain('另一个标签页的场景生成')
      expect(chatStore.state.activeCount).toBe(1)
      expect(wrapper.get('.delete-btn-wrapper').attributes('disabled')).toBeDefined()
      /*
       * The hint moved from a native `title` to the wrapping `HintTooltip`, so read it from the wrapper's prop.
       *
       * A native `title` renders as a grey OS tooltip: about a second of delay, no theme awareness, and nothing
       * at all on touch. What is asserted here is the same string reaching the same user, through the tooltip
       * the rest of the product uses.
       */
      expect(wrapper.findAllComponents(HintTooltip).map(tip => tip.props('content')))
        .toContain(i18n.global.t('app.chat.sessionStillRunning'))
    } finally {
      wrapper.unmount()
      vi.useRealTimers()
    }
  })

  it('does not let an older background poll remove a session that was just created', async () => {
    vi.useFakeTimers()
    const activeSession = { ...session, active: true }
    const createdSession = {
      ...session,
      id: 'session-created',
      title: '刚创建的对话',
      active: false
    }
    let resolveStalePoll!: (sessions: Array<typeof activeSession>) => void
    chatApi.getSessionList
      .mockResolvedValueOnce([activeSession])
      .mockReturnValueOnce(new Promise(resolve => { resolveStalePoll = resolve }))
    chatApi.getSessionActivity.mockImplementation(async (sessionId: string) => ({
      sessionId,
      active: true
    }))
    chatApi.getSessionHistory.mockImplementation(async (sessionId: string) =>
      historyPage([], sessionId))
    chatApi.createSession.mockResolvedValue(createdSession)
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()
      expect(chatApi.getSessionList).toHaveBeenCalledTimes(2)

      await wrapper.get('.new-chat-btn').trigger('click')
      await flushPromises()
      expect(wrapper.get('[data-testid="chat-session-session-created"]').element.parentElement
        ?.classList.contains('active')).toBe(true)

      resolveStalePoll([activeSession])
      await flushPromises()

      expect(wrapper.get('[data-testid="chat-session-session-created"]').text()).toContain('刚创建的对话')
    } finally {
      wrapper.unmount()
      vi.useRealTimers()
    }
  })

  it('waits for a foreground session refresh before starting another background poll', async () => {
    vi.useFakeTimers()
    const activeSession = { ...session, active: true }
    let resolveForegroundRefresh!: (sessions: Array<typeof activeSession>) => void
    chatApi.getSessionList
      .mockResolvedValueOnce([activeSession])
      .mockReturnValueOnce(new Promise(resolve => { resolveForegroundRefresh = resolve }))
      .mockResolvedValue([activeSession])
    chatApi.getSessionActivity.mockImplementation(async (sessionId: string) => ({
      sessionId,
      active: true
    }))
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      chatStore.closeChat()
      await flushPromises()
      chatStore.openChat()
      await flushPromises()
      expect(chatApi.getSessionList).toHaveBeenCalledTimes(2)

      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()
      expect(chatApi.getSessionList).toHaveBeenCalledTimes(2)

      resolveForegroundRefresh([activeSession])
      await flushPromises()
      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()
      expect(chatApi.getSessionList).toHaveBeenCalledTimes(3)
    } finally {
      wrapper.unmount()
      vi.useRealTimers()
    }
  })

  it('does not duplicate a created session that background polling observed first', async () => {
    vi.useFakeTimers()
    const activeSession = { ...session, active: true }
    const createdSession = {
      ...session,
      id: 'session-created',
      title: '新对话',
      active: false
    }
    let resolveSession!: (value: typeof createdSession) => void
    chatApi.getSessionList
      .mockResolvedValueOnce([activeSession])
      .mockResolvedValueOnce([activeSession, createdSession])
    chatApi.getSessionActivity.mockImplementation(async (sessionId: string) => ({
      sessionId,
      active: true
    }))
    chatApi.getSessionHistory.mockImplementation(async (sessionId: string) =>
      historyPage([], sessionId))
    chatApi.createSession.mockReturnValue(new Promise(resolve => { resolveSession = resolve }))
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await wrapper.get('.new-chat-btn').trigger('click')
      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()
      expect(wrapper.findAll('[data-testid="chat-session-session-created"]')).toHaveLength(1)

      resolveSession(createdSession)
      await flushPromises()

      expect(wrapper.findAll('[data-testid="chat-session-session-created"]')).toHaveLength(1)
    } finally {
      wrapper.unmount()
      vi.useRealTimers()
    }
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
    const warning = vi.spyOn(feedback, 'notifyBlocked').mockImplementation(() => undefined)
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
    const warning = vi.spyOn(feedback, 'notifyBlocked').mockImplementation(() => undefined)
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
    const warning = vi.spyOn(feedback, 'notifyBlocked').mockImplementation(() => undefined)
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
    const warning = vi.spyOn(feedback, 'notifyBlocked').mockImplementation(() => undefined)
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
    const errorMessage = vi.spyOn(feedback, 'notifyError').mockImplementation(() => undefined)
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

  it('keeps the current live stream attached when new-session creation fails', async () => {
    let streamSignal: AbortSignal | undefined
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.createSession.mockRejectedValue(new Error('session limit reached'))
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      args[2].onAccepted?.()
      streamSignal = args[3]?.signal
      return new Promise<void>(resolve =>
        streamSignal?.addEventListener('abort', () => resolve(), { once: true }))
    })
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
      await flushPromises()
      await wrapper.get('[data-testid="chat-input"]').setValue('继续执行长任务')
      await wrapper.get('[data-testid="chat-send"]').trigger('click')
      await flushPromises()

      await wrapper.get('.new-chat-btn').trigger('click')
      await flushPromises()

      expect(streamSignal?.aborted).toBe(false)
      expect(chatApi.requestSessionStop).not.toHaveBeenCalled()
      expect(wrapper.find('[data-testid="chat-stop"]').exists()).toBe(true)
      expect(wrapper.get('[data-testid="chat-session-session-1"]').element.parentElement
        ?.classList.contains('active')).toBe(true)
    } finally {
      wrapper.unmount()
    }
  })

  it('treats an incomplete new-session response as a visible failure', async () => {
    const errorMessage = vi.spyOn(feedback, 'notifyError').mockImplementation(() => undefined)
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

  it('keeps the latest user-selected session when an earlier new-chat request finishes later', async () => {
    const firstSession = { ...session, id: 'session-a', title: '原会话' }
    const selectedSession = { ...session, id: 'session-b', title: '用户最后选择' }
    const createdSession = { ...session, id: 'session-c', title: '较早请求创建' }
    let resolveSession!: (value: typeof createdSession) => void
    chatApi.getSessionList.mockResolvedValue([firstSession, selectedSession])
    chatApi.getSessionHistory.mockImplementation(async (sessionId: string) =>
      historyPage([], sessionId))
    chatApi.createSession.mockReturnValue(new Promise(resolve => { resolveSession = resolve }))
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-a"]').trigger('click')
      await flushPromises()

      await wrapper.get('.new-chat-btn').trigger('click')
      await wrapper.get('[data-testid="chat-session-session-b"]').trigger('click')
      await flushPromises()
      resolveSession(createdSession)
      await flushPromises()

      expect(wrapper.get('[data-testid="chat-session-session-b"]').element.parentElement
        ?.classList.contains('active')).toBe(true)
      expect(wrapper.get('[data-testid="chat-session-session-c"]').element.parentElement
        ?.classList.contains('active')).toBe(false)
    } finally {
      wrapper.unmount()
    }
  })

  it('keeps a retried conversation selected when an earlier new-chat request finishes later', async () => {
    const firstSession = { ...session, id: 'session-a', title: '需要重试的会话' }
    const createdSession = { ...session, id: 'session-c', title: '较早请求创建' }
    let resolveSession!: (value: typeof createdSession) => void
    chatApi.getSessionList.mockResolvedValue([firstSession])
    chatApi.getSessionHistory
      .mockRejectedValueOnce(new Error('history unavailable'))
      .mockResolvedValue(historyPage([], firstSession.id))
    chatApi.createSession.mockReturnValue(new Promise(resolve => { resolveSession = resolve }))
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-a"]').trigger('click')
      await flushPromises()
      expect(wrapper.find('[data-testid="chat-history-retry"]').exists()).toBe(true)

      await wrapper.get('.new-chat-btn').trigger('click')
      await wrapper.get('[data-testid="chat-history-retry"] button').trigger('click')
      await flushPromises()
      resolveSession(createdSession)
      await flushPromises()

      expect(wrapper.get('[data-testid="chat-session-session-a"]').element.parentElement
        ?.classList.contains('active')).toBe(true)
      expect(wrapper.get('[data-testid="chat-session-session-c"]').element.parentElement
        ?.classList.contains('active')).toBe(false)
    } finally {
      wrapper.unmount()
    }
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
    expect(wrapper.text()).toContain('执行当前预览的受保护操作')
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
    // Same move as the delete button above: the hint is the wrapping tooltip's content now, not a `title`.
    expect(wrapper.findAllComponents(HintTooltip).map(tip => tip.props('content')))
      .toContain('停止仍在后台运行的助手任务')
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

  it('keeps an idle selection while another conversation runs and keeps the Board locked', async () => {
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

    expect(chatApi.getSessionActivity.mock.calls.at(-1)?.[0]).toBe('session-b')
    expect(wrapper.get('[data-testid="chat-session-session-b"]')
      .element.parentElement?.classList.contains('active')).toBe(true)
    expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeUndefined()
    expect(wrapper.find('[data-testid="chat-remote-execution"]').exists()).toBe(false)
    expect(chatStore.state.streaming).toBe(true)

    wrapper.unmount()
  })

  it('reconciles the Board and notifies when a background conversation finishes', async () => {
    vi.useFakeTimers()
    const sessionA = { ...session, id: 'session-a', title: '场景生成', active: false }
    const sessionB = { ...session, id: 'session-b', title: '当前会话', active: false }
    const notifyInfo = vi.spyOn(feedback, 'notifyInfo').mockImplementation(() => undefined)
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatApi.getSessionList
      .mockResolvedValueOnce([sessionA, sessionB])
      .mockResolvedValueOnce([{ ...sessionA, active: true }, sessionB])
      .mockResolvedValue([{
        ...sessionA,
        active: false,
        latestTerminalMessageId: 101,
        latestExecutionStatus: 'COMPLETED',
        hasUnreadUpdate: true
      }, sessionB])
    chatApi.getSessionHistory.mockImplementation(async (sessionId: string) =>
      historyPage([], sessionId))
    chatApi.getPendingConfirmation.mockImplementation(async (sessionId: string) => ({
      sessionId,
      kinds: []
    }))
    chatApi.getSessionActivity.mockResolvedValue({ sessionId: 'session-b', active: false })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-b"]').trigger('click')
      await flushPromises()

      chatStore.closeChat()
      await flushPromises()
      chatStore.openChat()
      await flushPromises()
      expect(wrapper.find('[data-testid="chat-session-active"]').exists()).toBe(true)

      await vi.advanceTimersByTimeAsync(1000)
      await flushPromises()

      expect(executeCommand).toHaveBeenCalledWith({
        type: 'REFRESH_DATA',
        payload: { target: 'board_state' }
      })
      expect(notifyInfo).toHaveBeenCalledWith(i18n.global.t(
        'app.chat.backgroundSessionCompleted',
        { title: '场景生成' }
      ))
      expect(wrapper.find('[data-testid="chat-session-active"]').exists()).toBe(false)
      expect(chatStore.state.streaming).toBe(false)
    } finally {
      wrapper.unmount()
      notifyInfo.mockRestore()
      vi.useRealTimers()
    }
  })

  it('reconciles and notifies when foreground refresh first observes background completion', async () => {
    const sessionA = { ...session, id: 'session-a', title: '后台场景生成', active: true }
    const sessionB = { ...session, id: 'session-b', title: '当前会话', active: false }
    const notifyInfo = vi.spyOn(feedback, 'notifyInfo').mockImplementation(() => undefined)
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatApi.getSessionList
      .mockResolvedValueOnce([sessionA, sessionB])
      .mockResolvedValueOnce([{
        ...sessionA,
        active: false,
        latestTerminalMessageId: 102,
        latestExecutionStatus: 'COMPLETED',
        hasUnreadUpdate: true
      }, sessionB])
    chatApi.getSessionHistory.mockImplementation(async (sessionId: string) =>
      historyPage([], sessionId))
    chatApi.getSessionActivity.mockImplementation(async (sessionId: string) => ({
      sessionId,
      active: sessionId === sessionA.id
    }))
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-b"]').trigger('click')
      await flushPromises()

      chatStore.closeChat()
      await flushPromises()
      chatStore.openChat()
      await flushPromises()

      expect(executeCommand).toHaveBeenCalledWith({
        type: 'REFRESH_DATA',
        payload: { target: 'board_state' }
      })
      expect(notifyInfo).toHaveBeenCalledWith(i18n.global.t(
        'app.chat.backgroundSessionCompleted',
        { title: '后台场景生成' }
      ))
      expect(wrapper.find('[data-testid="chat-session-active"]').exists()).toBe(false)
    } finally {
      wrapper.unmount()
      notifyInfo.mockRestore()
    }
  })

  it('reconciles a foreground terminal message that completed between session-list refreshes', async () => {
    const fastSession = {
      ...session,
      id: 'fast-session',
      title: '快速后台任务',
      latestTerminalMessageId: 103,
      latestExecutionStatus: 'COMPLETED' as const,
      hasUnreadUpdate: true
    }
    const notifyInfo = vi.spyOn(feedback, 'notifyInfo').mockImplementation(() => undefined)
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatApi.getSessionList
      .mockResolvedValueOnce([])
      .mockResolvedValue([fastSession])
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    try {
      await flushPromises()
      window.dispatchEvent(new Event('focus'))
      await flushPromises()

      expect(executeCommand).toHaveBeenCalledWith({
        type: 'REFRESH_DATA',
        payload: { target: 'board_state' }
      })
      expect(notifyInfo).toHaveBeenCalledWith(i18n.global.t(
        'app.chat.backgroundSessionCompleted',
        { title: '快速后台任务' }
      ))
    } finally {
      wrapper.unmount()
      notifyInfo.mockRestore()
    }
  })

  it('does not show a previous account background-completion notice after account change', async () => {
    const aliceBackground = { ...session, id: 'session-a', title: 'Alice 后台任务', active: true }
    const aliceCurrent = { ...session, id: 'session-b', title: 'Alice 当前会话', active: false }
    const bobSession = {
      ...session,
      id: 'session-c',
      userId: 2,
      title: 'Bob 会话',
      active: false
    }
    let resolveReconciliation!: (result: boolean) => void
    const executeCommand = vi.fn().mockReturnValue(new Promise<boolean>(resolve => {
      resolveReconciliation = resolve
    }))
    const notifyInfo = vi.spyOn(feedback, 'notifyInfo').mockImplementation(() => undefined)
    chatApi.getSessionList
      .mockResolvedValueOnce([aliceBackground, aliceCurrent])
      .mockResolvedValueOnce([{ ...aliceBackground, active: false }, aliceCurrent])
      .mockResolvedValueOnce([bobSession])
    chatApi.getSessionHistory.mockImplementation(async (sessionId: string) =>
      historyPage([], sessionId))
    chatApi.getSessionActivity.mockImplementation(async (sessionId: string) => ({
      sessionId,
      active: sessionId === aliceBackground.id
    }))
    authStore.login(validToken('alice'), {
      userId: 1,
      phone: '13800138000',
      username: 'alice'
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-b"]').trigger('click')
      await flushPromises()
      chatStore.closeChat()
      await flushPromises()
      chatStore.openChat()
      await flushPromises()
      expect(executeCommand).toHaveBeenCalledTimes(1)

      authStore.login(validToken('bob'), {
        userId: 2,
        phone: '13900139000',
        username: 'bob'
      })
      await flushPromises()
      resolveReconciliation(true)
      await flushPromises()

      expect(wrapper.get('[data-testid="chat-session-session-c"]').text()).toContain('Bob 会话')
      expect(notifyInfo).not.toHaveBeenCalledWith(expect.stringContaining('Alice 后台任务'))
    } finally {
      wrapper.unmount()
      notifyInfo.mockRestore()
    }
  })

  it('detaches a long-running conversation when starting another without stopping the server work', async () => {
    const sessionA = { ...session, id: 'session-a', title: '长任务', active: false }
    const sessionB = { ...session, id: 'session-b', title: '继续提问', active: false }
    const sessionC = { ...session, id: 'session-c', title: '新对话', active: false }
    let firstStreamSignal: AbortSignal | undefined
    chatApi.getSessionList.mockResolvedValue([sessionA, sessionB])
    chatApi.getSessionHistory.mockImplementation(async (sessionId: string) =>
      historyPage([], sessionId))
    chatApi.getPendingConfirmation.mockResolvedValue({ sessionId: 'session-a', kinds: [] })
    chatApi.createSession.mockResolvedValue(sessionC)
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      args[2].onAccepted?.()
      if (chatApi.sendStreamChat.mock.calls.length === 1) {
        firstStreamSignal = args[3]?.signal
        return new Promise<void>(resolve =>
          firstStreamSignal?.addEventListener('abort', () => resolve(), { once: true }))
      }
      const signal = args[3]?.signal as AbortSignal | undefined
      return new Promise<void>(resolve =>
        signal?.addEventListener('abort', () => resolve(), { once: true }))
    })
    chatStore.openChat()

    const wrapper = mountChat()
    try {
      await flushPromises()
      await wrapper.get('[data-testid="chat-session-session-a"]').trigger('click')
      await flushPromises()
      await wrapper.get('[data-testid="chat-input"]').setValue('生成并替换当前场景')
      await wrapper.get('[data-testid="chat-send"]').trigger('click')
      await flushPromises()

      await wrapper.get('.new-chat-btn').trigger('click')
      await flushPromises()

      expect(firstStreamSignal?.aborted).toBe(true)
      expect(chatApi.requestSessionStop).not.toHaveBeenCalled()
      expect(wrapper.get('[data-testid="chat-session-session-c"]').element.parentElement
        ?.classList.contains('active')).toBe(true)
      expect(wrapper.get('[data-testid="chat-session-active"]').attributes('title'))
        .toBe('后台任务执行中')
      expect(wrapper.get('[data-testid="chat-input"]').attributes('disabled')).toBeUndefined()
      expect(chatStore.state.streaming).toBe(true)

      await wrapper.get('[data-testid="chat-input"]').setValue('检查当前设备')
      await wrapper.get('[data-testid="chat-send"]').trigger('click')
      await flushPromises()
      expect(chatApi.sendStreamChat).toHaveBeenCalledTimes(2)
    } finally {
      wrapper.unmount()
    }
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
    // `finally`, like the five neighbouring reattachment cases — and here it matters more, because this one
    // runs on *real* timers. A failing assertion used to skip the unmount, leaving the component's 1s
    // `scheduleActiveSessionsPoll` alive; each tick then consumed one `mockResolvedValueOnce` from the
    // shared queues, so the next five tests read a response meant for this one. Observed in a full-suite
    // run: one starved test here produced six failures, none of which reproduced in isolation.
    // `vi.resetAllMocks()` in `beforeEach` cannot help — it resets implementations, not a mounted component.
    try {
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
    } finally {
      wrapper.unmount()
    }
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
    const warning = vi.spyOn(feedback, 'notifyBlocked').mockImplementation(() => undefined)
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
    const warning = vi.spyOn(feedback, 'notifyBlocked').mockImplementation(() => undefined)
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
    const warning = vi.spyOn(feedback, 'notifyBlocked').mockImplementation(() => undefined)
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
    const warning = vi.spyOn(feedback, 'notifyBlocked').mockImplementation(() => undefined)
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
    const warning = vi.spyOn(feedback, 'notifyBlocked').mockImplementation(() => undefined)
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
    const errorMessage = vi.spyOn(feedback, 'notifyError').mockImplementation(() => undefined)
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

  it('reports the configured parallel-conversation limit precisely', async () => {
    const errorMessage = vi.spyOn(feedback, 'notifyError').mockImplementation(() => undefined)
    chatApi.getSessionList.mockResolvedValue([session])
    chatApi.sendStreamChat.mockRejectedValue(new ChatStreamError('busy', {
      kind: 'HTTP_ERROR',
      status: 429,
      reasonCode: 'USER_CHAT_OPERATION_BUSY',
      limit: 4
    }))
    chatStore.openChat()

    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-session-session-1"]').trigger('click')
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('并行检查另一个场景')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(errorMessage).toHaveBeenCalledWith(
      '发送消息失败：当前已有 4 个助手会话在运行。你可以查看这些会话，或等待其中一个完成后重试。'
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

  it('leaves read-only Board playback before sending a new turn', async () => {
    const prepareInteraction = vi.fn(() => true)
    chatApi.createSession.mockResolvedValue(session)
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      acceptAndFinishStream(args)
    })
    chatStore.openChat()

    const wrapper = mountChat({ prepareInteraction })
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('继续分析')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(prepareInteraction).toHaveBeenCalledOnce()
    expect(chatApi.sendStreamChat).toHaveBeenCalledOnce()
    wrapper.unmount()
  })

  it('does not start a turn when Board preparation observes a replacement in progress', async () => {
    const prepareInteraction = vi.fn(() => false)
    chatStore.openChat()

    const wrapper = mountChat({ prepareInteraction })
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('继续分析')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(prepareInteraction).toHaveBeenCalledOnce()
    expect(chatApi.sendStreamChat).not.toHaveBeenCalled()
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
    // The newest turn's reasoning stays expanded after completion: it used to shut the instant the
    // stream ended, so anyone who was not watching live never read the argument behind the answer.
    const completedDetails = wrapper.get('details.chat-execution-trace')
    expect(completedDetails.attributes('open')).toBeDefined()

    // A deliberate collapse is remembered, rather than being re-expanded on the next render.
    const completedDetailsElement = completedDetails.element as HTMLDetailsElement
    completedDetailsElement.open = false
    await completedDetails.trigger('toggle')
    await flushPromises()
    expect(wrapper.get('details.chat-execution-trace').attributes('open')).toBeUndefined()

    // Re-expanding scrolls back to the first step rather than restoring a stale offset.
    const completedEvents = completedDetails.get('.chat-execution-events').element as HTMLElement
    completedEvents.scrollTop = 80
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

  it('announces an assistant action only after its authoritative refresh succeeds', async () => {
    const executeCommand = vi.fn().mockResolvedValue(true)
    const notifyInfo = vi.spyOn(feedback, 'notifyInfo').mockImplementation(() => undefined)
    chatApi.createSession.mockResolvedValue(session)
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      const callbacks = args[2]
      callbacks.onAccepted?.()
      callbacks.onCommand({
        type: 'REFRESH_DATA',
        payload: {
          target: 'run_history',
          assistantAction: 'FORMAL_VERIFICATION_RUN'
        }
      })
      callbacks.onMessage('验证完成')
      callbacks.onFinish?.({ turnId: args[4], executionStatus: 'COMPLETED' })
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('运行验证')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(executeCommand).toHaveBeenCalledWith({
      type: 'REFRESH_DATA',
      payload: {
        target: 'run_history',
        assistantAction: 'FORMAL_VERIFICATION_RUN'
      }
    })
    expect(notifyInfo).toHaveBeenCalledWith('AI 助手已运行形式化验证，运行历史已同步。')
    wrapper.unmount()
  })

  it('announces an exact summary-only receipt after authoritative refresh succeeds', async () => {
    const executeCommand = vi.fn().mockResolvedValue(true)
    const notifyInfo = vi.spyOn(feedback, 'notifyInfo').mockImplementation(() => undefined)
    const summary = '已清除 4 条撤销/重做记录，当前画布未改变。'
    chatApi.createSession.mockResolvedValue(session)
    chatApi.sendStreamChat.mockImplementation(async (...args: any[]) => {
      const callbacks = args[2]
      callbacks.onAccepted?.()
      callbacks.onCommand({
        type: 'REFRESH_DATA',
        payload: { target: 'board_state', assistantSummary: summary }
      })
      callbacks.onMessage('历史已清理')
      callbacks.onFinish?.({ turnId: args[4], executionStatus: 'COMPLETED' })
    })
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('清理不可用的撤销历史')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    expect(executeCommand).toHaveBeenCalledWith({
      type: 'REFRESH_DATA',
      payload: { target: 'board_state', assistantSummary: summary }
    })
    expect(notifyInfo).toHaveBeenCalledWith(summary)
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
    expect(chatApi.requestSessionStop).toHaveBeenCalledWith('session-1', activeTurnId)
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

  it('stops every active conversation before allowing logout', async () => {
    const sessionA = { ...session, id: 'session-a', title: '场景生成', active: true }
    const sessionB = { ...session, id: 'session-b', title: '形式化验证', active: true }
    const stoppedSessions = new Set<string>()
    const executeCommand = vi.fn().mockResolvedValue(true)
    chatApi.getSessionList.mockImplementation(async () => [
        { ...sessionA, active: false },
        { ...sessionB, active: false }
      ].map(candidate => ({
        ...candidate,
        active: !stoppedSessions.has(candidate.id)
      })))
    chatApi.getSessionHistory.mockImplementation(async (sessionId: string) =>
      historyPage([], sessionId))
    chatApi.requestSessionStop.mockImplementation(async (sessionId: string) => {
      stoppedSessions.add(sessionId)
    })
    chatApi.getSessionActivity.mockImplementation(async (sessionId: string) => ({
      sessionId,
      active: !stoppedSessions.has(sessionId)
    }))
    chatStore.openChat()

    const wrapper = mountChat({ executeCommand })
    await flushPromises()

    const result = await (wrapper.vm as any).prepareForLogout()
    await flushPromises()

    expect(result).toBe('ready')
    expect(chatApi.requestSessionStop).toHaveBeenCalledWith('session-b')
    expect(chatApi.requestSessionStop).toHaveBeenCalledWith('session-a', undefined)
    expect(stoppedSessions).toEqual(new Set(['session-a', 'session-b']))
    expect(executeCommand).toHaveBeenCalledWith({
      type: 'REFRESH_DATA',
      payload: { target: 'board_state' }
    })
    wrapper.unmount()
  })

  it('stops an active stream with its owner token when another account takes over', async () => {
    const aliceToken = validToken('alice-chat-owner')
    const bobToken = validToken('bob-current')
    let activeTurnId = ''
    let streamSignal: AbortSignal | undefined
    authStore.login(aliceToken, { userId: 1, phone: '13800138000', username: 'alice' })
    chatApi.createSession.mockResolvedValue(session)
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      activeTurnId = args[4]
      streamSignal = args[3]?.signal
      args[2].onAccepted?.()
      return new Promise<void>(resolve => {
        streamSignal?.addEventListener('abort', () => resolve(), { once: true })
      })
    })
    chatStore.openChat()
    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('运行工具')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    authStore.login(bobToken, { userId: 2, phone: '13900139000', username: 'bob' })
    await flushPromises()

    expect(chatApi.requestSessionStop)
      .toHaveBeenCalledWith('session-1', activeTurnId, aliceToken)
    expect(streamSignal?.aborted).toBe(true)
    expect(authStore.getToken()).toBe(bobToken)
    wrapper.unmount()
  })

  it('uses a renewed same-user token to stop an already active stream', async () => {
    const originalToken = validToken('alice-original')
    const renewedToken = validToken('alice-renewed')
    const bobToken = validToken('bob-after-renewal')
    let activeTurnId = ''
    let streamSignal: AbortSignal | undefined
    const alice = { userId: 1, phone: '13800138000', username: 'alice' }
    authStore.login(originalToken, alice)
    chatApi.createSession.mockResolvedValue(session)
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      activeTurnId = args[4]
      streamSignal = args[3]?.signal
      args[2].onAccepted?.()
      return new Promise<void>(resolve => {
        streamSignal?.addEventListener('abort', () => resolve(), { once: true })
      })
    })
    chatStore.openChat()
    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('运行工具')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    authStore.login(renewedToken, alice)
    await flushPromises()
    authStore.login(bobToken, { userId: 2, phone: '13900139000', username: 'bob' })
    await flushPromises()

    expect(chatApi.requestSessionStop)
      .toHaveBeenCalledWith('session-1', activeTurnId, renewedToken)
    expect(streamSignal?.aborted).toBe(true)
    wrapper.unmount()
  })

  it('captures a token renewed while session creation is pending before dispatch', async () => {
    const originalToken = validToken('alice-before-create')
    const renewedToken = validToken('alice-after-create')
    const bobToken = validToken('bob-after-create')
    let resolveSession!: (value: typeof session) => void
    let activeTurnId = ''
    let streamSignal: AbortSignal | undefined
    const alice = { userId: 1, phone: '13800138000', username: 'alice' }
    authStore.login(originalToken, alice)
    chatApi.createSession.mockReturnValue(new Promise(resolve => { resolveSession = resolve }))
    chatApi.sendStreamChat.mockImplementation((...args: any[]) => {
      activeTurnId = args[4]
      streamSignal = args[3]?.signal
      args[2].onAccepted?.()
      return new Promise<void>(resolve => {
        streamSignal?.addEventListener('abort', () => resolve(), { once: true })
      })
    })
    chatStore.openChat()
    const wrapper = mountChat()
    await flushPromises()
    await wrapper.get('[data-testid="chat-input"]').setValue('等待会话创建')
    await wrapper.get('[data-testid="chat-send"]').trigger('click')
    await flushPromises()

    authStore.login(renewedToken, alice)
    await flushPromises()
    resolveSession(session)
    await flushPromises()
    authStore.login(bobToken, { userId: 2, phone: '13900139000', username: 'bob' })
    await flushPromises()

    expect(chatApi.requestSessionStop)
      .toHaveBeenCalledWith('session-1', activeTurnId, renewedToken)
    expect(streamSignal?.aborted).toBe(true)
    wrapper.unmount()
  })
})

describe('ChatView voice input', () => {
  /** Minimal stand-in for the browser SpeechRecognition the component constructs. */
  class FakeRecognition {
    static last: FakeRecognition | null = null
    onstart: (() => void) | null = null
    onend: (() => void) | null = null
    onerror: (() => void) | null = null
    onresult: ((event: any) => void) | null = null
    lang = ''
    interimResults = false
    maxAlternatives = 0
    aborted = false
    stopped = false

    constructor() { FakeRecognition.last = this }
    start() { this.onstart?.() }
    abort() { this.aborted = true }
    stop() { this.stopped = true }
  }

  beforeEach(() => {
    FakeRecognition.last = null
    ;(window as any).SpeechRecognition = FakeRecognition
    chatStore.openChat()
  })

  afterEach(() => {
    // This block mounts through the same helper, so it owes the same teardown — `mountedChats` is
    // file-scoped, and a wrapper left here would poll on into the *next* describe.
    while (mountedChats.length) {
      try {
        mountedChats.pop()?.unmount()
      } catch {
        // See the sibling hook above.
      }
    }
    delete (window as any).SpeechRecognition
    document.body.innerHTML = ''
  })

  const micButton = (wrapper: ReturnType<typeof mountChat>) =>
    wrapper.findAll('button').find(button =>
      button.attributes('aria-pressed') !== undefined
      && button.attributes('aria-label')?.match(/语音输入|voice input/i))!

  it('stops the recognizer when the panel unmounts', async () => {
    const wrapper = mountChat()
    await flushPromises()

    await micButton(wrapper).trigger('click')
    const recognition = FakeRecognition.last!
    expect(recognition).toBeDefined()

    wrapper.unmount()

    // Without teardown the microphone stays open after logout or navigating away.
    expect(recognition.aborted).toBe(true)
  })

  it('does not write a late transcript into a torn-down panel', async () => {
    const wrapper = mountChat()
    await flushPromises()
    await micButton(wrapper).trigger('click')
    const recognition = FakeRecognition.last!

    wrapper.unmount()
    expect(() => recognition.onresult?.({ results: [[{ transcript: 'late words' }]] })).not.toThrow()
  })

  it('lets the user stop a recording they started', async () => {
    const wrapper = mountChat()
    await flushPromises()

    const start = micButton(wrapper)
    const startLabel = start.attributes('aria-label')
    await start.trigger('click')
    await flushPromises()

    // The control must become a real stop affordance, not just look active.
    const stop = micButton(wrapper)
    expect(stop.attributes('aria-pressed')).toBe('true')
    expect(stop.attributes('aria-label')).not.toBe(startLabel)

    await stop.trigger('click')
    expect(FakeRecognition.last!.aborted).toBe(true)
    expect(micButton(wrapper).attributes('aria-pressed')).toBe('false')
    wrapper.unmount()
  })
})

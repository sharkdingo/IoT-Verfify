import { defineComponent, h, nextTick, onBeforeUnmount, onMounted } from 'vue'
import { flushPromises, mount } from '@vue/test-utils'
import { createMemoryHistory, createRouter } from 'vue-router'
import { beforeEach, describe, expect, it, vi } from 'vitest'
import App from './App.vue'
import { i18n } from '@/assets/i18n'
import { useChatStore } from '@/stores/chat'
import { useAuth } from '@/stores/auth'
import type { ChatLogoutPreparation } from '@/types/chat'

const chatApi = vi.hoisted(() => ({
  getSessionActivity: vi.fn(),
  getSessionList: vi.fn().mockResolvedValue([]),
  requestSessionStop: vi.fn()
}))

vi.mock('@/api/chat', async importOriginal => ({
  ...await importOriginal<typeof import('@/api/chat')>(),
  getSessionActivity: chatApi.getSessionActivity,
  getSessionList: chatApi.getSessionList,
  requestSessionStop: chatApi.requestSessionStop
}))

describe('App route lifecycle', () => {
  beforeEach(() => {
    chatApi.getSessionList.mockReset().mockResolvedValue([])
    chatApi.getSessionActivity.mockReset().mockResolvedValue({ sessionId: 'session-1', active: false })
    chatApi.requestSessionStop.mockReset().mockResolvedValue(undefined)
    useChatStore().setStreaming(false)
    useChatStore().setActiveCount(0)
    useChatStore().setUnreadCount(0)
    useChatStore().setReconciliationRequired(false)
  })

  it('restores persistent assistant activity before the panel is opened', async () => {
    const BoardRoute = defineComponent({ setup: () => () => h('div', 'board') })
    const router = createRouter({
      history: createMemoryHistory(),
      routes: [{ path: '/board', name: 'board', component: BoardRoute }],
    })
    const auth = useAuth()
    auth.login('alice-token', {
      userId: 1,
      phone: '13800138000',
      username: 'alice',
    })
    chatApi.getSessionList.mockResolvedValue([
      {
        id: 'finished-session',
        userId: 1,
        title: 'Finished while away',
        updatedAt: '2026-07-31T12:00:00Z',
        active: false,
        latestTerminalMessageId: 11,
        latestExecutionStatus: 'COMPLETED',
        hasUnreadUpdate: true
      },
      {
        id: 'running-session',
        userId: 1,
        title: 'Still running',
        updatedAt: '2026-07-31T12:01:00Z',
        active: true,
        latestTerminalMessageId: null,
        latestExecutionStatus: null,
        hasUnreadUpdate: false
      }
    ])
    const store = useChatStore()
    store.closeChat()
    await router.push('/board')
    await router.isReady()

    const wrapper = mount(App, { global: { plugins: [router, i18n] } })
    await flushPromises()

    expect(store.state.visible).toBe(false)
    expect(store.state.activeCount).toBe(1)
    expect(store.state.unreadCount).toBe(1)
    expect(store.state.streaming).toBe(false)
    wrapper.unmount()
    auth.logout()
  })

  it('stops authoritative assistant work before logout when the chat panel was never mounted', async () => {
    let prepareForLogout!: () => Promise<ChatLogoutPreparation>
    const refreshAllBoardState = vi.fn().mockResolvedValue(true)
    const BoardRoute = defineComponent({
      props: { prepareChatForLogout: Function },
      setup(props, { expose }) {
        prepareForLogout = props.prepareChatForLogout as () => Promise<ChatLogoutPreparation>
        expose({ refreshAllBoardState })
        return () => h('div', 'board')
      }
    })
    const router = createRouter({
      history: createMemoryHistory(),
      routes: [{ path: '/board', name: 'board', component: BoardRoute }],
    })
    const auth = useAuth()
    auth.login('alice-token', {
      userId: 1,
      phone: '13800138000',
      username: 'alice',
    })
    const activeSession = {
      id: 'session-from-another-tab',
      userId: 1,
      title: 'Scene generation',
      updatedAt: '2026-08-01T12:00:00Z',
      active: true,
      latestTerminalMessageId: null,
      latestExecutionStatus: null,
      hasUnreadUpdate: false
    }
    chatApi.getSessionList.mockResolvedValue([activeSession])
    chatApi.getSessionActivity.mockResolvedValue({
      sessionId: activeSession.id,
      active: false
    })
    const store = useChatStore()
    store.closeChat()
    await router.push('/board')
    await router.isReady()

    const wrapper = mount(App, { global: { plugins: [router, i18n] } })
    await flushPromises()

    await expect(prepareForLogout()).resolves.toBe('ready')
    expect(chatApi.requestSessionStop).toHaveBeenCalledWith(
      activeSession.id, undefined, 'alice-token')
    expect(chatApi.getSessionActivity).toHaveBeenCalledWith(activeSession.id)
    expect(refreshAllBoardState).toHaveBeenCalledOnce()

    wrapper.unmount()
    auth.logout()
  })

  it('reconciles the Board when a hidden observer sees a background session finish', async () => {
    const refreshAllBoardState = vi.fn().mockResolvedValue(true)
    const BoardRoute = defineComponent({
      setup(_, { expose }) {
        expose({ refreshAllBoardState })
        return () => h('div', 'board')
      }
    })
    const router = createRouter({
      history: createMemoryHistory(),
      routes: [{ path: '/board', name: 'board', component: BoardRoute }],
    })
    const auth = useAuth()
    auth.login('alice-token', {
      userId: 1,
      phone: '13800138000',
      username: 'alice',
    })
    const runningSession = {
      id: 'background-session',
      userId: 1,
      title: 'Background work',
      updatedAt: '2026-08-01T12:00:00Z',
      active: true,
      latestTerminalMessageId: null,
      latestExecutionStatus: null,
      hasUnreadUpdate: false
    }
    chatApi.getSessionList
      .mockResolvedValueOnce([runningSession])
      .mockResolvedValue([{ ...runningSession,
        active: false,
        latestTerminalMessageId: 21,
        latestExecutionStatus: 'COMPLETED',
        hasUnreadUpdate: true
      }])
    const store = useChatStore()
    store.closeChat()
    await router.push('/board')
    await router.isReady()

    const wrapper = mount(App, { global: { plugins: [router, i18n] } })
    await flushPromises()
    expect(store.state.activeCount).toBe(1)

    window.dispatchEvent(new Event('focus'))
    await flushPromises()

    expect(refreshAllBoardState).toHaveBeenCalledOnce()
    expect(store.state.activeCount).toBe(0)
    expect(store.state.unreadCount).toBe(1)
    expect(store.state.reconciliationRequired).toBe(false)
    wrapper.unmount()
    auth.logout()
  })

  it('reconciles a terminal message that completed between hidden-session polls', async () => {
    const refreshAllBoardState = vi.fn().mockResolvedValue(true)
    const BoardRoute = defineComponent({
      setup(_, { expose }) {
        expose({ refreshAllBoardState })
        return () => h('div', 'board')
      }
    })
    const router = createRouter({
      history: createMemoryHistory(),
      routes: [{ path: '/board', name: 'board', component: BoardRoute }],
    })
    const auth = useAuth()
    auth.login('alice-token', {
      userId: 1,
      phone: '13800138000',
      username: 'alice',
    })
    chatApi.getSessionList
      .mockResolvedValueOnce([])
      .mockResolvedValue([{
        id: 'fast-background-session',
        userId: 1,
        title: 'Fast background work',
        updatedAt: '2026-08-01T12:00:01Z',
        active: false,
        latestTerminalMessageId: 25,
        latestExecutionStatus: 'COMPLETED',
        hasUnreadUpdate: true
      }])
    const store = useChatStore()
    store.closeChat()
    await router.push('/board')
    await router.isReady()

    const wrapper = mount(App, { global: { plugins: [router, i18n] } })
    await flushPromises()
    window.dispatchEvent(new Event('focus'))
    await flushPromises()

    expect(refreshAllBoardState).toHaveBeenCalledOnce()
    expect(store.state.unreadCount).toBe(1)
    expect(store.state.reconciliationRequired).toBe(false)
    wrapper.unmount()
    auth.logout()
  })

  it('keeps failed background reconciliation visible and retries it', async () => {
    const refreshAllBoardState = vi.fn()
      .mockResolvedValueOnce(false)
      .mockResolvedValueOnce(true)
    const BoardRoute = defineComponent({
      setup(_, { expose }) {
        expose({ refreshAllBoardState })
        return () => h('div', 'board')
      }
    })
    const router = createRouter({
      history: createMemoryHistory(),
      routes: [{ path: '/board', name: 'board', component: BoardRoute }],
    })
    const auth = useAuth()
    auth.login('alice-token', {
      userId: 1,
      phone: '13800138000',
      username: 'alice',
    })
    const runningSession = {
      id: 'retry-session',
      userId: 1,
      title: 'Retry background sync',
      updatedAt: '2026-08-01T12:00:00Z',
      active: true,
      latestTerminalMessageId: null,
      latestExecutionStatus: null,
      hasUnreadUpdate: false
    }
    chatApi.getSessionList
      .mockResolvedValueOnce([runningSession])
      .mockResolvedValue([{ ...runningSession,
        active: false,
        latestTerminalMessageId: 31,
        latestExecutionStatus: 'PARTIAL',
        hasUnreadUpdate: true
      }])
    const store = useChatStore()
    store.closeChat()
    await router.push('/board')
    await router.isReady()

    const wrapper = mount(App, { global: { plugins: [router, i18n] } })
    await flushPromises()
    window.dispatchEvent(new Event('focus'))
    await flushPromises()

    expect(refreshAllBoardState).toHaveBeenCalledTimes(1)
    expect(store.state.reconciliationRequired).toBe(true)

    window.dispatchEvent(new Event('focus'))
    await flushPromises()

    expect(refreshAllBoardState).toHaveBeenCalledTimes(2)
    expect(store.state.reconciliationRequired).toBe(false)
    wrapper.unmount()
    auth.logout()
  })

  it('unmounts the board route when navigation leaves the workspace', async () => {
    const boardUnmounted = vi.fn()
    const BoardRoute = defineComponent({
      setup() {
        onBeforeUnmount(boardUnmounted)
        return () => h('div', 'board')
      },
    })
    const PublicRoute = defineComponent({
      setup: () => () => h('div', 'public'),
    })
    const router = createRouter({
      history: createMemoryHistory(),
      routes: [
        { path: '/board', name: 'board', component: BoardRoute },
        { path: '/', name: 'landing', component: PublicRoute, meta: { public: true } },
      ],
    })

    const auth = useAuth()
    auth.login('alice-token', {
      userId: 1,
      phone: '13800138000',
      username: 'alice',
    })
    useChatStore().closeChat()
    await router.push('/board')
    await router.isReady()
    const wrapper = mount(App, { global: { plugins: [router, i18n] } })

    await router.push('/')
    await flushPromises()
    await nextTick()

    expect(boardUnmounted).toHaveBeenCalledOnce()
    wrapper.unmount()
    auth.logout()
  })

  it('keeps a private route mounted across query changes within the same view', async () => {
    const boardMounted = vi.fn()
    const boardUnmounted = vi.fn()
    const BoardRoute = defineComponent({
      setup() {
        onMounted(boardMounted)
        onBeforeUnmount(boardUnmounted)
        return () => h('div', 'board')
      },
    })
    const router = createRouter({
      history: createMemoryHistory(),
      routes: [{ path: '/board', name: 'board', component: BoardRoute }],
    })
    const auth = useAuth()
    auth.login('alice-token', {
      userId: 1,
      phone: '13800138000',
      username: 'alice',
    })

    await router.push('/board')
    await router.isReady()
    const wrapper = mount(App, { global: { plugins: [router, i18n] } })
    await flushPromises()
    expect(boardMounted).toHaveBeenCalledOnce()

    // Query params address content *within* a view (the board's open run). Remounting on
    // every param change would discard the state the URL exists to restore.
    await router.push('/board?run=verification:12')
    await flushPromises()
    await router.push('/board?run=verification:12&trace=34')
    await flushPromises()
    await router.push('/board')
    await flushPromises()

    expect(boardUnmounted).not.toHaveBeenCalled()
    expect(boardMounted).toHaveBeenCalledOnce()

    wrapper.unmount()
    auth.logout()
  })

  it('remounts a private route when the authenticated user changes', async () => {
    const boardMounted = vi.fn()
    const boardUnmounted = vi.fn()
    const BoardRoute = defineComponent({
      setup() {
        onMounted(boardMounted)
        onBeforeUnmount(boardUnmounted)
        return () => h('div', 'board')
      },
    })
    const router = createRouter({
      history: createMemoryHistory(),
      routes: [{ path: '/board', name: 'board', component: BoardRoute }],
    })
    const auth = useAuth()
    auth.login('alice-token', {
      userId: 1,
      phone: '13800138000',
      username: 'alice',
    })

    await router.push('/board')
    await router.isReady()
    const wrapper = mount(App, { global: { plugins: [router, i18n] } })
    await flushPromises()
    expect(boardMounted).toHaveBeenCalledOnce()

    const chatStore = useChatStore()
    chatStore.setActiveCount(2)
    chatStore.setUnreadCount(1)
    chatStore.setReconciliationRequired(true)

    auth.login('bob-token', {
      userId: 2,
      phone: '13900139000',
      username: 'bob',
    })
    await nextTick()
    await flushPromises()

    expect(boardUnmounted).toHaveBeenCalledOnce()
    expect(boardMounted).toHaveBeenCalledTimes(2)
    expect(chatStore.state.activeCount).toBe(0)
    expect(chatStore.state.unreadCount).toBe(0)
    expect(chatStore.state.reconciliationRequired).toBe(false)

    auth.login('bob-token-refreshed', {
      userId: 2,
      phone: '13900139000',
      username: 'bob',
    })
    await nextTick()
    expect(boardUnmounted).toHaveBeenCalledOnce()
    expect(boardMounted).toHaveBeenCalledTimes(2)

    wrapper.unmount()
    auth.logout()
  })

  it('unmounts a private route and redirects to login after cross-tab logout', async () => {
    const boardUnmounted = vi.fn()
    const BoardRoute = defineComponent({
      setup() {
        onBeforeUnmount(boardUnmounted)
        return () => h('div', 'private board')
      },
    })
    const LandingRoute = defineComponent({
      setup: () => () => h('div', 'login'),
    })
    const router = createRouter({
      history: createMemoryHistory(),
      routes: [
        { path: '/board', name: 'board', component: BoardRoute },
        { path: '/', name: 'landing', component: LandingRoute, meta: { public: true } },
      ],
    })
    const auth = useAuth()
    auth.login('alice-token', {
      userId: 1,
      phone: '13800138000',
      username: 'alice',
    })
    await router.push('/board')
    await router.isReady()
    const wrapper = mount(App, { global: { plugins: [router, i18n] } })
    await flushPromises()

    auth.logout()
    await flushPromises()
    await nextTick()

    expect(boardUnmounted).toHaveBeenCalledOnce()
    expect(router.currentRoute.value.path).toBe('/')
    expect(router.currentRoute.value.query).toEqual({ mode: 'login', redirect: '/board' })
    expect(wrapper.text()).toContain('login')
    expect(wrapper.text()).not.toContain('private board')
    wrapper.unmount()
  })
})

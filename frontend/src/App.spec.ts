import { defineComponent, h, nextTick, onBeforeUnmount, onMounted } from 'vue'
import { flushPromises, mount } from '@vue/test-utils'
import { createMemoryHistory, createRouter } from 'vue-router'
import { describe, expect, it, vi } from 'vitest'
import App from './App.vue'
import { i18n } from '@/assets/i18n'
import { useChatStore } from '@/stores/chat'
import { useAuth } from '@/stores/auth'

describe('App route lifecycle', () => {
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

    auth.login('bob-token', {
      userId: 2,
      phone: '13900139000',
      username: 'bob',
    })
    await nextTick()
    await flushPromises()

    expect(boardUnmounted).toHaveBeenCalledOnce()
    expect(boardMounted).toHaveBeenCalledTimes(2)

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

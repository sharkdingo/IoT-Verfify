import { defineComponent, h, nextTick, onBeforeUnmount } from 'vue'
import { flushPromises, mount } from '@vue/test-utils'
import { createMemoryHistory, createRouter } from 'vue-router'
import { describe, expect, it, vi } from 'vitest'
import App from './App.vue'
import { i18n } from '@/assets/i18n'
import { useChatStore } from '@/stores/chat'

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

    useChatStore().closeChat()
    await router.push('/board')
    await router.isReady()
    const wrapper = mount(App, { global: { plugins: [router, i18n] } })

    await router.push('/')
    await flushPromises()
    await nextTick()

    expect(boardUnmounted).toHaveBeenCalledOnce()
    wrapper.unmount()
  })
})

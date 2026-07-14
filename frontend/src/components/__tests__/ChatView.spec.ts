// @vitest-environment jsdom
import { flushPromises, mount } from '@vue/test-utils'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

import { i18n } from '@/assets/i18n'
import { useChatStore } from '@/stores/chat'

const chatApi = vi.hoisted(() => ({
  createSession: vi.fn(),
  deleteSession: vi.fn(),
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

const mountChat = () => mount(ChatView, {
  props: { boardMode: true },
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

  it('renders the pending response inside one compact assistant bubble', async () => {
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
    expect(pendingBubble.text()).toContain('正在回复')
    expect(wrapper.find('.msg-content-wrapper > .thinking-state').exists()).toBe(false)

    finishStream()
    await flushPromises()
    wrapper.unmount()
  })
})

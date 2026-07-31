import { afterEach, describe, expect, it } from 'vitest'
import { useChatStore } from './chat'

describe('chat shared operation state', () => {
  const store = useChatStore()

  afterEach(() => {
    store.setStreaming(false)
    store.setActiveCount(0)
    store.setUnreadCount(0)
    store.setReconciliationRequired(false)
    store.closeChat()
  })

  it('exposes an active stream to Board replacement and playback guards', () => {
    expect(store.state.streaming).toBe(false)

    store.setStreaming(true)

    expect(store.state.streaming).toBe(true)
  })

  it('keeps visibility independent from stream ownership', () => {
    store.openChat()
    store.setStreaming(true)
    store.closeChat()

    expect(store.state.visible).toBe(false)
    expect(store.state.streaming).toBe(true)
  })

  it('keeps the persistent result count independent from panel visibility', () => {
    store.setUnreadCount(3)
    store.closeChat()

    expect(store.state.unreadCount).toBe(3)
  })

  it('keeps the authoritative active-session count independent from panel visibility', () => {
    store.setActiveCount(2)
    store.closeChat()

    expect(store.state.activeCount).toBe(2)
  })

  it('keeps failed background reconciliation visible and independent from panel visibility', () => {
    store.setReconciliationRequired(true)
    store.closeChat()

    expect(store.state.reconciliationRequired).toBe(true)
  })
})

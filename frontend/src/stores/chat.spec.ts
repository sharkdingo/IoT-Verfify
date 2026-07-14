import { afterEach, describe, expect, it } from 'vitest'
import { useChatStore } from './chat'

describe('chat shared operation state', () => {
  const store = useChatStore()

  afterEach(() => {
    store.setStreaming(false)
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
})

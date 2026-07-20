import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

class FakeBroadcastChannel {
  static instances: FakeBroadcastChannel[] = []
  readonly posted: unknown[] = []
  private listener: ((event: MessageEvent) => void) | null = null

  constructor(readonly name: string) {
    FakeBroadcastChannel.instances.push(this)
  }

  addEventListener(_type: string, listener: (event: MessageEvent) => void) {
    this.listener = listener
  }

  postMessage(message: unknown) {
    this.posted.push(message)
  }

  emit(data: unknown) {
    this.listener?.({ data } as MessageEvent)
  }

  close() {}
}

describe('board invalidation channel', () => {
  beforeEach(() => {
    vi.resetModules()
    FakeBroadcastChannel.instances = []
    vi.stubGlobal('BroadcastChannel', FakeBroadcastChannel)
  })

  afterEach(() => {
    vi.unstubAllGlobals()
  })

  it('publishes semantic mutations and scopes received events by user', async () => {
    const { publishBoardInvalidation, subscribeBoardInvalidation } =
      await import('../boardInvalidation')
    const received: unknown[] = []
    const unsubscribe = subscribeBoardInvalidation(7, message => received.push(message))

    const channel = FakeBroadcastChannel.instances[0]
    channel.emit({ type: 'BOARD_INVALIDATED', userId: 8, reason: 'manual', issuedAt: 1 })
    channel.emit({ type: 'BOARD_INVALIDATED', userId: 7, reason: 'http-mutation', issuedAt: 2 })
    expect(received).toHaveLength(1)

    publishBoardInvalidation(7, 'chat-tool')
    expect(channel.posted).toEqual([
      expect.objectContaining({ type: 'BOARD_INVALIDATED', userId: 7, reason: 'chat-tool' })
    ])

    unsubscribe()
    channel.emit({ type: 'BOARD_INVALIDATED', userId: 7, reason: 'manual', issuedAt: 3 })
    expect(received).toHaveLength(1)
  })
})

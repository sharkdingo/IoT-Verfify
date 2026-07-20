export type BoardInvalidationReason = 'http-mutation' | 'chat-tool' | 'manual'

type BoardInvalidationMessage = {
  type: 'BOARD_INVALIDATED'
  userId: number
  reason: BoardInvalidationReason
  issuedAt: number
}

const CHANNEL_NAME = 'iot-verify-board-invalidation-v1'
const VALID_REASONS = new Set<BoardInvalidationReason>(['http-mutation', 'chat-tool', 'manual'])
const listeners = new Set<(message: BoardInvalidationMessage) => void>()
let channel: BroadcastChannel | null = null

const getChannel = (): BroadcastChannel | null => {
  if (channel || typeof window === 'undefined' || typeof BroadcastChannel === 'undefined') {
    return channel
  }
  channel = new BroadcastChannel(CHANNEL_NAME)
  channel.addEventListener('message', event => {
    const message = event.data as Partial<BoardInvalidationMessage> | null
    if (message?.type !== 'BOARD_INVALIDATED'
      || !Number.isSafeInteger(message.userId) || Number(message.userId) <= 0
      || !VALID_REASONS.has(message.reason as BoardInvalidationReason)
      || typeof message.issuedAt !== 'number' || !Number.isFinite(message.issuedAt)) return
    listeners.forEach(listener => listener(message as BoardInvalidationMessage))
  })
  return channel
}

export const publishBoardInvalidation = (
  userId: number | null | undefined,
  reason: BoardInvalidationReason
) => {
  if (!Number.isSafeInteger(userId) || userId == null || userId <= 0) return
  getChannel()?.postMessage({
    type: 'BOARD_INVALIDATED',
    userId,
    reason,
    issuedAt: Date.now()
  } satisfies BoardInvalidationMessage)
}

export const subscribeBoardInvalidation = (
  userId: number | null | undefined,
  listener: (message: BoardInvalidationMessage) => void
) => {
  if (!Number.isSafeInteger(userId) || userId == null || userId <= 0) return () => undefined
  getChannel()
  const scopedListener = (message: BoardInvalidationMessage) => {
    if (message.userId === userId) listener(message)
  }
  listeners.add(scopedListener)
  return () => listeners.delete(scopedListener)
}

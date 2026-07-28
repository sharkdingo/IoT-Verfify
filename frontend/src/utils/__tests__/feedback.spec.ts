// @vitest-environment jsdom
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

const elementPlus = vi.hoisted(() => ({
  message: Object.assign(vi.fn(), {
    success: vi.fn(), info: vi.fn(), warning: vi.fn(), error: vi.fn(), closeAll: vi.fn()
  }),
  box: { confirm: vi.fn(), alert: vi.fn(), close: vi.fn() }
}))

vi.mock('element-plus', () => ({
  ElMessage: elementPlus.message,
  ElMessageBox: elementPlus.box
}))

import {
  acknowledge,
  confirmDestructive,
  dismissAllNotifications,
  dismissOpenConfirmation,
  notifyBlocked,
  notifyError,
  notifyInfo,
  notifySuccess
} from '../feedback'
import { i18n } from '@/assets/i18n'

beforeEach(() => {
  vi.clearAllMocks()
  // Backend free text is only shown when it matches the active locale; pin it so the
  // locale-matching behaviour is what is under test, not the default.
  i18n.global.locale.value = 'en'
})

afterEach(() => {
  vi.restoreAllMocks()
})

describe('toast severities', () => {
  it('maps each intent to one severity and always sets a duration', () => {
    notifySuccess('saved')
    notifyInfo('noted')
    notifyBlocked('close playback first')
    notifyError('request failed')

    for (const [call, message] of [
      [elementPlus.message.success, 'saved'],
      [elementPlus.message.info, 'noted'],
      [elementPlus.message.warning, 'close playback first'],
      [elementPlus.message.error, 'request failed']
    ] as const) {
      expect(call).toHaveBeenCalledTimes(1)
      const options = call.mock.calls[0][0] as { message: string, duration: number }
      expect(options.message).toBe(message)
      expect(options.duration).toBeGreaterThan(0)
    }
  })

  it('gives an error longer on screen than a success', () => {
    notifySuccess('saved')
    notifyError('failed')
    const success = elementPlus.message.success.mock.calls[0][0] as { duration: number }
    const failure = elementPlus.message.error.mock.calls[0][0] as { duration: number }
    expect(failure.duration).toBeGreaterThan(success.duration)
  })

  it('clears every open toast when the board changes context wholesale', () => {
    dismissAllNotifications()
    expect(elementPlus.message.closeAll).toHaveBeenCalledOnce()
  })
})

describe('confirmDestructive', () => {
  it('reports confirmation as true and cancellation as false, never throwing', async () => {
    elementPlus.box.confirm.mockResolvedValueOnce('confirm')
    await expect(confirmDestructive({ title: 'Delete', message: 'Sure?' })).resolves.toBe(true)

    elementPlus.box.confirm.mockRejectedValueOnce('cancel')
    await expect(confirmDestructive({ title: 'Delete', message: 'Sure?' })).resolves.toBe(false)

    // A dismissal (Escape / backdrop) is also an ordinary "no".
    elementPlus.box.confirm.mockRejectedValueOnce('close')
    await expect(confirmDestructive({ title: 'Delete', message: 'Sure?' })).resolves.toBe(false)
  })

  it('marks the confirm button as dangerous and keeps a cancel affordance', async () => {
    elementPlus.box.confirm.mockResolvedValueOnce('confirm')
    await confirmDestructive({ title: 'Delete rule', message: 'Sure?', confirmText: 'Delete' })

    const [message, title, options] = elementPlus.box.confirm.mock.calls[0] as [
      string, string, Record<string, unknown>
    ]
    expect(message).toBe('Sure?')
    expect(title).toBe('Delete rule')
    expect(options.confirmButtonText).toBe('Delete')
    expect(options.cancelButtonText).toBeTruthy()
    expect(options.confirmButtonClass).toContain('danger')
  })

  it('does not lock scroll, because the board shell is a fixed non-scrolling surface', async () => {
    elementPlus.box.confirm.mockResolvedValueOnce('confirm')
    await confirmDestructive({ title: 'Delete', message: 'Sure?' })
    const options = elementPlus.box.confirm.mock.calls[0][2] as Record<string, unknown>
    expect(options.lockScroll).toBe(false)
    expect(options.appendTo).toBe('body')
  })
})

describe('acknowledge', () => {
  it('resolves even when dismissed, since there is nothing further to decide', async () => {
    elementPlus.box.alert.mockRejectedValueOnce('close')
    await expect(acknowledge({ title: 'Invalid scene', message: 'Details' })).resolves.toBeUndefined()
  })

  it('carries its own tone for a diagnostic report', async () => {
    elementPlus.box.alert.mockResolvedValueOnce('confirm')
    await acknowledge({ title: 'Invalid scene', message: 'Details', tone: 'error' })
    const options = elementPlus.box.alert.mock.calls[0][2] as Record<string, unknown>
    expect(options.type).toBe('error')
  })
})

describe('dismissOpenConfirmation', () => {
  it('closes a confirmation whose owning surface went away', () => {
    dismissOpenConfirmation()
    expect(elementPlus.box.close).toHaveBeenCalledOnce()
  })
})

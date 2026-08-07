// @vitest-environment jsdom
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

const elementPlus = vi.hoisted(() => ({
  message: Object.assign(vi.fn(), {
    success: vi.fn(), info: vi.fn(), warning: vi.fn(), error: vi.fn(), closeAll: vi.fn()
  }),
  box: { confirm: vi.fn(), alert: vi.fn(), close: vi.fn() }
}))

vi.mock('element-plus', () => ({
  /*
   * `HintTooltip` imports `ElTooltip`, and a whole-module mock hides it — every case in the file then fails at
   * import time with "No 'ElTooltip' export is defined", a message that names the mock rather than the component
   * needing it. A render-slot stub suffices: nothing here asserts tooltip behaviour, only the control it wraps.
   */
  ElTooltip: { name: 'ElTooltip', template: '<slot />' },
  ElMessage: elementPlus.message,
  ElMessageBox: elementPlus.box
}))

import {
  acknowledge,
  confirmChoice,
  confirmDestructive,
  dismissAllNotifications,
  dismissOpenConfirmation,
  notifyBlocked,
  notifyError,
  notifyInfo,
  notifySuccess
} from '../feedback'
import { i18n } from '@/assets/i18n'
import { openModalDepth } from '@/composables/useBodyScrollLock'

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

  it('groups identical errors instead of stacking duplicate toasts', () => {
    notifyError('history failed')

    expect(elementPlus.message.error).toHaveBeenCalledWith(expect.objectContaining({
      message: 'history failed',
      grouping: true
    }))
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

describe('confirmChoice', () => {
  /*
   * The non-destructive half. It exists because every confirmation used to be `confirmDestructive`, so a red
   * button appeared on "apply this AI suggestion anyway" and on "delete this device" alike — which left the
   * danger colour meaning nothing at the one moment it has to mean something.
   */
  it('asks the same question without a danger button', async () => {
    elementPlus.box.confirm.mockResolvedValueOnce('confirm')
    await expect(confirmChoice({
      title: 'Similar rule exists',
      message: 'Save anyway?',
      confirmText: 'Save anyway'
    })).resolves.toBe(true)

    const [message, title, options] = elementPlus.box.confirm.mock.calls[0] as [
      string, string, Record<string, unknown>
    ]
    expect(message).toBe('Save anyway?')
    expect(title).toBe('Similar rule exists')
    expect(options.confirmButtonText).toBe('Save anyway')
    expect(options.cancelButtonText).toBeTruthy()
    expect(options.confirmButtonClass).toBeUndefined()
    // Same surface contract as the destructive variant: teleported, and no scroll lock.
    expect(options.lockScroll).toBe(false)
    expect(options.appendTo).toBe('body')
  })

  it('treats cancelling as an ordinary outcome', async () => {
    elementPlus.box.confirm.mockRejectedValueOnce('cancel')
    await expect(confirmChoice({ title: 'Proceed', message: 'Sure?' })).resolves.toBe(false)
  })

  it('counts as a modal surface, so the board accelerators stay blocked behind it', async () => {
    // Same leak as the destructive path: without this, the board's window-level Ctrl+Z reached the surface
    // behind an open confirmation and undid an edit the user could not see.
    expect(openModalDepth.value).toBe(0)
    let settle!: () => void
    elementPlus.box.confirm.mockImplementationOnce(() => new Promise<void>(resolve => {
      settle = resolve
    }))
    const pending = confirmChoice({ title: 'Proceed', message: 'Sure?' })
    expect(openModalDepth.value).toBe(1)
    settle()
    await pending
    expect(openModalDepth.value).toBe(0)
  })
})

describe('modal depth registration', () => {
  // A MessageBox is modal to the user but takes no scroll lock (the board shell is a fixed 100vh
  // surface), so it does not register through `useModalAccessibility` like a `role="dialog"` panel.
  // Without counting here, the board's window-level Ctrl+Z stayed unblocked and undid an edit on the
  // surface behind an open confirmation.
  it('counts an open confirmation as a modal surface and releases it on settle', async () => {
    expect(openModalDepth.value).toBe(0)

    let settle!: () => void
    elementPlus.box.confirm.mockImplementationOnce(() => new Promise<void>(resolve => {
      settle = resolve
    }))
    const pending = confirmDestructive({ title: 'Delete', message: 'Sure?' })
    expect(openModalDepth.value).toBe(1)

    settle()
    await pending
    expect(openModalDepth.value).toBe(0)
  })

  it('releases the count when the confirmation is cancelled or fails', async () => {
    elementPlus.box.confirm.mockRejectedValueOnce('cancel')
    await confirmDestructive({ title: 'Delete', message: 'Sure?' })
    expect(openModalDepth.value).toBe(0)

    elementPlus.box.confirm.mockRejectedValueOnce(new Error('boom'))
    await confirmDestructive({ title: 'Delete', message: 'Sure?' })
    expect(openModalDepth.value).toBe(0)
  })

  it('releases the count when a confirmation is dismissed programmatically', async () => {
    // `ElMessageBox.close()` closes the surface without settling its promise, so the helper's own
    // `finally` never runs. Without an explicit release the count leaked and the board's Ctrl+Z — which
    // reads this depth — stayed blocked for the rest of the session while the toolbar button still
    // looked enabled. Reachable when a rule dialog closes underneath its own "save anyway" prompt.
    elementPlus.box.confirm.mockImplementationOnce(() => new Promise<void>(() => {
      // never settles, matching Element Plus's programmatic close
    }))
    void confirmDestructive({ title: 'Delete', message: 'Sure?' })
    expect(openModalDepth.value).toBe(1)

    dismissOpenConfirmation()

    expect(elementPlus.box.close).toHaveBeenCalled()
    expect(openModalDepth.value).toBe(0)
  })

  it('counts an acknowledgement too', async () => {
    let settle!: () => void
    elementPlus.box.alert.mockImplementationOnce(() => new Promise<void>(resolve => {
      settle = resolve
    }))
    const pending = acknowledge({ title: 'Heads up', message: 'Done' })
    expect(openModalDepth.value).toBe(1)

    settle()
    await pending
    expect(openModalDepth.value).toBe(0)
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

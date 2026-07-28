// @vitest-environment jsdom
import { describe, expect, it } from 'vitest'

import { resolveBoardUndoIntent, targetOwnsNativeUndo } from '../boardUndoShortcut'

const keydown = (init: Partial<KeyboardEventInit> & { key: string }) =>
  new KeyboardEvent('keydown', init)

describe('resolveBoardUndoIntent', () => {
  it('maps the Windows/Linux and macOS accelerators to undo', () => {
    expect(resolveBoardUndoIntent(keydown({ key: 'z', ctrlKey: true }))).toBe('undo')
    expect(resolveBoardUndoIntent(keydown({ key: 'z', metaKey: true }))).toBe('undo')
    // Layout-independent: `key` reports the typed character, and case must not matter.
    expect(resolveBoardUndoIntent(keydown({ key: 'Z', ctrlKey: true }))).toBe('undo')
  })

  it('maps both redo conventions', () => {
    expect(resolveBoardUndoIntent(keydown({ key: 'z', ctrlKey: true, shiftKey: true }))).toBe('redo')
    expect(resolveBoardUndoIntent(keydown({ key: 'z', metaKey: true, shiftKey: true }))).toBe('redo')
    expect(resolveBoardUndoIntent(keydown({ key: 'y', ctrlKey: true }))).toBe('redo')
  })

  it('ignores a keystroke while an IME composition is active', () => {
    // During Chinese/Japanese/Korean input the keystroke belongs to the composition; stealing it
    // would discard half-typed text.
    const composing = keydown({ key: 'z', ctrlKey: true })
    Object.defineProperty(composing, 'isComposing', { value: true })
    expect(resolveBoardUndoIntent(composing)).toBeNull()

    const imeKeyCode = keydown({ key: 'Process', ctrlKey: true })
    Object.defineProperty(imeKeyCode, 'keyCode', { value: 229 })
    expect(resolveBoardUndoIntent(imeKeyCode)).toBeNull()
  })

  it('ignores unrelated and over-modified combinations', () => {
    expect(resolveBoardUndoIntent(keydown({ key: 'z' }))).toBeNull()
    expect(resolveBoardUndoIntent(keydown({ key: 's', ctrlKey: true }))).toBeNull()
    expect(resolveBoardUndoIntent(keydown({ key: 'z', ctrlKey: true, altKey: true }))).toBeNull()
    // Both primary modifiers together is an OS/browser shortcut, not ours.
    expect(resolveBoardUndoIntent(keydown({ key: 'z', ctrlKey: true, metaKey: true }))).toBeNull()
    expect(resolveBoardUndoIntent(keydown({ key: 'y', ctrlKey: true, shiftKey: true }))).toBeNull()
  })
})

describe('targetOwnsNativeUndo', () => {
  it('leaves text entry controls to their own undo stack', () => {
    for (const tag of ['input', 'textarea']) {
      const element = document.createElement(tag)
      expect(targetOwnsNativeUndo(element), tag).toBe(true)
    }
  })

  it('leaves contenteditable regions and their descendants alone', () => {
    const editor = document.createElement('div')
    editor.setAttribute('contenteditable', 'true')
    // jsdom does not implement isContentEditable, so model what the browser reports.
    Object.defineProperty(editor, 'isContentEditable', { value: true })
    const inner = document.createElement('span')
    Object.defineProperty(inner, 'isContentEditable', { value: true })
    editor.append(inner)

    expect(targetOwnsNativeUndo(editor)).toBe(true)
    expect(targetOwnsNativeUndo(inner)).toBe(true)
  })

  it('claims the keystroke for ordinary board surfaces', () => {
    expect(targetOwnsNativeUndo(document.createElement('div'))).toBe(false)
    expect(targetOwnsNativeUndo(document.createElement('button'))).toBe(false)
    expect(targetOwnsNativeUndo(null)).toBe(false)
  })
})

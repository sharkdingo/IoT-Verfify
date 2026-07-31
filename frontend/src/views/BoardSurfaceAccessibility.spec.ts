import { readFileSync } from 'node:fs'
import { dirname, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { describe, expect, it } from 'vitest'

const currentDirectory = dirname(fileURLToPath(import.meta.url))
const boardSource = readFileSync(resolve(currentDirectory, 'Board.vue'), 'utf8')
const boardCss = readFileSync(resolve(currentDirectory, '../styles/board.css'), 'utf8')

describe('Board surface accessibility contracts', () => {
  it('keeps the automatic-fix request owner mounted while its dialog is hidden', () => {
    const fixDialogStart = boardSource.indexOf('<FixResultDialog')
    const fixDialog = boardSource.slice(fixDialogStart, boardSource.indexOf('/>', fixDialogStart) + 2)

    expect(fixDialogStart).toBeGreaterThan(-1)
    expect(fixDialog).toContain('ref="fixResultDialogRef"')
    expect(fixDialog).toContain(':visible="showFixDialog"')
    expect(fixDialog).not.toContain('v-if=')

    const openFixStart = boardSource.indexOf('const openFixDialog =')
    const openFixDialog = boardSource.slice(
      openFixStart,
      boardSource.indexOf('const canFixVerificationResultTrace', openFixStart)
    )
    expect(openFixDialog).toContain('canOpenTrace?.(traceId) === false')
    expect(openFixDialog).toContain('showFixDialog.value = true')
    expect(openFixDialog.indexOf('canOpenTrace?.(traceId) === false'))
      .toBeLessThan(openFixDialog.indexOf('fixTraceId.value = traceId'))
  })

  it('keeps the template instance dialog focus-managed and the delete footer reachable', () => {
    const templateDialog = boardSource.slice(
      boardSource.indexOf('v-if="templateInstanceDialogVisible"'),
      boardSource.indexOf('<!-- Left Sidebar - Control Center -->')
    )
    expect(templateDialog).toContain('@keydown="handleTemplateInstanceDialogKeydown"')
    expect(templateDialog).toContain(':ref="setTemplateInstanceDialogRef"')
    expect(templateDialog).toContain('tabindex="-1"')
    expect(templateDialog).toContain('max-h-[calc(100dvh-2rem)]')

    const deleteDialog = boardSource.slice(
      boardSource.indexOf('<!-- Custom Delete Confirmation Dialog -->'),
      boardSource.indexOf('<FuzzingResultDialog')
    )
    expect(deleteDialog).toContain('max-h-[calc(100dvh-1.5rem)]')
    expect(deleteDialog).toContain('min-h-0 flex-1 overflow-y-auto overscroll-contain')
    expect(deleteDialog).toContain('flex shrink-0 flex-wrap justify-end')
  })

  it('names the concrete template value behind blank initial-value choices', () => {
    const placeholder = boardSource.slice(
      boardSource.indexOf('const templateVariableInputPlaceholder ='),
      boardSource.indexOf('const buildTemplateInstanceRuntimeConfig')
    )
    expect(placeholder).toContain('getTemplateVariableDefaultValue(variable)')
    expect(placeholder).toContain("t('app.useTemplateDefaultWithValue', { value: defaultValue })")

    const templateDialog = boardSource.slice(
      boardSource.indexOf('v-if="templateInstanceDialogVisible"'),
      boardSource.indexOf('<!-- Left Sidebar - Control Center -->')
    )
    expect(templateDialog).toContain(
      'formatTemplateModelToken(templateInstanceDialogData.template, getTemplateVariableDefaultValue(variable))'
    )
  })

  it('isolates narrow-screen background controls and respects reduced motion', () => {
    const narrowBackground = boardSource.slice(
      boardSource.indexOf('data-testid="board-narrow-background"') - 100,
      boardSource.indexOf('data-testid="board-narrow-background"') + 300
    )
    expect(narrowBackground).toContain(':inert="showNarrowPanelScrim ? true : undefined"')
    expect(narrowBackground).toContain(':aria-hidden="showNarrowPanelScrim ? \'true\' : undefined"')

    expect(boardCss).toMatch(/\.bg-amber-100[\s\S]*background-color:\s*color-mix\(in srgb, #f59e0b 14%, var\(--surface-panel\)\)\s*!important/)
    expect(boardCss).toMatch(/\.text-amber-950[\s\S]*color:\s*#fde68a\s*!important/)
    expect(boardCss).toMatch(/\.text-red-700[\s\S]*color:\s*#fecaca\s*!important/)
    expect(boardCss).toMatch(/\.text-cyan-700[\s\S]*color:\s*#a5f3fc\s*!important/)
    expect(boardCss).toMatch(/@media \(prefers-reduced-motion: reduce\)[\s\S]*\.board-side-panel[\s\S]*\.animate-ping/)
    const resultDialogTheme = boardCss.slice(
      boardCss.indexOf('.dark .board-result-dialog-surface'),
      boardCss.indexOf('.iot-board .modern-panel')
    )
    expect(resultDialogTheme).toContain('.dark .board-result-dialog-surface .bg-amber-50')
    expect(resultDialogTheme).toContain('background-color: color-mix(in srgb, #f59e0b 13%, var(--surface-elevated)) !important')
    expect(resultDialogTheme).toContain('.dark .board-result-dialog-surface :is(')
    expect(resultDialogTheme).toContain('.text-red-600, .text-red-700, .text-red-800, .text-red-900')
    expect(resultDialogTheme).toContain('color: #fecaca !important')
    expect(resultDialogTheme).toContain('.text-violet-600')
    expect(resultDialogTheme).toContain('color: #c7d2fe !important')
    expect(resultDialogTheme).toContain('.text-cyan-700')
    expect(resultDialogTheme).toContain('color: #a5f3fc !important')
    expect(resultDialogTheme).toContain('.border-amber-200, .border-amber-300')
    expect(resultDialogTheme).not.toContain('.iot-board')

    const verificationResultStatus = boardSource.slice(
      boardSource.indexOf('const verificationResultStatus = computed'),
      boardSource.indexOf('const verificationModelSemanticsConsistent = computed')
    )
    expect(verificationResultStatus).not.toContain('bg-gradient-to-r')

    expect(boardCss).toMatch(/@media \(prefers-reduced-motion: reduce\)[\s\S]*\.board-result-dialog-surface,\s*\.board-result-dialog-surface \*/)
    expect(boardCss).not.toContain('.iot-board .board-result-dialog-surface')
  })

  it('keeps the playback change inspector beside the timeline in short landscape viewports', () => {
    expect(boardSource).toContain("'has-playback-change-popover': showPlaybackChangePopover")

    const shortLandscapePlayback = boardCss.slice(
      boardCss.indexOf('A short landscape viewport cannot stack the change inspector'),
      boardCss.indexOf('/* ==========', boardCss.indexOf('A short landscape viewport cannot stack the change inspector'))
    )
    expect(shortLandscapePlayback).toContain('@media (min-width: 640px) and (max-height: 599.98px)')
    expect(shortLandscapePlayback).toContain('.iot-board.has-playback-change-popover .board-playback-change-popover')
    expect(shortLandscapePlayback).toContain('width: min(22rem, 42vw)')
    expect(shortLandscapePlayback).toContain('.iot-board.has-playback-change-popover .board-timeline-host')
    expect(shortLandscapePlayback).toContain('right: calc(min(22rem, 42vw) + (var(--board-floating-gap, 1rem) * 2))')
  })

  it('pairs disabled formal-run controls with visible reasons', () => {
    for (const kind of ['verification', 'simulation']) {
      const button = boardSource.slice(
        boardSource.indexOf(`data-testid="run-${kind}"`) - 150,
        boardSource.indexOf(`data-testid="${kind}-run-blocked-reason"`) + 350
      )
      expect(button).toContain(`:aria-describedby="${kind}RunBlockedReason`)
      expect(button).toContain(`id="${kind}-run-blocked-reason"`)
      expect(button).toContain(`{{ ${kind}RunBlockedReason }}`)
    }
  })
})

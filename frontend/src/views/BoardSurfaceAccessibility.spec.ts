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
    // The shared primitive owns overflow, overscroll containment, the scrollbar skin, and the
    // scroll-padding that keeps a programmatically revealed control clear of the boundary. Asserting
    // `overflow-y-auto overscroll-contain` pinned two of those four and let the other two drift —
    // which is how 31 regions ended up with a scrollbar that did not match the product and no
    // scroll-padding for keyboard users.
    expect(deleteDialog).toContain('iot-scroll-region')
    expect(deleteDialog).toContain('min-h-0 flex-1')
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

    // The two assertions that used to sit here pinned class-keyed `!important` remaps for
    // `.bg-amber-100` and `.text-amber-950` inside the board panels. Those rules existed only because
    // components declared raw hues that dark theme then had to rewrite; with every component on
    // theme-aware roles the selectors could never match, so they were deleted along with the rest of
    // that block. The property they were protecting — panel status colours stay legible in dark — is
    // now owned by the roles and enforced in `styles/__tests__/semanticColourOwnership.spec.ts`.
    expect(boardCss).toMatch(/@media \(prefers-reduced-motion: reduce\)[\s\S]*\.board-side-panel[\s\S]*\.animate-ping/)

    // The result dialogs' status colours come from theme-aware role classes, so no class-keyed
    // override is needed to make them legible in dark. This used to assert the overrides themselves —
    // 28 `!important` selectors and their exact hex values — which made the test a copy of the CSS: it
    // failed on a change that improved the very thing it was protecting. What matters is the property,
    // so assert that: the roles are used, and the per-theme rewriting is gone.
    const resultDialogTheme = boardCss.slice(
      boardCss.indexOf('.dark .board-result-dialog-surface'),
      boardCss.indexOf('.iot-board .modern-panel')
    )
    expect(resultDialogTheme).not.toMatch(/\.text-(red|amber|green|emerald|indigo|violet|fuchsia|orange|cyan)-\d{3}/)
    expect(resultDialogTheme).not.toContain('.iot-board')

    // The verdict decision table maps each outcome to a role, never to a hue ramp.
    const verdictTable = boardSource.slice(
      boardSource.indexOf('const verificationResultStatus = computed'),
      boardSource.indexOf('const verificationModelSemanticsConsistent = computed')
    )
    expect(verdictTable).toMatch(/board-surface-(danger|warning|success)/)
    expect(verdictTable).not.toMatch(/bg-(red|amber|green|emerald)-\d{2,3}/)

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
    /*
     * The contract is the geometry — the timeline yields the inspector's width plus a gap on each side.
     *
     * Asserted without the fallback that used to sit inside the `var()`. The reason recorded here was **wrong**:
     * it claimed `--board-floating-gap` is declared at `:root`, so `, 1rem` could never be reached. It is
     * declared on `.iot-board` (`board.css:557`), and the two timeline hosts are *siblings* of that element, not
     * descendants — so inside them the variable did not resolve, `calc()` became invalid, and `left`/`right` fell
     * back to `auto`. A fixed box with both set to `auto` shrink-wraps at its static position: the trace overlay
     * sat flush against x=0 with the whole right side of the screen empty, and on a 101-state trace the
     * shrink-wrap reached 3258px and pushed the play button off-screen at 1440x900.
     *
     * The fallback was load-bearing for exactly these two elements, and removing it is what exposed that. The fix
     * was not to restore it — `boardShellStyle` now injects the variable onto the hosts, so they are positioned by
     * values they can actually see, and `boardDockGeometry.spec.ts` pins the two readers together.
     */
    expect(shortLandscapePlayback).toContain('right: calc(min(22rem, 42vw) + (var(--board-floating-gap) * 2))')
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

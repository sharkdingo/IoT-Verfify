import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * The counterexample-details dialog reached by the replay bar's "Run details" button
 * (`data-testid="trace-details-dialog"`).
 *
 * Text assertions over the source rather than a mounted render, for the reason recorded in
 * `actionDockHierarchy.spec.ts`: `Board.vue` is far too large to mount cheaply. What these pin is
 * the set of defects the dialog actually shipped with, each of which typechecked or read fine and
 * still broke the feature:
 *
 * - it bound `violatedSpec.name`, a field `Specification` does not have
 * - it offered no way to download the model it describes, while three other surfaces did
 * - its i18n keys (`app.createdAt`, `app.modelGenerationIssues`) were never defined, so the dialog
 *   rendered the raw key strings to the user — now guarded centrally by `i18nLiteralKeys.spec.ts`,
 *   which resolves every literal key through the real messages object
 */
describe('counterexample details dialog', () => {
  const root = join(process.cwd(), 'src')
  const board = readFileSync(join(root, 'views/Board.vue'), 'utf8')
  const specTypes = readFileSync(join(root, 'types/spec.ts'), 'utf8')

  /** The dialog block, so assertions cannot accidentally match identical markup elsewhere. */
  const dialog = (() => {
    const start = board.indexOf('data-testid="trace-details-dialog"')
    expect(start, 'trace-details-dialog should exist').toBeGreaterThan(-1)
    const end = board.indexOf('board-timeline-host--trace', start)
    expect(end, 'the replay bar should follow it').toBeGreaterThan(start)
    return board.slice(start, end)
  })()

  it('binds only fields that exist on the specification type', () => {
    // `name` is the field it used to bind. Proving the type lacks it is what makes this a real guard
    // rather than a restatement of the current code.
    expect(specTypes).not.toMatch(/^\s+name\??:/m)
    expect(dialog, 'must not bind a non-existent `name`').not.toContain('violatedSpec?.name')
    expect(dialog, 'label falls back templateLabel -> formula, as fuzzing findings do')
      .toContain('violatedSpec?.templateLabel')
  })

  it('does not offer the run-level model download, and escalates to the run instead', () => {
    // The SMV model is one per *run*: every counterexample under a run came out of the same model.
    // Offering the download here implied one model per counterexample, and put a scene-level artifact
    // behind a per-evidence surface. It lives in the verification result dialog now; this dialog
    // carries a link to the owning run instead, so the artifact is still one click away.
    expect(dialog, 'no run-level artifact download in a counterexample surface')
      .not.toContain('download-counterexample-smv')
    expect(dialog, 'and no direct call to the trace-keyed download')
      .not.toContain('downloadVerificationTraceSmv')

    const escalateAt = dialog.indexOf('data-testid="counterexample-open-owning-run"')
    expect(escalateAt, 'the escalation control should exist').toBeGreaterThan(-1)
    // Keyed on the owning run, not on the trace: `verificationTaskId` is the run this evidence
    // belongs to, and only a persisted counterexample has one.
    const guards = [...dialog.slice(0, escalateAt).matchAll(/v-if="([^"]*traceDetailsView[^"]*)"/g)]
    expect(guards.length, 'the escalation must carry a v-if guard').toBeGreaterThan(0)
    expect(guards[guards.length - 1][1], 'guarded on the owning run id')
      .toContain('traceDetailsView.verificationTaskId')
  })

  it('navigates to the owning run through the URL, not a retained result ref', () => {
    // A counterexample can be opened straight from history with no run loaded, so restoring a
    // retained `verificationResult` would land on nothing. The URL is the single authority for which
    // run is on screen, so this goes through the deep-link opener.
    const at = board.indexOf('const openOwningVerificationRun')
    expect(at, 'the handler should exist').toBeGreaterThan(-1)
    const body = board.slice(at, at + 400)
    expect(body, 'it opens a verification run target').toMatch(/openRunTarget\(\{\s*kind: 'verification'/)
    expect(body, 'and closes the counterexample dialog it came from')
      .toContain('dismissTraceDetailsDialog()')
    expect(body, 'not by assigning a retained result')
      .not.toMatch(/verificationResult\.value\s*=/)
  })

  it('separates this counterexample from the run that produced it', () => {
    // Everything here used to read as one flat list of "counterexample properties", but the attack
    // and privacy chips and model completeness describe the *run* and are identical across every
    // counterexample it produced. A reader comparing two counterexamples could not tell which
    // differences were even possible. Both sections must exist, and the run-context one must hold
    // the run-level chips.
    const evidenceAt = dialog.indexOf('data-testid="counterexample-evidence"')
    const contextAt = dialog.indexOf('data-testid="counterexample-run-context"')
    expect(evidenceAt, 'the per-counterexample section should exist').toBeGreaterThan(-1)
    expect(contextAt, 'the run-context section should exist').toBeGreaterThan(-1)
    expect(evidenceAt, 'the counterexample itself comes first').toBeLessThan(contextAt)

    const evidence = dialog.slice(evidenceAt, contextAt)
    expect(evidence, 'the violated specification is per-counterexample')
      .toContain('violatedSpec?.templateLabel')
    expect(evidence, 'so is the state count').toContain('statesInTrace')
    // The run-level facts must NOT sit in the evidence section.
    expect(evidence, 'attack scope is a run fact').not.toContain('attackSelectionSummary')
    expect(evidence, 'so is model completeness').not.toContain('modelComplete')

    const context = dialog.slice(contextAt)
    expect(context, 'attack scope belongs to the run').toContain('attackSelectionSummary')
    expect(context, 'privacy scope belongs to the run').toContain('enablePrivacy')
    expect(context, 'model completeness belongs to the run').toContain('modelComplete')
    expect(context, 'and the heading must say the facts repeat across counterexamples')
      .toContain('counterexampleRunContextHeading')
  })

  it('does not hide the timeline while showing this dialog', () => {
    // The dialog sits over the replay bar rather than replacing it: opening it sets only its own ref,
    // never `traceAnimationState.visible`.
    const at = board.indexOf('const openVerificationTraceDetails = () => {')
    expect(at).toBeGreaterThan(-1)
    const body = board.slice(at, at + 700)
    expect(body, 'opening the dialog must not close the playback surface')
      .not.toMatch(/traceAnimationState\.value\.visible\s*=/)
    expect(board, 'and the timeline renders on its own visibility flag')
      .toContain('v-if="traceAnimationState.visible && currentTrace"')
  })

  it('resolves the playing trace through the accessor the rest of the replay uses', () => {
    // A second local lookup implemented only the `savedTraces` branch, so in the state
    // `currentTrace`'s fallback exists for it claimed no run details while a trace was playing.
    expect(board, 'currentTrace must keep its two-branch fallback')
      .toMatch(/const currentTrace = computed\(\(\) => \{[\s\S]{0,400}verificationResult\.value\?\.traces/)
    const at = board.indexOf('const openVerificationTraceDetails = () => {')
    const body = board.slice(at, at + 700)
    expect(body, 'it must reuse the accessor').toContain('currentTrace.value')
    expect(body, 'and must not re-index savedTraces itself')
      .not.toMatch(/savedTraces\.value\[/)
  })

  it('keeps the replay bar dispatching exploration findings away from the verifier', () => {
    // One button serves two run kinds; keying it on the finding is what stops an exploration
    // result from opening the verifier's dialog.
    // `lastIndexOf`: the first occurrence of this id in the file is the `querySelector` string that
    // restores focus on dismiss, not the button, and searching forward from there found neither guard.
    const at = board.lastIndexOf('data-testid="trace-timeline-run-details"')
    expect(at, 'the replay bar run-details button should exist').toBeGreaterThan(-1)
    // The guard sits on the wrapping HintTooltip, not the button, so the window has to reach past the
    // <button> open tag to find it.
    const wrapperAt = board.lastIndexOf('<HintTooltip', at)
    expect(wrapperAt, 'the button should be wrapped in a tooltip').toBeGreaterThan(-1)
    expect(board.slice(wrapperAt, at), 'a fuzz finding must not reach this dialog')
      .toContain('!activeFuzzingFinding')
    expect(board.slice(wrapperAt, at), 'and an unsaved trace has no run to show')
      .toContain('currentTrace.verificationTaskId')
  })
})

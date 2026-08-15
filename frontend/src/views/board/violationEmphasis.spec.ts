import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * Arriving at the violating step must change the canvas, not only the rail.
 *
 * The rail marked the step with a ring and an 11px label from the start of playback, but during playback
 * the eye is on the canvas — and reaching the violating state changed nothing there: autoplay simply
 * called `stopTraceAnimation()` on the last state. The run's whole purpose arrived in silence.
 *
 * Measured in a browser on `acceptance-demo-scene.json`: step 0 → 0 emphasised nodes, step 1 →
 * 1 (`camera_1`, the device the violated specification binds), returning to step 0 → 0 again.
 */
describe('violation emphasis reaches the canvas', () => {
  const root = process.cwd()
  const board = readFileSync(join(root, 'src/views/Board.vue'), 'utf8')
  const canvas = readFileSync(join(root, 'src/components/CanvasBoard.vue'), 'utf8')
  const css = readFileSync(join(root, 'src/styles/board.css'), 'utf8')
  const specTypes = readFileSync(join(root, 'src/types/spec.ts'), 'utf8')

  it('passes the violating step and its subject devices to the canvas', () => {
    // Derived once at the binding rather than added to each writer of `highlightedTrace`: a writer that
    // forgot the field would be a violation the canvas silently failed to mark.
    expect(board, 'the canvas must receive the wrapped trace')
      .toContain(':highlighted-trace="canvasHighlightedTrace"')
    const at = board.indexOf('const canvasHighlightedTrace')
    expect(at, 'the wrapper should exist').toBeGreaterThan(-1)
    const body = board.slice(at, at + 2400)
    expect(body, 'it must carry the violating step').toContain('violationStateIndex')
    // Named `violatedSpec` fields, not a specific accessor: this asserted `violatedSpec?.boundDeviceIds`,
    // which `Specification` does not declare, so it pinned the defect in place. Which fields carry the
    // ids is the subject of its own test below.
    expect(body, 'and the devices the violated specification binds')
      .toMatch(/violationDeviceIds[\s\S]*violatedSpec\?\./)
  })

  it('scopes the emphasis to the step, so it clears when the viewer leaves', () => {
    const at = canvas.indexOf('const isAtViolationStep')
    expect(at).toBeGreaterThan(-1)
    const body = canvas.slice(at, at + 800)
    // Equality against the selected index is what makes it step state rather than a sticky mark.
    expect(body).toContain('trace.violationStateIndex === trace.selectedStateIndex')
    // A liveness violation occupies a whole cycle, so the set wins where it exists: testing only the
    // cycle's first state would drop the emphasis while the viewer is still inside the failing loop.
    expect(body, 'the step set must be honoured before the single index')
      .toContain('steps.includes(trace.selectedStateIndex)')
  })

  it('marks every step of a liveness cycle, not just the one the rail labels', () => {
    // Templates 2/5/6 negate to EG/GF, so NuSMV refutes them with an infinite lasso path. Trace 83
    // (`scene_spec_4`, "the front door never re-locks while nobody is home") is the measured case: 5 states,
    // loop from index 3, and its final state repeats index 3 exactly. Template 5 was missing from the
    // last-state set entirely, so that run marked no step and emphasised no device.
    const at = board.indexOf('const counterexampleViolationSteps')
    expect(at, 'the step set should exist').toBeGreaterThan(-1)
    const body = board.slice(at, at + 900)
    expect(body, 'the cycle is enumerated from the loop range').toContain('counterexampleLoopRange')

    const range = board.slice(board.indexOf('const counterexampleLoopRange'), at)
    // Read from NuSMV's own marker rather than guessed from the template or the index.
    expect(range, 'the loop is located by the backend flag').toContain("state?.loopStart === true")
    // But gated on the template, because the marker alone does not mean the cycle is the violation.
    expect(range, 'only a liveness template may claim its cycle').toContain('LIVENESS_TEMPLATES')
  })

  it('does not treat a loop on a safety counterexample as the violation', () => {
    // Measured on NuSMV 2.7.1: `-- Loop starts here` appears on SAFETY counterexamples too — a CTL
    // `AG(motion -> AX light)` (template 4) trace and an LTL `G(p)` trace both carry one, and the LTL trace
    // carried the line TWICE. Keying the cycle off the marker alone therefore marked a cycle for a safety
    // violation and re-admitted template 4, the one template that must deliberately claim no step.
    const liveness = board.slice(board.indexOf('const LIVENESS_TEMPLATES'), board.indexOf('const LIVENESS_TEMPLATES') + 200)
    expect(liveness, 'exactly the liveness templates').toMatch(/'2'.*'5'.*'6'/)

    const at = board.indexOf('const counterexampleViolationSteps')
    const body = board.slice(at, at + 1100)
    // A liveness template with no marker must claim nothing rather than falling through to the last state,
    // whose values are a loop re-print.
    expect(body, 'liveness is handled on its own branch').toContain('LIVENESS_TEMPLATES.has(String(templateId))')

    // Two markers in one trace: the backend computes loopBack against the LAST one, so the frontend must
    // agree or it would over-mark by a state.
    const range = board.slice(board.indexOf('const counterexampleLoopRange'), at)
    expect(range, 'the last marker wins, matching the backend').toContain('start = index')

    // A liveness template must never fall through to the last-state rule, which would name a single
    // step for a fault that has none. Assert the set literal itself, not a source window: the surrounding
    // prose legitimately names 2/5/6 when explaining why they are excluded.
    const declaration = board.slice(board.indexOf('const LAST_STATE_VIOLATION_TEMPLATES'))
    const literal = declaration.slice(0, declaration.indexOf(')') + 1)
    expect(literal, 'the safety templates keyed by last state').toContain("'1', '3', '7'")
    expect(literal, 'liveness templates are excluded from the last-state rule').not.toMatch(/'2'|'5'|'6'/)
  })

  it('does not carry a counterexample violation into a simulation replay', () => {
    // `savedTraces` has three writers and no reset, and `currentTrace` prefers it unconditionally — so a
    // counterexample opened earlier stays selected while a simulation replays through the same
    // `highlightedTrace`, and the canvas outlined that counterexample's devices on a run that violated
    // nothing. The emphasis is gated on the active playback kind instead.
    const at = board.indexOf('const canvasHighlightedTrace')
    const body = board.slice(at, at + 2400)
    expect(body, 'the gate must read the playback kind').toContain("activePlaybackKind.value === 'counterexample'")
    expect(body, 'a fuzz finding is also a violation replay').toContain("activePlaybackKind.value === 'fuzzing'")
    // All three violation fields must be gated, not just the step: the device ids alone would still paint.
    expect(body).toMatch(/violationStateIndex:\s*isViolationPlayback/)
    expect(body).toMatch(/violationStateIndexes:\s*isViolationPlayback/)
    expect(body).toMatch(/violationDeviceIds\s*=\s*isViolationPlayback/)
  })

  it('says why the loop-closing step shows no change, rather than reporting an empty diff', () => {
    // NuSMV re-prints the loop entry with no variable lines, so the delta merge makes the final state
    // identical to its predecessor. "No observable changes" is then true but reads as a broken animation.
    const popover = readFileSync(join(root, 'src/components/PlaybackChangePopover.vue'), 'utf8')
    const loopAt = popover.indexOf('data-testid="playback-change-loop-back"')
    const emptyAt = popover.indexOf('data-testid="playback-change-empty"')
    expect(loopAt, 'the loop explanation must exist').toBeGreaterThan(-1)
    expect(loopAt, 'and be tested before the generic empty state').toBeLessThan(emptyAt)
    expect(board, 'the board must tell the popover which step closes the loop')
      .toContain(':is-loop-back-state="activePlaybackIsLoopBackState"')
  })

  it('scopes the emphasis to the specification subject, with a non-silent fallback', () => {
    const at = canvas.indexOf('const isNodeAtViolation')
    expect(at).toBeGreaterThan(-1)
    const body = canvas.slice(at, at + 300)
    expect(body, 'bound devices win when the specification names any').toContain('scoped.has(node.id)')
    expect(body, 'and a specification binding none must still mark something')
      .toContain('isNodeInTrace(node)')
    expect(canvas, 'the class must be applied to the node').toContain("'device-at-violation': isNodeAtViolation(node)")
  })

  it('reads the subject devices off fields the specification type actually has', () => {
    // The scoping above is only real if the id list is non-empty for a specification that names devices.
    // It used to read `violatedSpec.boundDeviceIds` — a field `Specification` does not declare — so the
    // list was permanently `[]`, the fallback ran every time, and the canvas emphasised every device in
    // the state. The shape assertion in the gating test above passed throughout, because the defect was
    // the field name rather than the expression.
    expect(specTypes, 'the fabricated field must not appear on the type')
      .not.toMatch(/boundDeviceIds/)

    const at = board.indexOf('const canvasHighlightedTrace')
    const body = board.slice(at, at + 2400)
    // The bare identifier, not an access shape: `(spec as any)?.boundDeviceIds` reads the same absent
    // field while matching no accessor pattern, and a cast is exactly how this defect returns.
    const code = body.split('\n').filter(line => !line.trim().startsWith('//')).join('\n')
    expect(code, 'and must not be read by the derivation, cast or not')
      .not.toContain('boundDeviceIds')
    // `devices` is the accumulated reference list; the conditions are the authority behind it. Asserted
    // separately so the derivation can be reordered without a false failure.
    expect(body, 'the accumulated device references').toMatch(/violatedSpec\?\.devices/)
    for (const side of ['aConditions', 'ifConditions', 'thenConditions']) {
      expect(body, `${side} carry deviceId and must be read`).toContain(`violatedSpec?.${side}`)
    }
    expect(body, 'and the ids must be de-duplicated across the two sources').toMatch(/new Set\(/)
  })

  it('keeps the ring under reduced motion while dropping the arrival flash', () => {
    // Reduced motion may remove animation, never information: the ring states "this is the violating
    // step", so only the flash is suppressed.
    expect(css).toContain('.iot-board .device-node.device-at-violation')
    expect(css, 'the persistent statement is an outline, not an animation')
      .toMatch(/\.device-node\.device-at-violation\s*\{[^}]*outline:\s*3px solid var\(--danger-fill\)/)
    const reduced = css.slice(css.indexOf('@media (prefers-reduced-motion: reduce)', css.indexOf('device-at-violation')))
    expect(reduced.slice(0, 1200), 'the flash must be listed for suppression')
      .toContain('device-at-violation')
  })

  it('uses the non-text indicator token rather than a literal red', () => {
    // `--danger-fill` is measured at 4.41:1 light / 3.70:1 dark, against the 3:1 WCAG 1.4.11 asks of a
    // non-text indicator; a literal would not be theme-aware.
    const at = css.indexOf('.iot-board .device-node.device-at-violation')
    const block = css.slice(at, at + 1200)
    expect(block).toContain('var(--danger-fill)')
    expect(block, 'no literal hex red').not.toMatch(/#(EF4444|ef4444|F87171|f87171)/)
  })
})

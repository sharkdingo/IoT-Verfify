// Pure decision helpers for the verification-trace playback surface in Board.vue.
// Extracted so the mutual-exclusion guard and the trace-context fallback can be unit-tested
// without mounting the whole Board component.

import type { Trace } from '@/types/verify'

export interface PlaybackPanelState {
  simulationVisible: boolean
  recommendationPanelVisible: boolean
}

export interface PlaybackGuardResult {
  allowed: boolean
  // Warning message to surface when playback is blocked; empty when allowed.
  reason: string
}

/**
 * Whether a verification trace may open the playback animation right now. A trace uses the same
 * animation surface as the simulation timeline and the recommendations panel, so it must not stack
 * on top of either. Mirrors the guards `selectAndPlayTrace` applies to the current-result path.
 */
export function canOpenTracePlayback(state: PlaybackPanelState): PlaybackGuardResult {
  if (state.simulationVisible) {
    return { allowed: false, reason: 'Please close the simulation timeline first' }
  }
  if (state.recommendationPanelVisible) {
    return { allowed: false, reason: 'Please close the Rule Recommendations panel first' }
  }
  return { allowed: true, reason: '' }
}

export interface TraceContext {
  isAttack: boolean
  intensity: number
}

export interface VerificationFormContext {
  isAttack: boolean
  intensity: number
}

/**
 * The verification context to label a trace with: the trace's own stored context when available
 * (backend derives isAttack/intensity from the request snapshot), else the live form as a fallback
 * for legacy traces recorded before the snapshot existed (isAttack null/undefined).
 */
export function deriveTraceContext(
  trace: Pick<Trace, 'isAttack' | 'intensity'> | null | undefined,
  form: VerificationFormContext
): TraceContext {
  if (trace && trace.isAttack !== undefined && trace.isAttack !== null) {
    return { isAttack: !!trace.isAttack, intensity: trace.intensity ?? 0 }
  }
  return { isAttack: form.isAttack, intensity: form.intensity }
}

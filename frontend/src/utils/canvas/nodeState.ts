import type { DeviceManifest } from '@/types/device'

type StateManifest = Pick<DeviceManifest, 'Modes' | 'InitState' | 'WorkingStates'>

const normalizedWorkingStates = (manifest?: StateManifest | null): string[] =>
  Array.isArray(manifest?.WorkingStates)
    ? manifest.WorkingStates
        .map(state => String(state?.Name || '').trim())
        .filter(Boolean)
    : []

export const hasModeledStateMachine = (manifest?: StateManifest | null): boolean =>
  Boolean(
    Array.isArray(manifest?.Modes) && manifest.Modes.length > 0
    && normalizedWorkingStates(manifest).length > 0
  )

export const resolveEffectiveNodeState = (
  configuredState: unknown,
  manifest?: StateManifest | null,
  fallback = ''
): string => {
  const configured = String(configuredState ?? '').trim()
  const initial = String(manifest?.InitState ?? '').trim()
  const legalStates = normalizedWorkingStates(manifest)

  if (!hasModeledStateMachine(manifest)) return configured || initial || fallback
  if (configured && legalStates.includes(configured)) return configured
  if (initial && legalStates.includes(initial)) return initial
  return legalStates[0] || fallback
}

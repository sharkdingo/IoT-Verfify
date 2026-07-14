import type { ModelEnvironmentVariable } from '@/types/model'

export type EnvironmentPatchField = 'value' | 'trust' | 'privacy'

export interface SourcedEnvironmentPatches {
  source: string
  patches: ModelEnvironmentVariable[]
}

export interface EnvironmentPatchConflict {
  name: string
  field: EnvironmentPatchField
  firstSource: string
  secondSource: string
}

export const mergeSourcedEnvironmentPatches = (
  rows: SourcedEnvironmentPatches[]
): { merged: ModelEnvironmentVariable[]; conflicts: EnvironmentPatchConflict[] } => {
  const mergedByName = new Map<string, ModelEnvironmentVariable>()
  const sourcesByField = new Map<string, string>()
  const conflicts: EnvironmentPatchConflict[] = []

  for (const row of rows) {
    for (const patch of row.patches || []) {
      const name = String(patch?.name ?? '').trim()
      if (!name) continue
      const merged = mergedByName.get(name) || { name }

      for (const field of ['value', 'trust', 'privacy'] as const) {
        const value = patch[field]
        if (value === undefined) continue
        const sourceKey = `${name}\u0000${field}`
        const firstSource = sourcesByField.get(sourceKey)
        if (firstSource && merged[field] !== value) {
          conflicts.push({ name, field, firstSource, secondSource: row.source })
          continue
        }
        merged[field] = value
        sourcesByField.set(sourceKey, row.source)
      }

      mergedByName.set(name, merged)
    }
  }

  return { merged: Array.from(mergedByName.values()), conflicts }
}

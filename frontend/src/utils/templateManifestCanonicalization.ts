const compareManifestKeys = (left: string, right: string) =>
  left.localeCompare(right, 'en', { numeric: true, sensitivity: 'base' })

/**
 * Canonical manifest shape used when comparing a request with a server round trip.
 * Backend template DTOs omit null object fields, so an optional explicit null and an
 * omitted field represent the same persisted manifest. Array order remains semantic.
 */
export const canonicalizeTemplateManifest = (value: unknown): unknown => {
  if (Array.isArray(value)) return value.map(canonicalizeTemplateManifest)
  if (value && typeof value === 'object') {
    return Object.keys(value as Record<string, unknown>)
      .sort(compareManifestKeys)
      .reduce<Record<string, unknown>>((result, key) => {
        const next = canonicalizeTemplateManifest((value as Record<string, unknown>)[key])
        if (next !== undefined && next !== null) result[key] = next
        return result
      }, {})
  }
  return value
}

export const templateManifestSemanticKey = (manifest: unknown): string =>
  JSON.stringify(canonicalizeTemplateManifest(manifest))

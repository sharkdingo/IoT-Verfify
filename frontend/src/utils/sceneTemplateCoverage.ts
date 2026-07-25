import type { DeviceTemplate } from '@/types/device'

const normalizeTemplateName = (value: unknown): string =>
  String(value ?? '').trim().toLowerCase()

const canonicalValue = (value: unknown): unknown => {
  if (Array.isArray(value)) return value.map(canonicalValue)
  if (value && typeof value === 'object') {
    return Object.keys(value as Record<string, unknown>)
      .sort((left, right) => left.localeCompare(right, 'en', { numeric: true, sensitivity: 'base' }))
      .reduce<Record<string, unknown>>((result, key) => {
        const next = canonicalValue((value as Record<string, unknown>)[key])
        if (next !== undefined) result[key] = next
        return result
      }, {})
  }
  return value
}

const manifestKey = (template: DeviceTemplate): string =>
  JSON.stringify(canonicalValue(template.manifest))

export const sceneTemplatesCoveredByCatalog = (
  expectedTemplates: DeviceTemplate[],
  existingTemplates: DeviceTemplate[],
  createdTemplates: DeviceTemplate[]
): boolean => {
  const expectedByName = new Map(expectedTemplates.map(template => [
    normalizeTemplateName(template.name || template.manifest?.Name),
    template
  ]))
  const availableByName = new Map<string, DeviceTemplate>()
  for (const template of [...existingTemplates, ...createdTemplates]) {
    const key = normalizeTemplateName(template.name || template.manifest?.Name)
    if (key) availableByName.set(key, template)
  }
  if (createdTemplates.some(template =>
    !expectedByName.has(normalizeTemplateName(template.name || template.manifest?.Name)))) {
    return false
  }
  for (const [key, expected] of expectedByName) {
    const available = availableByName.get(key)
    if (!available || manifestKey(available) !== manifestKey(expected)) return false
  }
  return true
}

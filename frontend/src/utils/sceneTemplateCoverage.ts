import type { DeviceTemplate } from '@/types/device'
import { templateManifestSemanticKey } from '@/utils/templateManifestCanonicalization'

const normalizeTemplateName = (value: unknown): string =>
  String(value ?? '').trim().toLowerCase()

const manifestKey = (template: DeviceTemplate): string =>
  templateManifestSemanticKey(template.manifest)

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

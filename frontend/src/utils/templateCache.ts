// Frontend-only cache for device template manifests used by nodes.
// Goal: deleting a template should NOT affect existing nodes (they keep variables/states/APIs).
//
// We store a snapshot of the manifest keyed by nodeId in localStorage.
// This avoids any backend changes and survives page reloads.

import type { DeviceManifest } from '@/types/device'

type ManifestCache = Record<string, DeviceManifest>

const STORAGE_KEY = 'iot_verify_node_manifest_cache_v1'

const safeParse = (raw: string | null): ManifestCache => {
  if (!raw) return {}
  try {
    const parsed = JSON.parse(raw)
    if (!parsed || typeof parsed !== 'object') return {}
    return parsed as ManifestCache
  } catch {
    return {}
  }
}

const readAll = (): ManifestCache => {
  return safeParse(localStorage.getItem(STORAGE_KEY))
}

const writeAll = (data: ManifestCache) => {
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(data))
  } catch {
    // ignore quota / privacy mode errors; fallback behavior will still work when template exists
  }
}

export const getCachedManifestForNode = (nodeId: string): DeviceManifest | null => {
  const map = readAll()
  return map[nodeId] ?? null
}

export const cacheManifestForNode = (nodeId: string, manifest: DeviceManifest | null | undefined) => {
  if (!nodeId || !manifest) return
  const map = readAll()
  map[nodeId] = manifest
  writeAll(map)
}

/**
 * If a node currently resolves to a template manifest, snapshot it so later template deletion won't break UI.
 */
export const hydrateManifestCacheForNodes = (
  nodes: Array<{ id: string; templateName?: string }>,
  templates: Array<{ manifest?: DeviceManifest | null }>,
  resolveTemplateForNode: (node: { id: string; templateName?: string }) => { manifest?: DeviceManifest | null } | null
) => {
  if (!nodes?.length) return
  for (const n of nodes) {
    // If already cached, skip
    if (getCachedManifestForNode(n.id)) continue
    const tpl = resolveTemplateForNode(n)
    const manifest = tpl?.manifest ?? null
    if (manifest) cacheManifestForNode(n.id, manifest)
  }
}












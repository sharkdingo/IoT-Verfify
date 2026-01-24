import type {
    BasicDeviceInfo,
    DeviceApiView,
    DeviceManifest,
    DeviceStateView,
    DeviceTemplate,
    DeviceVariableView
} from '../types/device'
import type { DeviceNode } from '../types/node'

// --- 图标与路径 ---

export const getDeviceIconPath = (folder: string, state: string) => {
    return new URL(`../assets/${folder}/${state}.svg`, import.meta.url).href
}

export const getNodeIcon = (node: DeviceNode) => {
    const folder = node.templateName.replace(/ /g, '_')
    const state = node.state || 'Working'

    // Try different state name variations
    const possibleStates = [state, state.toLowerCase(), state.charAt(0).toUpperCase() + state.slice(1).toLowerCase()]

    for (const stateName of possibleStates) {
        try {
            const path = getDeviceIconPath(folder, stateName)
            // In a real implementation, you'd check if the file exists
            // For now, we'll just return the first possibility
            return path
        } catch (e) {
            continue
        }
    }

    // Fallback to a default icon or placeholder
    return getDeviceIconPath('default', 'Working')
}

// --- 状态查找 ---

export const getEndStateByApi = (
    templates: DeviceTemplate[],
    templateName: string,
    apiName: string
): string | null => {
    const tpl = templates.find(t => t.name === templateName)
    if (!tpl) return null
    const api = tpl.manifest.APIs.find(a => a.Name === apiName)
    return api ? api.EndState : null
}

// --- 信息提取 (用于 DeviceDialog 展示) ---

export const extractBasicDeviceInfo = (
    manifest: DeviceManifest | null | undefined,
    fallbackName: string,
    instanceLabel: string,
    fallbackDescription: string
): BasicDeviceInfo => {
    const name = manifest?.Name ?? fallbackName
    const description = manifest?.Description ?? fallbackDescription
    const initState = manifest?.InitState ?? ''
    const impacted = Array.isArray(manifest?.ImpactedVariables) ? manifest!.ImpactedVariables : []

    return {
        name,
        instanceLabel,
        description,
        initState,
        impactedVariables: impacted
    }
}

export const extractDeviceVariables = (
    manifest: DeviceManifest | null | undefined
): DeviceVariableView[] => {
    if (!manifest) return []
    const views: DeviceVariableView[] = []

    // 1. Internal Variables
    if (Array.isArray(manifest.InternalVariables)) {
        manifest.InternalVariables.forEach(v => {
            let valStr = ''
            if (v.Values && v.Values.length) valStr = v.Values.join(' / ')
            else if (v.LowerBound !== undefined && v.UpperBound !== undefined) valStr = `[${v.LowerBound}, ${v.UpperBound}]`

            views.push({
                name: v.Name,
                value: valStr, // 这里展示类型或范围
                trust: v.Trust ?? ''
            })
        })
    }

    // 2. Impacted Variables
    if (Array.isArray(manifest.ImpactedVariables)) {
        manifest.ImpactedVariables.forEach(name => {
            if (!views.some(v => v.name === name)) {
                views.push({ name, value: '(External)', trust: '' })
            }
        })
    }
    return views
}

export const extractDeviceStates = (
    manifest: DeviceManifest | null | undefined
): DeviceStateView[] => {
    if (!manifest || !Array.isArray(manifest.WorkingStates)) return []
    return manifest.WorkingStates.map(ws => ({
        name: ws.Name,
        description: ws.Description,
        trust: ws.Trust
    }))
}

export const extractDeviceApis = (
    manifest: DeviceManifest | null | undefined
): DeviceApiView[] => {
    if (!manifest || !Array.isArray(manifest.APIs)) return []
    return manifest.APIs.map(api => ({
        name: api.Name,
        from: api.StartState,
        to: api.EndState,
        description: api.Description ?? ''
    }))
}

// --- 校验逻辑 ---

export const validateManifest = (obj: any): { valid: boolean; msg?: string } => {
    if (!obj || typeof obj !== 'object') return { valid: false, msg: 'Invalid JSON object' }

    // 必填字段检查
    if (!obj.Name) return { valid: false, msg: 'Missing field "Name"' }
    if (obj.InitState === undefined) return { valid: false, msg: 'Missing field "InitState"' }

    // 数组类型检查
    if (!Array.isArray(obj.InternalVariables)) return { valid: false, msg: '"InternalVariables" must be an array' }
    if (!Array.isArray(obj.WorkingStates)) return { valid: false, msg: '"WorkingStates" must be an array' }
    if (!Array.isArray(obj.APIs)) return { valid: false, msg: '"APIs" must be an array' }

    // 逻辑一致性检查
    // 1. InitState 必须存在于 WorkingStates 中 (或者是空字符串，某些设备允许)
    if (obj.InitState !== '' && obj.WorkingStates.length > 0) {
        const stateNames = obj.WorkingStates.map((s: any) => s.Name)
        if (!stateNames.includes(obj.InitState)) {
            return { valid: false, msg: `InitState "${obj.InitState}" is not defined in WorkingStates` }
        }
    }

    return { valid: true }
}

// --- 默认设备图标 (SVG字符串) ---
export const getDefaultDeviceIcon = (deviceType: string): string => {
  const defaultIcons: Record<string, string> = {
    Sensor: `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="12" fill="#3B82F6" stroke="#1E40AF" stroke-width="2"/>
      <path d="M16 8v8l6 4" stroke="white" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>
    </svg>`,
    Switch: `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="8" y="12" width="16" height="8" rx="4" fill="#10B981" stroke="#059669" stroke-width="2"/>
      <circle cx="20" cy="16" r="3" fill="white"/>
    </svg>`,
    Light: `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <path d="M16 4v6M8 12l4 4M24 12l-4 4M12 20l4 4M20 20l-4 4" stroke="#F59E0B" stroke-width="2" stroke-linecap="round"/>
      <circle cx="16" cy="14" r="6" fill="#F59E0B" stroke="#D97706" stroke-width="2"/>
    </svg>`
  }
  return defaultIcons[deviceType] || `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
    <rect x="4" y="4" width="24" height="24" rx="4" fill="#6B7280" stroke="#4B5563" stroke-width="2"/>
    <text x="16" y="20" text-anchor="middle" fill="white" font-size="12" font-family="Arial">?</text>
  </svg>`
}

// --- 增强版图标获取函数 ---
export const getNodeIconWithFallback = (node: DeviceNode): string => {
  const folder = node.templateName.replace(/ /g, '_')
  const state = node.state || 'Working'

  // Try different state name variations
  const possibleStates = [
    state,
    state.toLowerCase(),
    state.charAt(0).toUpperCase() + state.slice(1).toLowerCase(),
    'Working', // Default fallback
    'On',      // Alternative default
    'Off'      // Another alternative
  ]

  for (const stateName of possibleStates) {
    try {
      const path = getDeviceIconPath(folder, stateName)
      // In browser environment, we could check if image loads successfully
      // For now, return the path and let the browser handle broken images
      return path
    } catch (e) {
      continue
    }
  }

  // If all attempts fail, return a data URL with default SVG
  return `data:image/svg+xml;base64,${btoa(getDefaultDeviceIcon(node.templateName))}`
}
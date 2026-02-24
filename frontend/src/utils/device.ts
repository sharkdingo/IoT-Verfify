import type {
    BasicDeviceInfo,
    DeviceApiView,
    DeviceManifest,
    DeviceStateView,
    DeviceTemplate,
    DeviceVariableView
} from '../types/device'
import type { DeviceNode } from '../types/node'

// --- 设备状态管理 ---
// 存储所有设备实例的状态，key 是 deviceId，value 是当前状态
const deviceStates: Map<string, string> = new Map()

/**
 * 获取设备的状态
 * @param deviceId 设备实例的唯一标识
 * @param initState 设备的初始状态（从模板的 InitState 获取）
 * @returns 当前状态，如果未设置则返回初始状态
 */
export const getDeviceState = (deviceId: string, initState: string): string => {
    if (!deviceStates.has(deviceId)) {
        deviceStates.set(deviceId, initState)
    }
    return deviceStates.get(deviceId) || initState
}

/**
 * 更新设备状态
 * @param deviceId 设备实例的唯一标识
 * @param newState 新状态
 */
export const updateDeviceState = (deviceId: string, newState: string): void => {
    deviceStates.set(deviceId, newState)
}

/**
 * 根据 API 触发更新设备状态
 * @param deviceId 设备实例的唯一标识
 * @param apiName 触发的 API 名称
 * @param manifest 设备模板清单
 * @returns 是否成功更新状态
 */
export const updateDeviceStateByApi = (deviceId: string, apiName: string, manifest: DeviceManifest): boolean => {
    if (!manifest || !manifest.APIs) return false

    const api = manifest.APIs.find(a => a.Name === apiName)
    if (api && api.EndState) {
        updateDeviceState(deviceId, api.EndState)
        return true
    }
    return false
}

/**
 * 重置设备状态到初始状态
 * @param deviceId 设备实例的唯一标识
 * @param initState 设备的初始状态
 */
export const resetDeviceState = (deviceId: string, initState: string): void => {
    deviceStates.set(deviceId, initState)
}

/**
 * 清除设备状态（当设备被删除时调用）
 * @param deviceId 设备实例的唯一标识
 */
export const clearDeviceState = (deviceId: string): void => {
    deviceStates.delete(deviceId)
}

// --- 图标与路径 ---

/**
 * 获取设备图标的路径
 * @param folder 设备模板名称（转换为文件夹格式）
 * @param state 当前状态
 * @returns 图标的 URL 路径
 */
export const getDeviceIconPath = (folder: string, state: string) => {
    // 尝试不同的状态名称变体
    const possibleStates = [
        state,
        state.toLowerCase(),
        state.charAt(0).toUpperCase() + state.slice(1).toLowerCase(),
        // 对于多模式状态（如 "auto;auto"），尝试第一部分
        state.includes(';') ? state.split(';')[0] : null,
        state.includes(';') ? state.split(';')[0].toLowerCase() : null,
        // 默认状态
        'Working',
        'On',
        'Off'
    ].filter(Boolean) as string[]

    for (const stateName of possibleStates) {
        try {
            const path = new URL(`../assets/${folder}/${stateName}.svg`, import.meta.url).href
            return path
        } catch (e) {
            continue
        }
    }

    // 所有尝试都失败，返回一个占位符 SVG
    return `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="8" y="8" width="16" height="16" rx="2" fill="#94A3B8" stroke="#64748B" stroke-width="2"/>
      <circle cx="16" cy="16" r="4" fill="white"/>
    </svg>`
}

/**
 * 获取变量图标的路径
 * @param variableName 变量名称
 * @returns 图标的 URL 路径
 */
export const getVariableIconPath = (variableName: string) => {
    try {
        const path = new URL(`../assets/variables/${variableName}.svg`, import.meta.url).href
        return path
    } catch (e) {
        // 如果变量图标不存在，返回默认变量图标
        try {
            return new URL(`../assets/variables/temperature.svg`, import.meta.url).href
        } catch (e) {
            return ''
        }
    }
}

export const getNodeIcon = (node: DeviceNode, manifest?: DeviceManifest) => {
    const folder = node.templateName.replace(/ /g, '_')

    // 如果是变量节点（templateName 以 variable_ 开头），从 variables 文件夹获取图标
    if (node.templateName.startsWith('variable_')) {
        const variableName = node.templateName.replace('variable_', '')
        return getVariableIconPath(variableName)
    }

    // 如果传入了 manifest，优先使用状态管理
    if (manifest) {
        // 获取当前状态（优先使用状态管理的状态，否则使用 node 上的状态，否则使用初始状态）
        const currentState = node.state || manifest.InitState
        return getDeviceIconPath(folder, currentState)
    }

    // 兼容旧版：直接使用 node.state
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

  // If all attempts fail, return empty string
  return ''
}

// --- 默认设备图标 ---
// 注意：所有图标现在应该从 @frontend/src/assets 目录中获取
export const getDefaultDeviceIcon = (deviceType: string, initState?: string): string => {
  // 将设备类型名称转换为文件夹格式（使用下划线替换空格）
  const folder = deviceType.replace(/ /g, '_')
  
  // 使用传入的初始状态，如果没有则默认为 'Working'
  const state = initState || 'Working'
  const iconPath = getDeviceIconPath(folder, state)
  
  // 如果图标路径是有效的 SVG 字符串（占位符），直接返回
  if (iconPath.startsWith('<svg')) {
    return iconPath
  }
  
  // 返回包含图标的 img 标签
  return `<img src="${iconPath}" alt="${deviceType}" class="w-full h-full object-contain" />`
}
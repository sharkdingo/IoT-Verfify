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
    return getDeviceIconPath(folder, state)
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
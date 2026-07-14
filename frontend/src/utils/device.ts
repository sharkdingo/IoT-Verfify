import type {
    BasicDeviceInfo,
    DeviceApiView,
    DeviceManifest,
    DeviceStateView,
    DeviceTemplate,
    DeviceVariableView,
    InternalVariable
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
 * @param nextState 新状态
 */
export const updateDeviceState = (deviceId: string, nextState: string): void => {
    deviceStates.set(deviceId, nextState)
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

const deviceIconModules = import.meta.glob('../assets/*/*.svg', {
    eager: true,
    query: '?url',
    import: 'default'
}) as Record<string, string>

const variableIconModules = import.meta.glob('../assets/variables/*.svg', {
    eager: true,
    query: '?url',
    import: 'default'
}) as Record<string, string>

const normalizeAssetFolder = (name: string) =>
    String(name || 'Device').trim().replace(/\s+/g, '_')

const normalizeStateName = (state: string) => String(state || 'Working').trim()

const svgDataUri = (svg: string): string =>
    `data:image/svg+xml;charset=utf-8,${encodeURIComponent(svg)}`

const escapeXml = (value: string): string =>
    value
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')

const escapeAttr = (value: string): string =>
    value
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')

const hashString = (value: string): number => {
    let hash = 0
    for (let i = 0; i < value.length; i++) {
        hash = (hash * 31 + value.charCodeAt(i)) >>> 0
    }
    return hash
}

const getTemplateInitials = (name: string): string => {
    const words = String(name || 'Device')
        .replace(/[_-]+/g, ' ')
        .split(/\s+/)
        .filter(Boolean)

    const initials = words.length > 1
        ? words.slice(0, 2).map(word => word.charAt(0)).join('')
        : (words[0] || '?').slice(0, 2)

    return initials.toUpperCase()
}

const createGeneratedDeviceIcon = (deviceType: string, state?: string): string => {
    const name = String(deviceType || 'Device').replace(/_/g, ' ')
    const hash = hashString(name)
    const hue = hash % 360
    const accent = `hsl(${hue} 78% 52%)`
    const soft = `hsl(${hue} 88% 94%)`
    const mid = `hsl(${hue} 72% 72%)`
    const initials = escapeXml(getTemplateInitials(name))
    const stateLabel = escapeXml(normalizeStateName(state || '').slice(0, 14))
    const showState = stateLabel && stateLabel.toLowerCase() !== 'working'

    return svgDataUri(`
<svg width="72" height="72" viewBox="0 0 72 72" fill="none" xmlns="http://www.w3.org/2000/svg">
  <rect x="6" y="6" width="60" height="60" rx="16" fill="${soft}" stroke="${accent}" stroke-width="3"/>
  <rect x="18" y="18" width="36" height="27" rx="6" fill="white" stroke="${mid}" stroke-width="3"/>
  <path d="M25 28h22M25 35h16" stroke="${accent}" stroke-width="3" stroke-linecap="round"/>
  <circle cx="49" cy="51" r="8" fill="${accent}"/>
  <text x="36" y="59" text-anchor="middle" font-family="Inter, Arial, sans-serif" font-size="${showState ? 8 : 13}" font-weight="800" fill="#0f172a">${showState ? stateLabel : initials}</text>
</svg>`)
}

const getStateVariants = (state: string): string[] => {
    const cleanState = normalizeStateName(state)
    const variants = [
        cleanState,
        cleanState.toLowerCase(),
        cleanState.charAt(0).toUpperCase() + cleanState.slice(1).toLowerCase(),
        cleanState.includes(';') ? cleanState.split(';')[0] : '',
        cleanState.includes(';') ? cleanState.split(';')[0].toLowerCase() : '',
        'Working',
        'working',
        'On',
        'on',
        'Off',
        'off'
    ]

    return [...new Set(variants.filter(Boolean))]
}

const getBundledDeviceIconPath = (folder: string, state: string): string | null => {
    const normalizedFolder = normalizeAssetFolder(folder)

    for (const stateName of getStateVariants(state)) {
        const path = deviceIconModules[`../assets/${normalizedFolder}/${stateName}.svg`]
        if (path) return path
    }

    return null
}

const getFirstBundledDeviceIconPath = (folder: string): string | null => {
    const normalizedFolder = normalizeAssetFolder(folder)
    const prefix = `../assets/${normalizedFolder}/`
    const firstKey = Object.keys(deviceIconModules)
        .filter(key => key.startsWith(prefix))
        .sort((a, b) => a.localeCompare(b))
        .find(Boolean)

    return firstKey ? deviceIconModules[firstKey] : null
}

const isSafeManifestIcon = (icon: string | undefined | null): icon is string => {
    if (!icon || typeof icon !== 'string') return false
    const trimmed = icon.trim()
    if (trimmed.length === 0 || trimmed.length > 262144) return false

    return /^data:image\/(svg\+xml|png|jpe?g|webp|gif)(;[^,]+)?,/i.test(trimmed)
        || /^https:\/\//i.test(trimmed)
}

const getManifestIcon = (manifest?: DeviceManifest | null): string | null => {
    const icon = manifest?.Icon?.trim()
    return isSafeManifestIcon(icon) ? icon : null
}

export const getDeviceIconUrl = (
    deviceType: string,
    state: string = 'Working',
    manifest?: DeviceManifest | null
): string => {
    const manifestIcon = getManifestIcon(manifest)
    if (manifestIcon) return manifestIcon

    const folder = normalizeAssetFolder(deviceType)
    return getBundledDeviceIconPath(folder, state)
        || getFirstBundledDeviceIconPath(folder)
        || createGeneratedDeviceIcon(deviceType, state)
}

/**
 * 获取设备图标的路径
 * @param folder 设备模板名称（转换为文件夹格式）
 * @param state 当前状态
 * @returns 图标的 URL 路径
 */
export const getDeviceIconPath = (folder: string, state: string) => {
    return getBundledDeviceIconPath(folder, state)
        || getFirstBundledDeviceIconPath(folder)
        || createGeneratedDeviceIcon(folder.replace(/_/g, ' '), state)
}

/**
 * 获取变量图标的路径
 * @param variableName 变量名称
 * @returns 图标的 URL 路径
 */
export const getVariableIconPath = (variableName: string) => {
    return variableIconModules[`../assets/variables/${variableName}.svg`]
        || variableIconModules['../assets/variables/temperature.svg']
        || ''
}

export const getNodeIcon = (
    node: DeviceNode,
    manifestOrState?: DeviceManifest | string | null,
    stateOverride?: string
) => {
    const manifest = typeof manifestOrState === 'object' ? manifestOrState : null
    const explicitState = typeof manifestOrState === 'string' ? manifestOrState : stateOverride
    const currentState = explicitState || node.state || manifest?.InitState || 'Working'

    return getDeviceIconUrl(node.templateName, currentState, manifest)
}

// --- 状态查找 ---

export const getEndStateByApi = (
    templates: DeviceTemplate[],
    templateName: string,
    apiName: string
): string | null => {
    const tpl = templates.find(t => t.name === templateName)
    if (!tpl) return null
    const api = (tpl.manifest.APIs ?? []).find(a => a.Name === apiName)
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
                const definition = resolveImpactEnvironmentDefinition(manifest, name)
                const value = definition?.Values?.length
                    ? definition.Values.join(' / ')
                    : definition?.LowerBound !== undefined && definition?.UpperBound !== undefined
                        ? `[${definition.LowerBound}, ${definition.UpperBound}]`
                        : ''
                views.push({ name, value, trust: definition?.Trust ?? '' })
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
        description: ws.Description ?? '',
        trust: ws.Trust ?? ''
    }))
}

export const extractDeviceApis = (
    manifest: DeviceManifest | null | undefined
): DeviceApiView[] => {
    if (!manifest || !Array.isArray(manifest.APIs)) return []
    return manifest.APIs.map(api => ({
        name: api.Name,
        from: api.StartState ?? '',
        to: api.EndState,
        description: api.Description ?? ''
    }))
}

// --- 校验逻辑 ---

export const resolveImpactEnvironmentDefinition = (
    manifest: DeviceManifest | null | undefined,
    name: string
): InternalVariable | undefined => {
    const target = String(name || '').trim()
    if (!manifest || !target) return undefined
    const readable = manifest.InternalVariables?.find(variable =>
        variable?.Name === target && variable.IsInside !== true
    )
    if (readable) return readable
    const domain = manifest.EnvironmentDomains?.find(item => item?.Name === target)
    return domain ? {
        ...domain,
        IsInside: false,
        FalsifiableWhenCompromised: false
    } : undefined
}

export const validateManifest = (obj: any): { valid: boolean; msg?: string } => {
    if (!obj || typeof obj !== 'object') return { valid: false, msg: 'Invalid JSON object' }

    if (!obj.Name) return { valid: false, msg: 'Missing field "Name"' }

    for (const field of ['Modes', 'InternalVariables', 'EnvironmentDomains', 'ImpactedVariables', 'WorkingStates', 'Transitions', 'APIs', 'Contents']) {
        if (obj[field] !== undefined && !Array.isArray(obj[field])) {
            return { valid: false, msg: `"${field}" must be an array` }
        }
    }

    const hasModes = Array.isArray(obj.Modes) && obj.Modes.length > 0
    const hasInitState = typeof obj.InitState === 'string' && obj.InitState.trim() !== ''
    const hasWorkingStates = Array.isArray(obj.WorkingStates) && obj.WorkingStates.length > 0
    const validTrust = (value: unknown) => ['trusted', 'untrusted'].includes(String(value || '').trim().toLowerCase())
    const validPrivacy = (value: unknown) => ['public', 'private'].includes(String(value || '').trim().toLowerCase())

    if (hasModes || hasInitState || hasWorkingStates) {
        if (!hasModes) return { valid: false, msg: 'Mode-based templates must contain non-empty "Modes"' }
        if (!hasInitState) return { valid: false, msg: 'Mode-based templates must contain "InitState"' }
        if (!hasWorkingStates) return { valid: false, msg: 'Mode-based templates must contain non-empty "WorkingStates"' }
    }

    if (hasInitState && hasWorkingStates) {
        const initialState = obj.InitState.trim()
        const stateNames = obj.WorkingStates.map((s: any) => String(s?.Name || '').trim())
        if (!stateNames.includes(initialState)) {
            return { valid: false, msg: `InitState "${obj.InitState}" is not defined in WorkingStates` }
        }
    }

    if (hasModes && hasWorkingStates) {
        const normalizeStateComponent = (value: unknown) =>
            String(value || '').trim().replace(/ /g, '').toLowerCase()
        const fullStates = new Map<string, string>()
        const components = new Map<string, { fullState: string; trust: string; privacy: string }>()
        for (const state of obj.WorkingStates) {
            const rawState = String(state?.Name || '').trim()
            if (Object.prototype.hasOwnProperty.call(state || {}, 'Invariant')) {
                return {
                    valid: false,
                    msg: `WorkingState "${rawState}" uses unsupported Invariant; define behavior with structured Dynamics, Transitions, rules, or specifications`
                }
            }
            if (!validTrust(state?.Trust) || !validPrivacy(state?.Privacy)) {
                return {
                    valid: false,
                    msg: `WorkingState "${rawState}" must define Trust as trusted/untrusted and Privacy as public/private`
                }
            }
            const segments = rawState.split(';')
            if (segments.length !== obj.Modes.length) {
                return {
                    valid: false,
                    msg: `WorkingState "${rawState}" must contain one semicolon-separated value for each mode`
                }
            }
            const normalizedSegments = segments.map(normalizeStateComponent)
            const missingModeIndex = normalizedSegments.findIndex(segment => !segment || segment === '_')
            if (missingModeIndex >= 0) {
                return {
                    valid: false,
                    msg: `WorkingState "${rawState}" must define a concrete value for mode "${obj.Modes[missingModeIndex]}"`
                }
            }
            const fullStateKey = normalizedSegments.join(';')
            const previousFullState = fullStates.get(fullStateKey)
            if (previousFullState) {
                return {
                    valid: false,
                    msg: `WorkingStates "${previousFullState}" and "${rawState}" are duplicates after model normalization`
                }
            }
            fullStates.set(fullStateKey, rawState)

            const trust = String(state.Trust).trim().toLowerCase()
            const privacy = String(state.Privacy).trim().toLowerCase()
            for (let index = 0; index < obj.Modes.length; index += 1) {
                const componentKey = `${normalizeStateComponent(obj.Modes[index])}\u0000${normalizedSegments[index]}`
                const previous = components.get(componentKey)
                if (previous && (previous.trust !== trust || previous.privacy !== privacy)) {
                    return {
                        valid: false,
                        msg: `WorkingStates "${previous.fullState}" and "${rawState}" assign conflicting Trust/Privacy labels to ${obj.Modes[index]}="${segments[index].trim()}"`
                    }
                }
                components.set(componentKey, { fullState: rawState, trust, privacy })
            }
        }
    }

    const normalizedName = (value: unknown) => String(value || '').trim().toLowerCase()
    const internalNames = new Map<string, any>()
    for (const variable of obj.InternalVariables || []) {
        const name = normalizedName(variable?.Name)
        if (!name) return { valid: false, msg: 'Every InternalVariables item must contain Name' }
        if (internalNames.has(name)) return { valid: false, msg: `Duplicate InternalVariable "${variable.Name}"` }
        if (!validTrust(variable.Trust) || !validPrivacy(variable.Privacy)) {
            return {
                valid: false,
                msg: `InternalVariable "${variable.Name}" must define Trust as trusted/untrusted and Privacy as public/private`
            }
        }
        if (typeof variable.FalsifiableWhenCompromised !== 'boolean') {
            return { valid: false, msg: `InternalVariable "${variable.Name}" must define FalsifiableWhenCompromised` }
        }
        if (typeof variable.IsInside !== 'boolean') {
            return { valid: false, msg: `InternalVariable "${variable.Name}" must explicitly define IsInside as true (device-local) or false (shared environment)` }
        }
        const hasValues = Array.isArray(variable.Values) && variable.Values.length > 0
        const hasLower = Number.isInteger(variable.LowerBound)
        const hasUpper = Number.isInteger(variable.UpperBound)
        if (hasValues === (hasLower && hasUpper) || hasLower !== hasUpper) {
            return { valid: false, msg: `InternalVariable "${variable.Name}" must explicitly define Values or LowerBound+UpperBound` }
        }
        internalNames.set(name, variable)
    }

    const domainNames = new Map<string, any>()
    for (const domain of obj.EnvironmentDomains || []) {
        const name = normalizedName(domain?.Name)
        if (!name) return { valid: false, msg: 'Every EnvironmentDomains item must contain Name' }
        if (domainNames.has(name)) return { valid: false, msg: `Duplicate EnvironmentDomain "${domain.Name}"` }
        if (internalNames.has(name)) {
            return { valid: false, msg: `EnvironmentDomain "${domain.Name}" duplicates an InternalVariable` }
        }
        if (!validTrust(domain.Trust) || !validPrivacy(domain.Privacy)) {
            return {
                valid: false,
                msg: `EnvironmentDomain "${domain.Name}" must define Trust as trusted/untrusted and Privacy as public/private`
            }
        }
        const hasValues = Array.isArray(domain.Values) && domain.Values.length > 0
        const hasLower = Number.isInteger(domain.LowerBound)
        const hasUpper = Number.isInteger(domain.UpperBound)
        if (hasValues === (hasLower && hasUpper) || hasLower !== hasUpper) {
            return { valid: false, msg: `EnvironmentDomain "${domain.Name}" must define Values or LowerBound+UpperBound` }
        }
        domainNames.set(name, domain)
    }

    const impactedNames = new Set<string>()
    for (const rawName of obj.ImpactedVariables || []) {
        const name = normalizedName(rawName)
        if (!name) return { valid: false, msg: 'ImpactedVariables cannot contain an empty name' }
        if (impactedNames.has(name)) return { valid: false, msg: `Duplicate ImpactedVariable "${rawName}"` }
        impactedNames.add(name)
        const variable = internalNames.get(name)
        if (variable?.IsInside === true) {
            return { valid: false, msg: `ImpactedVariable "${rawName}" conflicts with a device-local InternalVariable` }
        }
        if (!variable && !domainNames.has(name)) {
            return { valid: false, msg: `ImpactedVariable "${rawName}" needs a domain in this manifest` }
        }
    }
    for (const [name, domain] of domainNames) {
        if (!impactedNames.has(name)) {
            return { valid: false, msg: `EnvironmentDomain "${domain.Name}" is not listed in ImpactedVariables` }
        }
    }

    for (const content of obj.Contents || []) {
        const name = String(content?.Name || '').trim()
        if (!name) return { valid: false, msg: 'Every Contents item must contain Name' }
        if (!validPrivacy(content?.Privacy)) {
            return { valid: false, msg: `Content "${name}" must define Privacy as public/private` }
        }
    }

    for (const transition of obj.Transitions || []) {
        const name = String(transition?.Name || '').trim() || '<unnamed>'
        if (Object.prototype.hasOwnProperty.call(transition || {}, 'Signal')) {
            return {
                valid: false,
                msg: `Transition "${name}" uses unsupported Signal; event pulses are available only on state-changing APIs with Signal=true`
            }
        }
    }

    for (const api of obj.APIs || []) {
        const name = String(api?.Name || '').trim() || '<unnamed>'
        if (typeof api?.StartState !== 'string') {
            return {
                valid: false,
                msg: `API "${name}" must explicitly define StartState (use an empty string for any state)`
            }
        }
        if (typeof api?.Signal !== 'boolean') {
            return {
                valid: false,
                msg: `API "${name}" must explicitly define boolean Signal (true = observable automation trigger; false = command only)`
            }
        }
        if (api?.AcceptsContent !== undefined && typeof api.AcceptsContent !== 'boolean') {
            return {
                valid: false,
                msg: `API "${name}" AcceptsContent must be boolean when provided`
            }
        }
    }

    return { valid: true }
}

// --- 增强版图标获取函数 ---
export const getNodeIconWithFallback = (node: DeviceNode): string => {
  return getNodeIcon(node)
}

// --- 默认设备图标 ---
// 注意：所有图标现在应该从 @frontend/src/assets 目录中获取
export const getDefaultDeviceIcon = (
  deviceType: string,
  initState?: string,
  manifest?: DeviceManifest | null
): string => {
  const iconPath = getDeviceIconUrl(deviceType, initState || 'Working', manifest)
  return `<img src="${escapeAttr(iconPath)}" alt="${escapeAttr(deviceType)}" class="w-full h-full object-contain" />`
}

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
    // ===== 传感器类 =====
    'Temperature Sensor': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="11" fill="#3B82F6" stroke="#1D4ED8" stroke-width="2"/>
      <path d="M16 9v5c0 2.5 2 4.5 4.5 5.5" stroke="white" stroke-width="2" stroke-linecap="round"/>
      <circle cx="16" cy="13" r="2" fill="#FCD34D"/>
    </svg>`,
    'Humidity Sensor': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <path d="M16 6c-5.5 0-10 4.5-10 10 0 5.5 4.5 10 10 10s10-4.5 10-10c0-5.5-4.5-10-10-10z" fill="#06B6D4" stroke="#0891B2" stroke-width="2"/>
      <path d="M12 18c0-2 1.5-3 4-3s4 1 4 3" stroke="white" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Illuminance Sensor': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="11" fill="#FBBF24" stroke="#D97706" stroke-width="2"/>
      <circle cx="16" cy="16" r="5" fill="white"/>
      <path d="M16 3v2M16 27v2M3 16h2M27 16h2M7 7l1.5 1.5M23.5 23.5l1.5 1.5M7 25l1.5-1.5M23.5 9l1.5-1.5" stroke="#FBBF24" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Gas Sensor': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="11" fill="#EF4444" stroke="#B91C1C" stroke-width="2"/>
      <path d="M13 12h6v2h-6zM13 16h6v2h-6zM13 20h6v2h-6z" fill="white"/>
    </svg>`,
    'Smoke Sensor': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="11" fill="#94A3B8" stroke="#64748B" stroke-width="2"/>
      <circle cx="16" cy="12" r="3" fill="white"/>
      <path d="M12 18c0 2 2 4 4 4s4-2 4-4" fill="white"/>
    </svg>`,
    'Motion Detector': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="11" fill="#8B5CF6" stroke="#6D28D9" stroke-width="2"/>
      <path d="M10 16h4M18 16h4M16 10v4M16 18v4" stroke="white" stroke-width="2" stroke-linecap="round"/>
      <circle cx="16" cy="16" r="3" fill="#FCD34D"/>
    </svg>`,
    'Soil Moisture Sensor': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="8" y="8" width="16" height="16" rx="2" fill="#92400E" stroke="#78350F" stroke-width="2"/>
      <path d="M12 14c0-1.5 1.5-2 4-2s4 0.5 4 2" stroke="#3B82F6" stroke-width="2" stroke-linecap="round"/>
      <path d="M14 18c0 1 1 2 2 2s2-1 2-2" stroke="#22C55E" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Electricity Meter Sensor': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="6" y="8" width="20" height="16" rx="2" fill="#3B82F6" stroke="#1D4ED8" stroke-width="2"/>
      <circle cx="16" cy="16" r="4" fill="white"/>
      <path d="M16 13v3l2 2" stroke="#3B82F6" stroke-width="1.5" stroke-linecap="round"/>
    </svg>`,
    'Swimming Pool Water Quality Sensor': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="11" fill="#06B6D4" stroke="#0891B2" stroke-width="2"/>
      <path d="M10 14c2 2 6 2 8 0M12 18c1.5 1.5 4.5 1.5 6 0" stroke="white" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Refrigerator Door Sensor': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="8" y="6" width="16" height="20" rx="2" fill="#F8FAFC" stroke="#94A3B8" stroke-width="2"/>
      <path d="M16 6v20" stroke="#94A3B8" stroke-width="2"/>
      <circle cx="16" cy="12" r="1.5" fill="#64748B"/>
    </svg>`,

    // ===== 照明类 =====
    'Light': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <path d="M16 4v6M8 12l4 4M24 12l-4 4M12 20l4 4M20 20l-4 4" stroke="#F59E0B" stroke-width="2" stroke-linecap="round"/>
      <circle cx="16" cy="14" r="6" fill="#F59E0B" stroke="#D97706" stroke-width="2"/>
    </svg>`,

    // ===== 空调暖通类 =====
    'Air Conditioner': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="4" y="8" width="24" height="16" rx="2" fill="#0EA5E9" stroke="#0284C7" stroke-width="2"/>
      <path d="M8 14h4M8 18h4M12 14v4" stroke="white" stroke-width="2" stroke-linecap="round"/>
      <path d="M20 14v4h4" stroke="white" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>
    </svg>`,
    'Thermostat': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="11" fill="#F97316" stroke="#EA580C" stroke-width="2"/>
      <circle cx="16" cy="16" r="6" fill="white"/>
      <path d="M16 12v4l2.5 2.5" stroke="#F97316" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Humidifier': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="10" y="12" width="12" height="12" rx="2" fill="#0EA5E9" stroke="#0284C7" stroke-width="2"/>
      <path d="M14 8v4M18 8v4M16 6v6" stroke="#0EA5E9" stroke-width="2" stroke-linecap="round"/>
      <circle cx="16" cy="22" r="1" fill="white"/>
    </svg>`,
    'Air Purifier': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="6" y="10" width="20" height="14" rx="2" fill="#22C55E" stroke="#16A34A" stroke-width="2"/>
      <circle cx="16" cy="17" r="4" fill="white"/>
      <path d="M12 17h8M16 13v8" stroke="#22C55E" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Air Quality Monitor': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="6" y="8" width="20" height="16" rx="2" fill="#22C55E" stroke="#16A34A" stroke-width="2"/>
      <circle cx="12" cy="14" r="2" fill="white"/>
      <circle cx="16" cy="14" r="2" fill="white"/>
      <circle cx="20" cy="14" r="2" fill="white"/>
      <circle cx="12" cy="19" r="2" fill="white"/>
      <circle cx="16" cy="19" r="2" fill="#FCD34D"/>
      <circle cx="20" cy="19" r="2" fill="white"/>
    </svg>`,
    'Ventilator': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="11" fill="#64748B" stroke="#475569" stroke-width="2"/>
      <circle cx="16" cy="16" r="3" fill="white"/>
      <path d="M16 5v3M16 24v3M5 16h3M24 16h3M8 8l2 2M22 22l2 2M8 24l2-2M22 8l2-2" stroke="#64748B" stroke-width="2" stroke-linecap="round"/>
    </svg>`,

    // ===== 门窗类 =====
    'Window': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="6" y="8" width="20" height="16" rx="1" fill="#0EA5E9" stroke="#0284C7" stroke-width="2"/>
      <path d="M16 8v16M6 16h20" stroke="white" stroke-width="2"/>
    </svg>`,
    'Window Shade': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="6" y="6" width="20" height="20" rx="1" fill="#F8FAFC" stroke="#94A3B8" stroke-width="2"/>
      <path d="M6 10h20M6 14h20M6 18h20M6 22h20" stroke="#CBD5E1" stroke-width="1"/>
    </svg>`,
    'Door': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="8" y="4" width="14" height="24" rx="1" fill="#92400E" stroke="#78350F" stroke-width="2"/>
      <circle cx="19" cy="16" r="2" fill="#FCD34D"/>
    </svg>`,
    'Door RFID': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="8" y="4" width="14" height="24" rx="1" fill="#3B82F6" stroke="#1D4ED8" stroke-width="2"/>
      <rect x="11" y="8" width="8" height="10" rx="1" fill="white"/>
      <circle cx="15" cy="13" r="1.5" fill="#3B82F6"/>
      <path d="M12 16h4M12 18h4" stroke="#3B82F6" stroke-width="1" stroke-linecap="round"/>
    </svg>`,
    'Garage Door': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="4" y="6" width="24" height="20" rx="2" fill="#6B7280" stroke="#4B5563" stroke-width="2"/>
      <path d="M4 10h24M4 14h24M4 18h24M4 22h24" stroke="#4B5563" stroke-width="2"/>
    </svg>`,

    // ===== 厨房电器类 =====
    'Washer Machine': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="6" y="6" width="20" height="20" rx="2" fill="#F8FAFC" stroke="#94A3B8" stroke-width="2"/>
      <circle cx="16" cy="16" r="6" fill="#3B82F6" stroke="#1D4ED8" stroke-width="2"/>
      <circle cx="16" cy="16" r="2" fill="white"/>
    </svg>`,
    'Dryer': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="6" y="8" width="20" height="16" rx="2" fill="#F8FAFC" stroke="#94A3B8" stroke-width="2"/>
      <circle cx="16" cy="16" r="5" fill="none" stroke="#F97316" stroke-width="2"/>
      <path d="M13 16h6M16 13v6" stroke="#F97316" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Oven': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="4" y="8" width="24" height="16" rx="2" fill="#4B5563" stroke="#374151" stroke-width="2"/>
      <rect x="8" y="12" width="16" height="8" rx="1" fill="#1F2937"/>
      <circle cx="20" cy="20" r="1.5" fill="#FCD34D"/>
    </svg>`,
    'Range Hood': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <path d="M6 12h20v2H6z" fill="#6B7280" stroke="#4B5563" stroke-width="2"/>
      <path d="M10 14v10M22 14v10" stroke="#4B5563" stroke-width="2"/>
      <path d="M8 24h16" stroke="#4B5563" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Coffee Maker': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="8" y="14" width="16" height="10" rx="1" fill="#92400E" stroke="#78350F" stroke-width="2"/>
      <path d="M12 14V8c0-1 2-2 4-2s4 1 4 2v6" stroke="#78350F" stroke-width="2"/>
      <rect x="12" y="18" width="8" height="4" rx="1" fill="#F8FAFC"/>
    </svg>`,
    'Cooker': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="6" y="10" width="20" height="14" rx="2" fill="#374151" stroke="#1F2937" stroke-width="2"/>
      <circle cx="11" cy="17" r="3" fill="#EF4444"/>
      <circle cx="21" cy="17" r="3" fill="#22C55E"/>
      <rect x="9" y="6" width="14" height="4" rx="1" fill="#4B5563"/>
    </svg>`,
    'Refrigerator': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="6" y="4" width="20" height="24" rx="2" fill="#F8FAFC" stroke="#94A3B8" stroke-width="2"/>
      <path d="M6 14h20" stroke="#94A3B8" stroke-width="2"/>
      <circle cx="22" cy="9" r="1.5" fill="#64748B"/>
    </svg>`,
    'Water Heater': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="10" y="6" width="12" height="20" rx="6" fill="#EF4444" stroke="#B91C1C" stroke-width="2"/>
      <path d="M14 12h4M14 16h4M14 20h4" stroke="white" stroke-width="2" stroke-linecap="round"/>
    </svg>`,

    // ===== 其他设备类 =====
    'Clock': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="11" fill="#F8FAFC" stroke="#64748B" stroke-width="2"/>
      <circle cx="16" cy="16" r="8" fill="none" stroke="#CBD5E1" stroke-width="1"/>
      <path d="M16 8v8l4 4" stroke="#4B5563" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>
    </svg>`,
    'Calendar': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="4" y="6" width="24" height="20" rx="2" fill="#F8FAFC" stroke="#64748B" stroke-width="2"/>
      <path d="M4 12h24" stroke="#64748B" stroke-width="2"/>
      <rect x="8" y="4" width="16" height="4" fill="#3B82F6"/>
    </svg>`,
    'Camera': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="4" y="10" width="24" height="14" rx="2" fill="#8B5CF6" stroke="#7C3AED" stroke-width="2"/>
      <circle cx="16" cy="17" r="4" fill="white"/>
      <circle cx="16" cy="17" r="2" fill="#8B5CF6"/>
      <path d="M10 10V8h4v2M18 10V8h4v2" stroke="#8B5CF6" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Alarm': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <path d="M16 4l12 20H4L16 4z" fill="#EF4444" stroke="#B91C1C" stroke-width="2"/>
      <circle cx="16" cy="18" r="3" fill="white"/>
      <path d="M14 26h4" stroke="#EF4444" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Mobile Phone': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="10" y="4" width="12" height="24" rx="2" fill="#4B5563" stroke="#374151" stroke-width="2"/>
      <circle cx="16" cy="25" r="1.5" fill="#6B7280"/>
      <rect x="13" y="7" width="6" height="8" rx="1" fill="white"/>
    </svg>`,
    'Car': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <path d="M6 16l3-6h14l3 6v4H6v-4z" fill="#3B82F6" stroke="#1D4ED8" stroke-width="2"/>
      <circle cx="10" cy="22" r="3" fill="#374151"/>
      <circle cx="22" cy="22" r="3" fill="#374151"/>
      <path d="M4 16h4M24 16h4" stroke="#3B82F6" stroke-width="2"/>
    </svg>`,
    'TV': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="2" y="6" width="28" height="18" rx="2" fill="#1F2937" stroke="#111827" stroke-width="2"/>
      <rect x="4" y="8" width="24" height="14" rx="1" fill="#3B82F6"/>
      <path d="M8 26v2h16v-2" stroke="#374151" stroke-width="2"/>
    </svg>`,
    'Home Mode': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <path d="M16 6L4 14v12h24V14L16 6z" fill="#F59E0B" stroke="#D97706" stroke-width="2"/>
      <path d="M11 20h10M16 15v5" stroke="white" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Weather': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="14" r="6" fill="#FCD34D" stroke="#D97706" stroke-width="2"/>
      <path d="M8 24c0-4 3-8 8-8s8 4 8 8" fill="#3B82F6" stroke="#1D4ED8" stroke-width="2"/>
    </svg>`,

    // ===== 户外设备类 =====
    'Swimming Pool Water Pump': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="8" y="12" width="16" height="12" rx="2" fill="#06B6D4" stroke="#0891B2" stroke-width="2"/>
      <circle cx="13" cy="18" r="3" fill="white"/>
      <path d="M19 15l3 3M19 21l3-3" stroke="white" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Sprinkler Controller': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="6" y="8" width="20" height="16" rx="2" fill="#22C55E" stroke="#16A34A" stroke-width="2"/>
      <circle cx="16" cy="16" r="4" fill="white"/>
      <path d="M16 12v-2M16 22v-2M12 16h-2M22 16h-2" stroke="#22C55E" stroke-width="2" stroke-linecap="round"/>
    </svg>`,

    // ===== 社交/通讯类 =====
    'Twitter': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="11" fill="#1DA1F2" stroke="#0D8BD9" stroke-width="2"/>
      <path d="M22 12c-2 1.5-5 2-7 1M10 20c2-1.5 5-2 7-1M12 14l2 2M20 14l-2 2M16 10l-2 6" stroke="white" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Facebook': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="11" fill="#1877F2" stroke="#0D65D9" stroke-width="2"/>
      <path d="M20 16h-4M16 12v8M18 12v-2a2 2 0 00-2-2h-2" stroke="white" stroke-width="2" stroke-linecap="round"/>
    </svg>`,
    'Sina Weibo': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="11" fill="#E6162D" stroke="#C41020" stroke-width="2"/>
      <path d="M12 14c2 0 4 1 5 3M14 18c-1-2 0-4 2-4M20 14c-2 1-3 3-2 5" stroke="white" stroke-width="1.5" stroke-linecap="round"/>
      <circle cx="11" cy="17" r="1" fill="white"/>
    </svg>`,
    'Email': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="4" y="8" width="24" height="16" rx="2" fill="#3B82F6" stroke="#1D4ED8" stroke-width="2"/>
      <path d="M4 12l12 8 12-8" stroke="white" stroke-width="2"/>
    </svg>`,
    'Online Bank': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="4" y="10" width="24" height="14" rx="2" fill="#10B981" stroke="#059669" stroke-width="2"/>
      <path d="M4 16h24M10 14v6M16 14v6M22 14v6" stroke="white" stroke-width="2"/>
    </svg>`,

    // ===== 旧模板兼容 =====
    'Sensor': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <circle cx="16" cy="16" r="12" fill="#3B82F6" stroke="#1E40AF" stroke-width="2"/>
      <path d="M16 8v8l6 4" stroke="white" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>
    </svg>`,
    'Switch': `<svg width="32" height="32" viewBox="0 0 32 32" fill="none" xmlns="http://www.w3.org/2000/svg">
      <rect x="8" y="12" width="16" height="8" rx="4" fill="#10B981" stroke="#059669" stroke-width="2"/>
      <circle cx="20" cy="16" r="3" fill="white"/>
    </svg>`
  }

  return defaultIcons[deviceType] || defaultIcons['Sensor']
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
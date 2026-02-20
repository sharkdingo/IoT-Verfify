export interface SourceEntry {
    fromId: string  // 设备ID（仅设备API类型需要）
    fromApi: string  // API名称或变量名称
    // 区分来源类型：device=设备API触发，globalVariable=全局变量触发
    sourceType?: 'device' | 'globalVariable'
    // 兼容旧字段：itemType 用于区分 API 和变量（设备内部变量）
    itemType?: 'api' | 'variable'
    // 后端返回的字段名
    targetType?: 'api' | 'variable'
    // 条件关系和值（仅变量类型需要）
    relation?: string
    value?: string
}

// 全局变量列表（从设备模板的 ImpactedVariables 提取）
export const GLOBAL_VARIABLES = [
    { name: 'temperature', label: '温度 (Temperature)', unit: '°C' },
    { name: 'humidity', label: '湿度 (Humidity)', unit: '%' },
    { name: 'airQuality', label: '空气质量 (Air Quality)', unit: '' },
    { name: 'carbonDioxide', label: '二氧化碳 (CO₂)', unit: 'ppm' },
    { name: 'illuminance', label: '光照强度 (Illuminance)', unit: 'lux' },
    { name: 'contact', label: '门/窗状态 (Contact)', unit: '' },
    { name: 'waterTemperature', label: '水温 (Water Temperature)', unit: '°C' },
    { name: 'waterQuality', label: '水质 (Water Quality)', unit: '' }
] as const

export type GlobalVariableName = typeof GLOBAL_VARIABLES[number]['name']

export interface RuleForm {
    id?: string  // 可选，添加新规则时由前端生成
    name?: string // 规则名称
    // 多个源条目，每个源有自己的 API
    sources: SourceEntry[]
    toId: string
    toApi: string
}

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

export interface RuleForm {
    id?: string  // 可选，添加新规则时由前端生成
    name?: string // 规则名称
    // 多个源条目，每个源有自己的 API
    sources: SourceEntry[]
    toId: string
    toApi: string
}

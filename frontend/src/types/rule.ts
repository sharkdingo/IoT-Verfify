export interface SourceEntry {
    fromId: string
    fromApi: string
    itemType?: 'api' | 'variable'  // 区分 API 和变量
    targetType?: 'api' | 'variable'  // 后端返回的字段名
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

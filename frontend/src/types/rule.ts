export interface SourceEntry {
    fromId: string
    fromApi: string
}

export interface RuleForm {
    id?: string  // 可选，添加新规则时由前端生成
    // 多个源条目，每个源有自己的 API
    sources: SourceEntry[]
    toId: string
    toApi: string
}


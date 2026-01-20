export interface SourceEntry {
    fromId: string
    fromApi: string
}

export interface RuleForm {
    // 多个源条目，每个源有自己的 API
    sources: SourceEntry[]
    toId: string
    toApi: string
}

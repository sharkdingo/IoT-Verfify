export interface DeviceEdge {
    id: string
    from: string
    to: string
    fromLabel: string
    toLabel: string
    fromPos: { x: number; y: number }
    toPos: { x: number; y: number }
    // 动态添加的字段，用于规则显示
    fromApi?: string
    toApi?: string
    itemType?: 'api' | 'variable'
    relation?: string
    value?: string
}

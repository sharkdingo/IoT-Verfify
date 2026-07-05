export interface DeviceEdge {
    id: string
    from: string
    to: string
    fromLabel: string
    toLabel: string
    fromPos: { x: number; y: number }
    toPos: { x: number; y: number }
    // Rule-derived display metadata. These fields are not part of the backend
    // DeviceEdgeDto; boardApi.saveEdges strips them before sending edge payloads.
    fromApi?: string
    toApi?: string
    itemType?: 'api' | 'variable'
    relation?: string
    value?: string
}

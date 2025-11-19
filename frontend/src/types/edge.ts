export interface DeviceEdge {
    id: string
    from: string
    to: string
    fromLabel: string
    toLabel: string
    fromApi: string
    toApi: string
    fromPos: { x: number; y: number }
    toPos: { x: number; y: number }
}

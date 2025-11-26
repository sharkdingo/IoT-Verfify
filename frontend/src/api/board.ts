// src/api/board.ts
import api from './http'   // 你已有 http.ts：axios.create(...)

import type { DeviceNode } from '@/types/node'
import type { DeviceEdge } from '@/types/edge'
import type { Specification } from '@/types/spec'
import type { PanelActive } from '@/types/panel'
import type { CanvasPan } from '@/types/canvas'

export interface BoardLayoutDto {
    input: { x: number; y: number }
    status: { x: number; y: number }
    canvasPan: CanvasPan
    canvasZoom: number
}

export default {
    // ==== 节点 ====
    getNodes: () => api.get<DeviceNode[]>('/board/nodes'),
    saveNodes: (nodes: DeviceNode[]) => api.post('/board/nodes', nodes),

    // ==== 连线 ====
    getEdges: () => api.get<DeviceEdge[]>('/board/edges'),
    saveEdges: (edges: DeviceEdge[]) => api.post('/board/edges', edges),

    // ==== 规约 ====
    getSpecs: () => api.get<Specification[]>('/board/specs'),
    saveSpecs: (specs: Specification[]) => api.post('/board/specs', specs),

    // ==== 布局（panel + canvas） ====
    getLayout: () => api.get<BoardLayoutDto>('/board/layout'),
    saveLayout: (dto: BoardLayoutDto) => api.post('/board/layout', dto),

    // ==== 折叠面板 ====
    getActive: () => api.get<PanelActive>('/board/active'),
    saveActive: (active: PanelActive) => api.post('/board/active', active)
}

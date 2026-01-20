// src/api/board.ts
import api from './http'   // 你已有 http.ts：axios.create(...)

// 引入类型
import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { Specification } from '../types/spec'
import type { BoardLayoutDto, PanelActive } from '../types/panel'
import { DeviceTemplate } from "@/types/device.ts";

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
    // ==== 规则（sources -> target） ====
    getRules: () => api.get<RuleDto[]>('/board/rules'),
    saveRules: (rules: RuleDto[]) => api.post('/board/rules', rules),

    // ==== 布局（包含 Panel 位置、停靠状态、Canvas 缩放位移） ====
    getLayout: () => api.get<BoardLayoutDto>('/board/layout'),
    saveLayout: (dto: BoardLayoutDto) => api.post('/board/layout', dto),

    // ==== 折叠面板（展开/收起的内容项） ====
    getActive: () => api.get<PanelActive>('/board/active'),
    saveActive: (active: PanelActive) => api.post('/board/active', active),

    // ==== 设备模板 ====
    getDeviceTemplates: () => api.get<DeviceTemplate[]>('/board/templates'),
    addDeviceTemplate: (tpl: DeviceTemplate) => api.post('/board/templates', tpl)
}
// src/api/board.ts - Board API（自动解包Result<T>）
import api from './http';

// 引入类型
import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { Specification } from '../types/spec'
import type { BoardLayoutDto, PanelActive } from '../types/panel'
import type { RuleForm } from '../types/rule'
import type { DeviceTemplate } from '@/types/device'

// 辅助函数：解包Result（后端返回 { code, message, data }）
const unpack = <T>(response: any): T => {
  return response.data.data;
};

export default {
    // ==== 节点 ====
    getNodes: async (): Promise<DeviceNode[]> => {
        return unpack<DeviceNode[]>(await api.get('/board/nodes'));
    },
    saveNodes: async (nodes: DeviceNode[]): Promise<DeviceNode[]> => {
        return unpack<DeviceNode[]>(await api.post('/board/nodes', nodes));
    },

    // ==== 连线 ====
    getEdges: async (): Promise<DeviceEdge[]> => {
        return unpack<DeviceEdge[]>(await api.get('/board/edges'));
    },
    saveEdges: async (edges: DeviceEdge[]): Promise<DeviceEdge[]> => {
        return unpack<DeviceEdge[]>(await api.post('/board/edges', edges));
    },

    // ==== 规约 ====
    getSpecs: async (): Promise<Specification[]> => {
        return unpack<Specification[]>(await api.get('/board/specs'));
    },
    saveSpecs: async (specs: Specification[]): Promise<Specification[]> => {
        return unpack<Specification[]>(await api.post('/board/specs', specs));
    },

    // ==== 规则（sources -> target） ====
    getRules: async (): Promise<RuleForm[]> => {
        return unpack<RuleForm[]>(await api.get('/board/rules'));
    },
    saveRules: async (rules: RuleForm[]): Promise<RuleForm[]> => {
        return unpack<RuleForm[]>(await api.post('/board/rules', rules));
    },

    // ==== 布局（包含 Panel 位置、停靠状态、Canvas 缩放位移） ====
    getLayout: async (): Promise<BoardLayoutDto> => {
        return unpack<BoardLayoutDto>(await api.get('/board/layout'));
    },
    saveLayout: async (dto: BoardLayoutDto): Promise<BoardLayoutDto> => {
        return unpack<BoardLayoutDto>(await api.post('/board/layout', dto));
    },

    // ==== 折叠面板（展开/收起的内容项） ====
    getActive: async (): Promise<PanelActive> => {
        return unpack<PanelActive>(await api.get('/board/active'));
    },
    saveActive: async (active: PanelActive): Promise<PanelActive> => {
        return unpack<PanelActive>(await api.post('/board/active', active));
    },

    // ==== 设备模板 ====
    getDeviceTemplates: async (): Promise<DeviceTemplate[]> => {
        return unpack<DeviceTemplate[]>(await api.get('/board/templates'));
    },
    addDeviceTemplate: async (tpl: DeviceTemplate): Promise<DeviceTemplate> => {
        return unpack<DeviceTemplate>(await api.post('/board/templates', tpl));
    }
}

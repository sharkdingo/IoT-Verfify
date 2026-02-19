// src/api/board.ts - Board API（自动解包Result<T>）
import api from './http';

// 引入类型
import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { Specification } from '../types/spec'
import type { BoardLayoutDto } from '../types/canvas'
import type { PanelActive } from '../types/panel'
import type { RuleForm } from '../types/rule'
import type { DeviceTemplate } from '@/types/device'
import type { VerificationRequest, VerificationResult, VerificationTask } from '@/types/verify'

// 辅助函数：解包Result（后端返回 { code, message, data }）
const unpack = <T>(response: any): T => {
  return response.data.data;
};

// 后端 DeviceEdgeDto 接口（用于 API 通信）
interface BackendEdgeDto {
    id: string
    from: string
    to: string
    fromLabel: string
    toLabel: string
    fromPos: { x: number; y: number }
    toPos: { x: number; y: number }
    // 规则相关的字段
    fromApi?: string
    toApi?: string
    itemType?: 'api' | 'variable'
    relation?: string
    value?: string
}

// 后端 RuleDto 接口（用于 API 通信）
interface BackendRuleDto {
    id: number | null
    conditions: Array<{
        deviceName: string
        attribute: string
        relation: string
        value: string
    }>
    command: {
        deviceName: string
        action: string
        contentDevice: string | null
        content: string | null
    }
    ruleString: string
}

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
        const data = await unpack<BackendEdgeDto[]>(await api.get('/board/edges'));
        return data.map((edge: BackendEdgeDto) => ({
            id: edge.id || '',
            from: edge.from || '',
            to: edge.to || '',
            fromLabel: edge.fromLabel || '',
            toLabel: edge.toLabel || '',
            fromPos: edge.fromPos || { x: 0, y: 0 },
            toPos: edge.toPos || { x: 0, y: 0 },
            // 映射规则相关的字段，用于从连线恢复规则数据
            fromApi: edge.fromApi || '',
            toApi: edge.toApi || '',
            itemType: edge.itemType as 'api' | 'variable' | undefined,
            relation: edge.relation || '',
            value: edge.value || ''
        }));
    },
    saveEdges: async (edges: DeviceEdge[]): Promise<DeviceEdge[]> => {
        // 转换为后端 DTO，确保所有必填字段都有值（不能为空字符串或null）
        const edgeDtos: BackendEdgeDto[] = edges.map(edge => {
            // 安全获取坐标值
            const getPos = (pos?: { x?: number; y?: number }) => ({
                x: (pos?.x !== undefined ? pos.x : 0) as number,
                y: (pos?.y !== undefined ? pos.y : 0) as number
            });

            const dto = {
                id: edge.id || 'edge_' + Date.now() + '_' + Math.random().toString(36).substr(2, 9),
                from: String(edge.from || 'unknown'),
                to: String(edge.to || 'unknown'),
                fromLabel: String(edge.fromLabel || 'Unknown'),
                toLabel: String(edge.toLabel || 'Unknown'),
                fromPos: getPos(edge.fromPos),
                toPos: getPos(edge.toPos)
            };
            return dto;
        });
        return unpack<DeviceEdge[]>(await api.post('/board/edges', edgeDtos));
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
        const data = await unpack<BackendRuleDto[]>(await api.get('/board/rules'));
        return data.map((rule: BackendRuleDto) => ({
            id: rule.id ? `rule_${rule.id}` : '',
            name: rule.ruleString || '',
            sources: (rule.conditions && rule.conditions.length > 0) 
                ? rule.conditions.map((c) => ({
                    fromId: c.deviceName || '',
                    fromApi: c.attribute || '',
                    // 如果有 relation 和 value，设置类型为 variable，否则为 api
                    targetType: (c.relation && c.value) ? 'variable' : 'api',
                    relation: c.relation || 'EQ',
                    value: c.value || 'true'
                }))
                : [],
            toId: rule.command?.deviceName || '',
            toApi: rule.command?.action || ''
        }));
    },
    saveRules: async (rules: RuleForm[]): Promise<RuleForm[]> => {
        // 转换为后端 DTO，确保所有必填字段都有值
        const ruleDtos: BackendRuleDto[] = rules.map(rule => {
            // 对于新创建的规则（id 以 rule_ 开头），不发送 id，让后端自动生成
            let id: number | null = null;
            if (rule.id && rule.id.startsWith('rule_')) {
                // 新创建的规则，不传 id，或者传 null
                // 如果要支持更新已有规则，需要从数据库加载现有规则并比对
                id = null;
            } else if (rule.id) {
                // 已有规则，尝试解析为数字
                const num = Number(rule.id);
                if (!isNaN(num)) {
                    id = num;
                }
            }

            // 确保 conditions 是有效数组，不为 null，不是空数组
            const conditions = (rule.sources && rule.sources.length > 0)
                ? rule.sources.map(source => ({
                    deviceName: String(source.fromId || ''),
                    attribute: String(source.fromApi || ''),
                    relation: String(source.relation || 'EQ'),
                    value: String(source.value || 'true')
                }))
                : [{ deviceName: 'dummy', attribute: 'dummy', relation: 'EQ', value: 'true' }];

            // 确保 command 是有效对象，不为 null
            const command = {
                deviceName: String(rule.toId || ''),
                action: String(rule.toApi || ''),
                contentDevice: null as string | null,
                content: null as string | null
            };

            const dto = {
                id: id,
                conditions: conditions,
                command: command,
                ruleString: String(rule.name || '')
            };
            
            return dto;
        });

        return unpack<RuleForm[]>(await api.post('/board/rules', ruleDtos));
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
    },
    createDeviceTemplate: async (tpl: DeviceTemplate): Promise<DeviceTemplate> => {
        return unpack<DeviceTemplate>(await api.post('/board/templates', tpl));
    },
    reloadDeviceTemplates: async (): Promise<number> => {
        return unpack<number>(await api.post('/board/templates/reload'));
    },

    // ==== 验证 ====
    verify: async (req: VerificationRequest): Promise<VerificationResult> => {
        return unpack<VerificationResult>(await api.post('/verify', req));
    },
    getTask: async (taskId: number): Promise<VerificationTask> => {
        return unpack<VerificationTask>(await api.get(`/verify/tasks/${taskId}`));
    },
    getTaskProgress: async (taskId: number): Promise<number> => {
        return unpack<number>(await api.get(`/verify/tasks/${taskId}/progress`));
    },
    cancelTask: async (taskId: number): Promise<boolean> => {
        return unpack<boolean>(await api.post(`/verify/tasks/${taskId}/cancel`));
    }
}

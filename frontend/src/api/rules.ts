// src/api/rules.ts - Rules API
import api from '@/api/http'

// 辅助函数：解包Result（后端返回 { code, message, data }）
const unpack = <T>(response: any): T => {
  return response.data.data;
};

// 用于取消请求的 AbortController
let currentAbortController: AbortController | null = null;

/**
 * 获取规则推荐
 */
export interface RuleRecommendation {
  category: string
  description: string
  priority: string
  confidence: number
  requiresUserInput?: boolean
  conditions: {
    deviceName: string
    attribute: string
    relation: string
    value: string
  }[]
  command: {
    deviceName: string
    action: string
    contentDevice?: string
    content?: string
  }
}

export interface RecommendRulesResponse {
  message: string
  count: number
  recommendations: RuleRecommendation[]
}

export const recommendRules = async (
  maxRecommendations: number = 5,
  category: string = 'all',
  signal?: AbortSignal
): Promise<RecommendRulesResponse> => {
  // 如果有正在进行的请求，先取消
  if (currentAbortController) {
    currentAbortController.abort()
  }
  // 创建新的 AbortController
  currentAbortController = new AbortController()
  
  const response = await api.get<any>('/board/rules/recommend', {
    params: { maxRecommendations, category },
    signal: signal || currentAbortController.signal
  })
  currentAbortController = null
  return unpack<RecommendRulesResponse>(response)
}

/**
 * 取消规则推荐请求
 */
export const cancelRecommendRules = (): void => {
  if (currentAbortController) {
    currentAbortController.abort()
    currentAbortController = null
  }
}

/**
 * 规则类型定义
 */
export interface Rule {
  id?: number
  userId?: number
  conditions: {
    deviceName: string
    attribute: string
    relation?: string
    value?: string
  }[]
  command: {
    deviceName: string
    action: string
    contentDevice?: string
    content?: string
  }
}

/**
 * 获取规则列表
 */
export const getRules = async (): Promise<Rule[]> => {
  const response = await api.get<any>('/board/rules')
  return unpack<Rule[]>(response)
}

/**
 * 保存规则列表
 */
export const saveRules = async (rules: Rule[]): Promise<Rule[]> => {
  const response = await api.post<any>('/board/rules', rules)
  return unpack<Rule[]>(response)
}

// Default export for convenience
export default {
  recommendRules,
  cancelRecommendRules,
  getRules,
  saveRules
}

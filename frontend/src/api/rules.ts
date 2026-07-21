// src/api/rules.ts - Rules API
import api from '@/api/http'
import { validateStandaloneRecommendationResponse } from '@/utils/recommendationResponse'
import { validateRuleRecommendationCandidate } from '@/utils/recommendationMaterialization'

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
  category?: string
  /** Exact user-facing rule name persisted when the candidate is applied. */
  name: string
  conditions: {
    deviceId: string
    deviceLabel?: string
    deviceName: string
    attribute: string
    targetType: 'api' | 'variable' | 'mode' | 'state'
    relation?: string
    value?: string
  }[]
  command: {
    deviceId: string
    deviceLabel?: string
    deviceName: string
    action: string
    contentDevice?: string
    contentDeviceLabel?: string
    content?: string
    contentPrivacy?: 'public' | 'private'
  }
}

export interface RecommendationFilteredItem {
  type: string
  index: number
  reasonCode: string
  reason: string
  label?: string
}

export interface RecommendationAdjustmentItem {
  type: string
  index?: number
  reasonCode: string
  reason: string
  label?: string
  appliedValues: Record<string, unknown>
}

export interface RecommendRulesResponse {
  message: string
  count: number
  requestedCount: number
  validatedCount: number
  filteredCount: number
  filteredItems: RecommendationFilteredItem[]
  adjustedCount: number
  adjustedItems: RecommendationAdjustmentItem[]
  rawCandidateCount: number
  inspectedCount: number
  truncatedCount: number
  recommendations: RuleRecommendation[]
}

export const recommendRules = async (
  maxRecommendations: number = 5,
  category: string = 'all',
  language: string = 'en',
  userRequirement: string = '',
  requestId: string = crypto.randomUUID(),
  signal?: AbortSignal
): Promise<RecommendRulesResponse> => {
  const ownedController = signal ? null : new AbortController()
  if (ownedController) {
    currentAbortController?.abort()
    currentAbortController = ownedController
  }

  try {
    const response = await api.post<any>('/board/rules/recommend', {
      maxRecommendations, category, language, userRequirement, requestId
    }, {
      signal: signal || ownedController!.signal,
      timeout: 0
    })
    return validateStandaloneRecommendationResponse<RecommendRulesResponse>(
      unpack<unknown>(response),
      'Rule recommendation',
      validateRuleRecommendationCandidate,
      true
    )
  } finally {
    if (ownedController && currentAbortController === ownedController) {
      currentAbortController = null
    }
  }
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
// NOTE: targeted rule persistence and RuleDto <-> RuleForm mapping live in `api/board.ts`.
// This module owns only rule recommendation so there is one mutation authority.

// Default export for convenience
export default {
  recommendRules,
  cancelRecommendRules
}

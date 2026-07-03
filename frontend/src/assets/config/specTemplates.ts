// src/assets/config/specTemplates.ts
// Types live in @/types/spec (single source); this module only provides runtime config.
import type { SpecTemplate, SpecTemplateType, SpecTemplateDetail } from '@/types/spec.ts'

// Re-export so existing importers of these types from this module keep working.
export type { SpecTemplateType, SpecTemplateDetail }

/**
 * 七种规约模板配置
 * 
 * 规约条件位置 (Side) 说明：
 * - 'a': Always/Forall - 全局条件，用于描述系统必须始终满足的属性
 * - 'if': Antecedent - IF语句的前件（前提条件）
 * - 'then': Consequent - IF语句的后件（结果条件）
 */
export const specTemplateDetails: SpecTemplateDetail[] = [
  {
    id: '1',
    type: 'always',
    label: 'A holds forever',
    description: '系统必须始终保持某个状态或条件为真',
    requiredSides: ['a'],
    ltlFormula: '□A'
  },
  {
    id: '2',
    type: 'eventually',
    label: 'A will happen later',
    description: '某个状态或条件最终一定会发生',
    requiredSides: ['a'],
    ltlFormula: '◇A'
  },
  {
    id: '3',
    type: 'never',
    label: 'A never happens',
    description: '某个状态或条件永远不能发生',
    requiredSides: ['a'],
    ltlFormula: '□¬A'
  },
  {
    id: '4',
    type: 'immediate',
    label: 'IF A happens, B should happen in the next state (immediately after)',
    description: '当条件A发生时，条件B必须在下一状态满足（紧接其后）',
    requiredSides: ['if', 'then'],
    ltlFormula: '□(A → ○B)'
  },
  {
    id: '5',
    type: 'response',
    label: 'IF A happens, B should happen later',
    description: '当条件A发生后，条件B最终必须发生（响应模式）',
    requiredSides: ['if', 'then'],
    ltlFormula: '□(A → ◇B)'
  },
  {
    id: '6',
    type: 'persistence',
    label: 'IF A happens, B should happen later and last forever',
    description: '当条件A发生后，条件B必须永远保持',
    requiredSides: ['if', 'then'],
    ltlFormula: '□(A → □B)'
  },
  {
    id: '7',
    type: 'safety',
    label: 'A will not happen because of something untrusted',
    description: '当检测到不可信操作时，指定的事件A不会发生',
    requiredSides: ['a'],
    ltlFormula: '□(untrusted → ¬A)'
  }
]

// 兼容旧版本的简单模板列表（用于下拉选择）
export const defaultSpecTemplates: SpecTemplate[] = specTemplateDetails.map(t => ({
  id: t.id,
  label: t.label
}))

// 可用的关系运算符
export const relationOperators = [
  { value: '=', label: '=' },
  { value: '!=', label: '≠' },
  { value: '>', label: '>' },
  { value: '>=', label: '≥' },
  { value: '<', label: '<' },
  { value: '<=', label: '≤' },

  { value: 'in', label: 'in' },
  { value: 'not_in', label: 'not in' }
]

// 可用的目标类型（与后端 SpecConditionDto.targetType 一致）
export const targetTypes = [
  { value: 'state', label: 'State' },
  { value: 'variable', label: 'Variable' },
  { value: 'api', label: 'API' },
  { value: 'trust', label: 'Trust' },
  { value: 'privacy', label: 'Privacy' }
]

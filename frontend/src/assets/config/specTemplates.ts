// src/assets/config/specTemplates.ts
import type { SpecTemplate, SpecSide } from '@/types/spec.ts'

export type SpecTemplateType = 
  | 'always'      // A holds forever - 只有a条件
  | 'eventually'  // A will happen later - 只有a条件
  | 'never'       // A never happens - 只有a条件
  | 'immediate'   // A → B (at same time) - if + then
  | 'response'    // A → ◇B (eventually) - if + then
  | 'persistence' // A → □B (forever after) - if + then
  | 'safety'      // untrusted → ¬A - if + then

export interface SpecTemplateDetail extends SpecTemplate {
  type: SpecTemplateType
  description: string
  requiredSides: SpecSide[]  // 需要配置的条件位置
  ltlFormula: string         // 对应的LTL公式
}

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
    label: 'IF A happens, B should happen at the same time',
    description: '当条件A发生时，条件B必须同时发生',
    requiredSides: ['if', 'then'],
    ltlFormula: '□(A → B)'
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
    requiredSides: ['if', 'then'],
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
  { value: '=', label: '等于 (=)' },
  { value: '!=', label: '不等于 (≠)' },
  { value: '>', label: '大于 (>)' },
  { value: '>=', label: '大于等于 (≥)' },
  { value: '<', label: '小于 (<)' },
  { value: '<=', label: '小于等于 (≤)' },
  { value: 'contains', label: '包含' },
  { value: 'not_contains', label: '不包含' },
  { value: 'matches', label: '匹配正则' }
]

// 可用的目标类型
export const targetTypes = [
  { value: 'state', label: 'State' },
  { value: 'variable', label: 'Variable' },
  { value: 'api', label: 'API' }
]

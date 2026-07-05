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
    labelKey: 'app.specTemplates.always.label',
    description: 'The system must always maintain a given state or condition.',
    descriptionKey: 'app.specTemplates.always.description',
    requiredSides: ['a'],
    ltlFormula: '□A'
  },
  {
    id: '2',
    type: 'eventually',
    label: 'A will happen later',
    labelKey: 'app.specTemplates.eventually.label',
    description: 'A state or condition must eventually occur.',
    descriptionKey: 'app.specTemplates.eventually.description',
    requiredSides: ['a'],
    ltlFormula: '◇A'
  },
  {
    id: '3',
    type: 'never',
    label: 'A never happens',
    labelKey: 'app.specTemplates.never.label',
    description: 'A state or condition must never occur.',
    descriptionKey: 'app.specTemplates.never.description',
    requiredSides: ['a'],
    ltlFormula: '□¬A'
  },
  {
    id: '4',
    type: 'immediate',
    label: 'IF A happens, B should happen in the next state (immediately after)',
    labelKey: 'app.specTemplates.immediate.label',
    description: 'When condition A occurs, condition B must hold in the next state.',
    descriptionKey: 'app.specTemplates.immediate.description',
    requiredSides: ['if', 'then'],
    ltlFormula: '□(A → ○B)'
  },
  {
    id: '5',
    type: 'response',
    label: 'IF A happens, B should happen later',
    labelKey: 'app.specTemplates.response.label',
    description: 'After condition A occurs, condition B must eventually occur.',
    descriptionKey: 'app.specTemplates.response.description',
    requiredSides: ['if', 'then'],
    ltlFormula: '□(A → ◇B)'
  },
  {
    id: '6',
    type: 'persistence',
    label: 'IF A happens, B should happen later and last forever',
    labelKey: 'app.specTemplates.persistence.label',
    description: 'After condition A occurs, condition B must hold forever.',
    descriptionKey: 'app.specTemplates.persistence.description',
    requiredSides: ['if', 'then'],
    ltlFormula: '□(A → □B)'
  },
  {
    id: '7',
    type: 'safety',
    label: 'A will not happen because of something untrusted',
    labelKey: 'app.specTemplates.safety.label',
    description: 'When an untrusted operation is detected, event A must not occur.',
    descriptionKey: 'app.specTemplates.safety.description',
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

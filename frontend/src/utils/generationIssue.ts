import type { ModelGenerationIssue, ModelGenerationIssueReasonCode } from '@/types/verify'

export type GenerationIssueReasonKey =
  | 'app.generationIssueRuleNoTriggers'
  | 'app.generationIssueRuleNullTrigger'
  | 'app.generationIssueRuleUnresolvableTrigger'
  | 'app.generationIssueRuleNoResolvableTriggers'
  | 'app.generationIssueRulePropertyUnavailable'
  | 'app.generationIssueSpecNoConditions'
  | 'app.generationIssueSpecPrivacyDisabled'
  | 'app.generationIssueSpecUnsupportedRelation'
  | 'app.generationIssueSpecAmbiguousState'
  | 'app.generationIssueSpecUnknownSecurityProperty'
  | 'app.generationIssueSpecUnknownDevice'
  | 'app.generationIssueSpecTemplateMismatch'
  | 'app.generationIssueSpecInvalidValue'
  | 'app.generationIssueSpecUnsupportedCondition'
  | 'app.generationIssueUnknown'

const reasonKeys: Record<ModelGenerationIssueReasonCode, GenerationIssueReasonKey> = {
  RULE_NO_TRIGGER_CONDITIONS: 'app.generationIssueRuleNoTriggers',
  RULE_NULL_TRIGGER_CONDITION: 'app.generationIssueRuleNullTrigger',
  RULE_UNRESOLVABLE_TRIGGER_CONDITION: 'app.generationIssueRuleUnresolvableTrigger',
  RULE_NO_RESOLVABLE_TRIGGER_CONDITIONS: 'app.generationIssueRuleNoResolvableTriggers',
  RULE_PROPERTY_PROPAGATION_UNAVAILABLE: 'app.generationIssueRulePropertyUnavailable',
  SPEC_NO_CHECKABLE_CONDITIONS: 'app.generationIssueSpecNoConditions',
  SPEC_PRIVACY_MODELING_DISABLED: 'app.generationIssueSpecPrivacyDisabled',
  SPEC_UNSUPPORTED_RELATION: 'app.generationIssueSpecUnsupportedRelation',
  SPEC_AMBIGUOUS_STATE: 'app.generationIssueSpecAmbiguousState',
  SPEC_UNDECLARED_SECURITY_PROPERTY: 'app.generationIssueSpecUnknownSecurityProperty',
  SPEC_UNKNOWN_DEVICE: 'app.generationIssueSpecUnknownDevice',
  SPEC_TEMPLATE_SHAPE_MISMATCH: 'app.generationIssueSpecTemplateMismatch',
  SPEC_INVALID_VALUE: 'app.generationIssueSpecInvalidValue',
  SPEC_UNSUPPORTED_CONDITION: 'app.generationIssueSpecUnsupportedCondition',
  UNCLASSIFIED_GENERATION_ISSUE: 'app.generationIssueUnknown'
}

export const generationIssueReasonKey = (
  issue: Pick<ModelGenerationIssue, 'reasonCode'>
): GenerationIssueReasonKey => reasonKeys[issue.reasonCode] || 'app.generationIssueUnknown'

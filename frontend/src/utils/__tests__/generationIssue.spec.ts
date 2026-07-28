import { describe, expect, it } from 'vitest'
import { generationIssueReasonKey } from '@/utils/generationIssue'
import { i18n } from '@/assets/i18n'
import type { ModelGenerationIssueReasonCode } from '@/types/verify'

/**
 * Mirrors `ModelGenerationIssueReasonCode.java`. Spot-checking two codes let a new backend code ship
 * with no message behind its key, which renders the raw key to the user.
 */
const allReasonCodes: ModelGenerationIssueReasonCode[] = [
  'RULE_NO_TRIGGER_CONDITIONS',
  'RULE_NULL_TRIGGER_CONDITION',
  'RULE_UNRESOLVABLE_TRIGGER_CONDITION',
  'RULE_NO_RESOLVABLE_TRIGGER_CONDITIONS',
  'RULE_PROPERTY_PROPAGATION_UNAVAILABLE',
  'RULE_UNRESOLVABLE_COMMAND_ACTION',
  'SPEC_NO_CHECKABLE_CONDITIONS',
  'SPEC_PRIVACY_MODELING_DISABLED',
  'SPEC_UNSUPPORTED_RELATION',
  'SPEC_AMBIGUOUS_STATE',
  'SPEC_UNDECLARED_SECURITY_PROPERTY',
  'SPEC_UNKNOWN_DEVICE',
  'SPEC_TEMPLATE_SHAPE_MISMATCH',
  'SPEC_INVALID_VALUE',
  'SPEC_UNSUPPORTED_CONDITION',
  'UNCLASSIFIED_GENERATION_ISSUE'
]

describe('generationIssueReasonKey', () => {
  it('maps stable backend reason codes to localized message keys', () => {
    expect(generationIssueReasonKey({ reasonCode: 'RULE_NO_TRIGGER_CONDITIONS' }))
      .toBe('app.generationIssueRuleNoTriggers')
    expect(generationIssueReasonKey({ reasonCode: 'SPEC_UNKNOWN_DEVICE' }))
      .toBe('app.generationIssueSpecUnknownDevice')
  })

  it.each(['zh-CN', 'en'] as const)('has a %s message for every reason code', locale => {
    const missing = allReasonCodes.filter(code => {
      const key = generationIssueReasonKey({ reasonCode: code })
      return !i18n.global.te(key, locale)
    })
    expect(missing).toEqual([])
  })

  it('gives each reason code a distinct key so no two omissions read alike', () => {
    const keys = allReasonCodes.map(code => generationIssueReasonKey({ reasonCode: code }))
    expect(new Set(keys).size).toBe(allReasonCodes.length)
  })

  it('uses a non-technical fallback for unclassified omissions', () => {
    expect(generationIssueReasonKey({ reasonCode: 'UNCLASSIFIED_GENERATION_ISSUE' }))
      .toBe('app.generationIssueUnknown')
  })
})

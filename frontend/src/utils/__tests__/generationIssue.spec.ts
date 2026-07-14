import { describe, expect, it } from 'vitest'
import { generationIssueReasonKey } from '@/utils/generationIssue'

describe('generationIssueReasonKey', () => {
  it('maps stable backend reason codes to localized message keys', () => {
    expect(generationIssueReasonKey({ reasonCode: 'RULE_NO_TRIGGER_CONDITIONS' }))
      .toBe('app.generationIssueRuleNoTriggers')
    expect(generationIssueReasonKey({ reasonCode: 'SPEC_UNKNOWN_DEVICE' }))
      .toBe('app.generationIssueSpecUnknownDevice')
  })

  it('uses a non-technical fallback for unclassified omissions', () => {
    expect(generationIssueReasonKey({ reasonCode: 'UNCLASSIFIED_GENERATION_ISSUE' }))
      .toBe('app.generationIssueUnknown')
  })
})

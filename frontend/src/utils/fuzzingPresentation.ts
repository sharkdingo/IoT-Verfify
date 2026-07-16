export const fuzzingLimitationKey = (code: string): string => {
  const keys: Record<string, string> = {
    FINITE_TRACE_TEMPLATES_1_3_4_ONLY: 'app.fuzzLimitationFiniteTraceTemplates',
    ATTACK_TRUST_PRIVACY_CONTENT_UNSUPPORTED: 'app.fuzzLimitationUnsupportedConcepts',
    FINAL_ANTECEDENT_WITHOUT_SUCCESSOR_INCONCLUSIVE: 'app.fuzzLimitationFinalAntecedent',
    PAPER_EVENT_FSM_DISTANCE_ENABLED: 'app.fuzzLimitationPaperEventFsmDistanceEnabled',
    PAPER_RANDOM_INITIAL_STATE_ENABLED: 'app.fuzzLimitationPaperRandomInitialStateEnabled',
    PAPER_STRUCTURED_LTL_TEMPLATES_ONLY: 'app.fuzzLimitationPaperStructuredLtlOnly',
    PAPER_INTEGER_NUMERIC_DOMAIN_ONLY: 'app.fuzzLimitationPaperIntegerNumericOnly',
    PAPER_DISCRETE_ENVIRONMENT_DIRECT_VALUE_EXTENSION: 'app.fuzzLimitationPaperDiscreteEnvironmentExtension',
    NUSMV_REMAINS_PROOF_AUTHORITY: 'app.fuzzLimitationNuSmvProofAuthority',
    PAPER_PREDECESSOR_STATE_OUTPUTS_THREE_LEVELS_ONLY: 'app.fuzzLimitationPaperPredecessorOutputsThreeLevels',
    PAPER_MULTI_TARGET_PRODUCT_EXTENSION: 'app.fuzzLimitationPaperMultiTargetExtension'
  }
  return keys[code] || 'app.fuzzLimitationUnknown'
}

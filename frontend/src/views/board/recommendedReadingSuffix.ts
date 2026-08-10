/**
 * The reading label appended to a recommended specification condition, as an i18n key.
 *
 * A recommendation card is a **consent** surface: the user reads it and clicks Apply, and the applied
 * condition is persisted with whatever `variableSource` the model chose. The product refuses to let a human
 * save a variable condition without choosing, and rejects a model candidate that omits the field — so the
 * one thing it must not do is hide the model's answer at the moment of consent. The card previously rendered
 * `environment` and `reported` recommendations byte-identically.
 *
 * Returns null when there is nothing to name: a non-variable condition has no reading, and a missing one
 * cannot occur on this path (materialization rejects such a candidate) but is reported as absent rather than
 * guessed, on the same principle as everywhere else.
 */
export const recommendedReadingKey = (
    targetType: unknown,
    variableSource: unknown
): string | null => {
    if (String(targetType || '').trim().toLowerCase() !== 'variable') return null
    if (variableSource === 'environment') return 'app.specVariableSourceEnvironmentShort'
    if (variableSource === 'reported') return 'app.specVariableSourceReportedShort'
    return null
}

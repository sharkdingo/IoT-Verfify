import { describe, expect, it } from 'vitest'
import { recommendedReadingKey } from './recommendedReadingSuffix'

describe('recommendedReadingKey', () => {
    it('names the reading a recommended variable condition will persist', () => {
        // A recommendation card is where the user consents. Both readings rendered identically before this,
        // so Apply wrote a choice the user was never shown — one no human is allowed to skip.
        expect(recommendedReadingKey('variable', 'environment'))
            .toBe('app.specVariableSourceEnvironmentShort')
        expect(recommendedReadingKey('variable', 'reported'))
            .toBe('app.specVariableSourceReportedShort')
    })

    it('distinguishes the two readings rather than collapsing them', () => {
        expect(recommendedReadingKey('variable', 'environment'))
            .not.toBe(recommendedReadingKey('variable', 'reported'))
    })

    it('names nothing for a condition that has no reading', () => {
        // A mode/state/api/trust/privacy condition is not asking about a value at all, so appending a
        // reading would invent a distinction the property does not make.
        for (const targetType of ['state', 'mode', 'api', 'trust', 'privacy']) {
            expect(recommendedReadingKey(targetType, undefined)).toBeNull()
            // Even if a stray value rides along, a non-variable target must not display one.
            expect(recommendedReadingKey(targetType, 'environment')).toBeNull()
        }
    })

    it('tolerates the casing and padding the wire may carry', () => {
        expect(recommendedReadingKey(' Variable ', 'reported'))
            .toBe('app.specVariableSourceReportedShort')
    })

    it('reports an absent or unrecognised reading rather than guessing one', () => {
        expect(recommendedReadingKey('variable', undefined)).toBeNull()
        expect(recommendedReadingKey('variable', null)).toBeNull()
        expect(recommendedReadingKey('variable', 'pool')).toBeNull()
    })
})

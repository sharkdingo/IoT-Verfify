import { CREDENTIAL_LIMITS } from '@/constants/requestLimits'

const DISALLOWED_USERNAME_CHARACTERS = /[\p{Cc}\p{Cf}\p{Zl}\p{Zp}]/u

export const normalizeAccountIdentifier = (value: string): string =>
  value.normalize('NFC').trim()

/**
 * The length bounds come from `CREDENTIAL_LIMITS`, not from literals here.
 *
 * They were hardcoded `3` and `20` — the same defect as `UsernameNormalizer` on the backend, recurred on this
 * side. It is not merely a duplicate: `Landing.vue` checks the length against `CREDENTIAL_LIMITS` first and
 * shows `auth.usernameLength`, then calls this function and shows `auth.usernameInvalidCharacters`. If the two
 * disagreed, a *length* problem would be reported to the user as a *character-set* problem, on a field whose own
 * hint states the correct range — the user reads "invalid characters" about a name containing none.
 *
 * `credentialLimitsMirror.spec.ts` could not catch it: its call-site scan targets `Landing.vue` and the
 * identifier `usernameLength`, so a literal in this module was structurally invisible to it. That check now
 * covers this file too.
 */
export const isValidNormalizedUsername = (value: string): boolean => {
  const length = Array.from(value).length
  return length >= CREDENTIAL_LIMITS.minUsernameDisplayLength
    && length <= CREDENTIAL_LIMITS.maxUsernameDisplayLength
    && !DISALLOWED_USERNAME_CHARACTERS.test(value)
}

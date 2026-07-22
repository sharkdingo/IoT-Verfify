const DISALLOWED_USERNAME_CHARACTERS = /[\p{Cc}\p{Cf}\p{Zl}\p{Zp}]/u

export const normalizeAccountIdentifier = (value: string): string =>
  value.normalize('NFC').trim()

export const isValidNormalizedUsername = (value: string): boolean => {
  const length = Array.from(value).length
  return length >= 3
    && length <= 20
    && !DISALLOWED_USERNAME_CHARACTERS.test(value)
}

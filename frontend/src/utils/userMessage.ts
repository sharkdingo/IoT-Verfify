const HAN_CHARACTER = /[\u3400-\u9fff]/g
const ENGLISH_WORD = /\b[A-Za-z]{2,}\b/g

export const textMatchesLocale = (value: unknown, locale: string): value is string => {
  if (typeof value !== 'string' || !value.trim()) return false
  const text = value.trim()
  const hanCount = text.match(HAN_CHARACTER)?.length || 0
  const englishWordCount = text.match(ENGLISH_WORD)?.length || 0
  const chineseLocale = locale.toLowerCase().startsWith('zh')
  if (chineseLocale) {
    return hanCount > 0 && englishWordCount <= Math.max(2, Math.floor(hanCount / 2))
  }
  return hanCount === 0
}

export const localizedTextOrFallback = (
  value: unknown,
  fallback: string,
  locale: string
): string => textMatchesLocale(value, locale) ? value.trim() : fallback

export const localizedErrorMessage = (
  error: any,
  fallback: string,
  locale: string
): string => localizedTextOrFallback(
  error?.response?.data?.message || error?.message,
  fallback,
  locale
)

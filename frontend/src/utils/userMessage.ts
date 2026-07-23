const HAN_CHARACTER = /[\u3400-\u9fff]/g
const ENGLISH_WORD = /\b[A-Za-z]{2,}\b/g

export const textMatchesLocale = (value: unknown, locale: string): value is string => {
  if (typeof value !== 'string' || !value.trim()) return false
  const text = value.trim()
  const hanCount = text.match(HAN_CHARACTER)?.length || 0
  const englishWordCount = text.match(ENGLISH_WORD)?.length || 0
  const hasHan = hanCount > 0
  const hasEnglishWords = englishWordCount > 0

  // User-defined device and state labels commonly use a different script from the UI.
  // Without structured metadata, mixed-script text cannot be classified safely.
  if (hasHan && hasEnglishWords) return true

  const chineseLocale = locale.toLowerCase().startsWith('zh')
  return chineseLocale ? hasHan : !hasHan
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

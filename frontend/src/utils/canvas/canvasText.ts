const isWideGlyph = (glyph: string): boolean => {
  const codePoint = glyph.codePointAt(0) ?? 0
  return codePoint > 0xffff || /[\u2e80-\u9fff\uac00-\ud7af\uf900-\ufaff\ufe10-\ufe6f\uff01-\uff60\uffe0-\uffe6]/u.test(glyph)
}

const glyphWidth = (glyph: string): number => {
  if (isWideGlyph(glyph)) return 10
  if (/[MW@%#]/.test(glyph)) return 9
  if (/[A-Z]/.test(glyph)) return 7
  if (/[ilI1.,'`:;!|\s]/.test(glyph)) return 4
  return 6
}

export const estimateCanvasTextWidth = (value: string): number =>
  Array.from(String(value || '')).reduce((width, glyph) => width + glyphWidth(glyph), 0)

export const truncateCanvasTextToWidth = (value: string, maxWidth: number): string => {
  const normalized = String(value || '').trim()
  if (estimateCanvasTextWidth(normalized) <= maxWidth) return normalized

  const ellipsis = '…'
  const availableWidth = Math.max(0, maxWidth - glyphWidth(ellipsis))
  let width = 0
  let result = ''
  for (const glyph of Array.from(normalized)) {
    const nextWidth = width + glyphWidth(glyph)
    if (nextWidth > availableWidth) break
    result += glyph
    width = nextWidth
  }
  return `${result}${ellipsis}`
}

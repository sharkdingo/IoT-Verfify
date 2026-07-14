import { describe, expect, it } from 'vitest'
import { localizedErrorMessage, localizedTextOrFallback, textMatchesLocale } from '../userMessage'

describe('user-facing free-text language guard', () => {
  it('rejects an English backend sentence in a Chinese interface', () => {
    expect(textMatchesLocale('Unknown condition device: device_123', 'zh-CN')).toBe(false)
    expect(localizedErrorMessage({
      response: { data: { message: 'Unknown condition device: device_123' } }
    }, '操作失败', 'zh-CN')).toBe('操作失败')
  })

  it('keeps Chinese explanations and English device labels used inside them', () => {
    expect(localizedTextOrFallback(
      '删除设备 Air Conditioner 失败',
      '操作失败',
      'zh-CN'
    )).toBe('删除设备 Air Conditioner 失败')
  })

  it('keeps English diagnostics in an English interface', () => {
    expect(localizedTextOrFallback('The request was rejected.', 'Request failed', 'en'))
      .toBe('The request was rejected.')
  })
})

import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { beforeEach, describe, expect, it } from 'vitest'
import { i18n, setLocale, syncDocumentLanguage } from '../i18n'

/**
 * The document must declare the language it is actually rendering.
 *
 * `index.html` hardcoded `lang="en"` and nothing ever updated it, while the app's default locale is
 * `zh-CN` — so the shipped default declared English while rendering Chinese, and a screen reader applied
 * English pronunciation rules to every Chinese string. That is WCAG 3.1.1, and it affected the whole
 * product rather than one control.
 *
 * These checks exist because the defect is completely invisible on screen: nothing about the rendered
 * page looks different, so only an assertion catches a regression.
 */
describe('document language declaration', () => {
  beforeEach(() => {
    document.documentElement.lang = ''
  })

  it('declares the locale the app starts in', () => {
    syncDocumentLanguage(String(i18n.global.locale.value))
    expect(document.documentElement.lang).toBe(String(i18n.global.locale.value))
  })

  it('re-declares it whenever the language is set', () => {
    setLocale('en')
    expect(document.documentElement.lang).toBe('en')
    expect(localStorage.getItem('locale')).toBe('en')

    setLocale('zh-CN')
    expect(document.documentElement.lang).toBe('zh-CN')
    expect(localStorage.getItem('locale')).toBe('zh-CN')
  })

  it('keeps the static default in step with the app default', () => {
    // If these drift, the first paint declares one language and the app renders another.
    const html = readFileSync(join(__dirname, '../../../index.html'), 'utf8')
    const declared = html.match(/<html lang="([^"]+)"/)?.[1]
    const i18nSource = readFileSync(join(__dirname, '../i18n.ts'), 'utf8')
    const appDefault = i18nSource.match(/localStorage\.getItem\('locale'\)\s*\|\|\s*'([^']+)'/)?.[1]

    expect(declared).toBeDefined()
    expect(appDefault).toBeDefined()
    expect(declared).toBe(appDefault)
  })

  it('routes every language change through the single owner', () => {
    // A second writer that only persisted the choice would silently reintroduce the original defect,
    // because nothing on screen would look wrong.
    const toggle = readFileSync(
      join(__dirname, '../../components/common/LanguageToggle.vue'), 'utf8')
    expect(toggle).toContain('setLocale(')
    expect(toggle).not.toMatch(/localStorage\.setItem\('locale'/)
  })

  it('marks the switch control with the language of its own accessible name', () => {
    // Its `aria-label` is deliberately written in the language it leads to ("Switch to English" while
    // the interface is Chinese), so without `lang` a screen reader reads those words with the
    // surrounding document's rules — the one control where that is guaranteed to be wrong.
    const toggle = readFileSync(
      join(__dirname, '../../components/common/LanguageToggle.vue'), 'utf8')
    expect(toggle).toMatch(/:lang="isChinese \? 'en' : 'zh-CN'"/)
  })
})

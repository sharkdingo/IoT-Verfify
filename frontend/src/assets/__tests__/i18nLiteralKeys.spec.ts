import { readdirSync, readFileSync } from 'node:fs'
import { extname, join, relative } from 'node:path'
import { describe, expect, it } from 'vitest'

import { i18n } from '@/assets/i18n'

const SOURCE_EXTENSIONS = new Set(['.ts', '.vue'])
const TRANSLATION_CALL = /(?<![\w$])(?:\$t|t)\(\s*(['"])([^'"\r\n]+)\1/g

const sourceFiles = (directory: string): string[] => readdirSync(directory, { withFileTypes: true })
  .flatMap(entry => {
    const path = join(directory, entry.name)
    if (entry.isDirectory()) return sourceFiles(path)
    return SOURCE_EXTENSIONS.has(extname(entry.name)) ? [path] : []
  })

describe('literal i18n calls', () => {
  it('resolve in both supported languages', () => {
    const sourceRoot = join(process.cwd(), 'src')
    const missing: string[] = []
    const locales = ['zh-CN', 'en'] as const

    for (const file of sourceFiles(sourceRoot)) {
      if (file.endsWith('i18n.ts') || file.includes('__tests__')
          || file.endsWith('.spec.ts') || file.endsWith('.test.ts')) continue
      const content = readFileSync(file, 'utf8')
      for (const match of content.matchAll(TRANSLATION_CALL)) {
        const key = match[2]
        for (const locale of locales) {
          if (!i18n.global.te(key, locale)) {
            missing.push(`${relative(sourceRoot, file)}: ${locale}.${key}`)
          }
        }
      }
    }

    expect(missing, `Missing literal translation keys:\n${missing.join('\n')}`).toEqual([])
  })
})

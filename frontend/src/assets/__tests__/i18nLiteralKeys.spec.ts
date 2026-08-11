import { readdirSync, readFileSync } from 'node:fs'
import { extname, join, relative } from 'node:path'
import { describe, expect, it } from 'vitest'

import { i18n } from '@/assets/i18n'

const SOURCE_EXTENSIONS = new Set(['.ts', '.vue'])
const TRANSLATION_CALL = /(?<![\w$])(?:\$t|t)\(\s*(['"])([^'"\r\n]+)\1/g
// Matching only a callee named `t`/`$t` missed every key handed to an injected translator under
// another name: `traceView.ts` calls `translate('app.unknownDevice')`, so that key was absent from
// the bundle while the unit spec passed against its own stub dictionary. A dotted literal under a
// real message namespace is a key claim regardless of what consumes it, so audit the literals.
// The namespaces come from the bundle rather than a hand-kept list, so adding one to i18n.ts cannot
// leave a whole namespace unaudited — an earlier draft hardcoded `app|specTemplates` and silently
// excluded all 43 `auth.*` keys.
const messageNamespaces = (): string[] =>
  Object.keys((i18n.global.messages.value as Record<string, Record<string, unknown>>)['zh-CN'])
const KEY_LITERAL = new RegExp(
  `(['"])((?:${messageNamespaces().join('|')})\\.[A-Za-z0-9_]+(?:\\.[A-Za-z0-9_]+)*)\\1`,
  'g'
)

const sourceFiles = (directory: string): string[] => readdirSync(directory, { withFileTypes: true })
  .flatMap(entry => {
    const path = join(directory, entry.name)
    if (entry.isDirectory()) return sourceFiles(path)
    return SOURCE_EXTENSIONS.has(extname(entry.name)) ? [path] : []
  })

const LOCALES = ['zh-CN', 'en'] as const

/** Every key the pattern claims, with the locales it fails to resolve in. */
const unresolvedKeys = (pattern: RegExp) => {
  const sourceRoot = join(process.cwd(), 'src')
  const missing: string[] = []
  let scanned = 0

  for (const file of sourceFiles(sourceRoot)) {
    if (file.endsWith('i18n.ts') || file.includes('__tests__')
        || file.endsWith('.spec.ts') || file.endsWith('.test.ts')) continue
    const content = readFileSync(file, 'utf8')
    for (const match of content.matchAll(pattern)) {
      const key = match[2]
      scanned++
      for (const locale of LOCALES) {
        if (!i18n.global.te(key, locale)) {
          missing.push(`${relative(sourceRoot, file)}: ${locale}.${key}`)
        }
      }
    }
  }

  return { missing, scanned }
}

describe('literal i18n calls', () => {
  // Both patterns are kept because neither subsumes the other. KEY_LITERAL currently finds every key
  // TRANSLATION_CALL does and 423 more, but it is anchored to namespaces that exist, so it cannot see
  // `t('typo.somekey')` under a namespace that does not — which TRANSLATION_CALL reports as missing.
  it('resolve in both supported languages', () => {
    const { missing, scanned } = unresolvedKeys(TRANSLATION_CALL)

    // A scan that matches nothing asserts nothing; prove the corpus was actually walked.
    expect(scanned, 'no t()/$t() literal keys were scanned at all').toBeGreaterThan(500)
    expect(missing, `Missing literal translation keys:\n${missing.join('\n')}`).toEqual([])
  })

  it('resolve for keys passed to a renamed or injected translator', () => {
    const { missing, scanned } = unresolvedKeys(KEY_LITERAL)

    expect(scanned, 'no namespaced key literals were scanned at all').toBeGreaterThan(500)
    expect(missing, `Key literals with no translation:\n${missing.join('\n')}`).toEqual([])
  })
})

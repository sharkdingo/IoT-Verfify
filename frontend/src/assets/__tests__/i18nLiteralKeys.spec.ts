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

  /*
   * The reverse direction: every key defined is a key something claims.
   *
   * The two assertions above check "a key a source file names must resolve", which is the direction that
   * prevents a raw `app.something` reaching a user. Nothing checked the other way, and **35 orphaned keys
   * had accumulated** — including a family of four (`runBoardInput*Short`) and six added and abandoned in
   * a single refactor (`keyMetrics`, `specificationResults`, `traceSummary`, `verificationContext`,
   * `specResultsSummary`, `viewTrace`). Each was translated twice and rendered nowhere, so a reader
   * looking for the string that produces a label finds a plausible unused one.
   *
   * Dynamically built keys are the reason this direction is harder, and they are handled by construction
   * rather than by an allowlist: any template literal of the form `namespace.prefix${…}` contributes its
   * prefix, and every key under a contributed prefix counts as claimed. The bare `app.${…}` form is
   * narrowed to the four trust/privacy values its call sites can actually produce — verified at
   * `CanvasBoard.vue` and `ControlCenter.vue`, whose interpolations are typed to closed four-value sets.
   * Widening that to "any app key" would make this test unable to fail.
   */
  it('are all claimed by some source file', () => {
    /*
     * `e2e/` counts as a claimant, and that is not padding. An E2E spec addresses the product the way a
     * user does — several assert on rendered sentences (`'Move earlier'`, `'Replace in full'`) rather
     * than on keys — so a key used only by an E2E selector would look orphaned to a `src/`-only scan and
     * be deleted, breaking the suite in a way no unit test could see. Scanning only `src/` was a real gap
     * in the sweep that removed 35 keys; it happened to hit nothing, which is luck, not a method.
     */
    const corpus = [
      ...sourceFiles(join(process.cwd(), 'src')).filter(file => !file.endsWith('i18n.ts')),
      ...sourceFiles(join(process.cwd(), 'e2e'))
    ]
      .map(file => readFileSync(file, 'utf8'))
      .join('\n')

    // Prefixes of dynamically constructed keys, e.g. `app.taskProgressStage_${stage}`.
    const dynamicPrefixes = [...corpus.matchAll(/[`'"]([A-Za-z][A-Za-z0-9_.]*?)\$\{/g)]
      .map(match => match[1])
      .filter(prefix => prefix.includes('.') && prefix !== 'app.')
    // `t(`app.${trust}`)` / `t(`app.${privacy}`)`: closed domains, so exactly these four.
    const bareDynamic = new Set(['app.trusted', 'app.untrusted', 'app.private', 'app.public'])

    const leafKeys = (value: unknown, path: string[] = []): string[] =>
      value !== null && typeof value === 'object'
        ? Object.entries(value as Record<string, unknown>)
          .flatMap(([key, child]) => leafKeys(child, [...path, key]))
        : [path.join('.')]

    const defined = leafKeys(
      (i18n.global.messages.value as Record<string, unknown>)['zh-CN'])
    expect(defined.length, 'the bundle should have been walked').toBeGreaterThan(1000)

    const orphans = defined.filter(key =>
      !corpus.includes(key)
      && !bareDynamic.has(key)
      && !dynamicPrefixes.some(prefix => key.startsWith(prefix))
      // A lookup table may map data to a leaf and build the key from it; the bare leaf appearing as a
      // quoted string elsewhere is weak evidence of that, so it is tolerated rather than reported.
      && !new RegExp(`['"\`]${key.split('.').pop()}['"\`]`).test(corpus))

    expect(orphans, `i18n keys defined but claimed by nothing:\n${orphans.join('\n')}`).toEqual([])
  })
})

import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * The two locales must say the same thing, and neither may claim more than the engine proved.
 *
 * A key present in one locale and missing from the other does not fail loudly — it renders its own key path on
 * screen for half the users, and vue-i18n logs a warning nobody reads in production. In a formal verification
 * tool the worse case is semantic: if a verdict string softens or strengthens across languages, two users looking
 * at the same model get different claims about it.
 *
 * Measured at the time of writing: **2343 keys in each locale, zero structural gaps**, placeholders consistent,
 * and no outcome string over- or under-claiming.
 *
 * Two of the three rules here were wrong on their first attempt, both in the direction of a false alarm, and both
 * corrections are the interesting part:
 *
 * 1. **Placeholder counting.** vue-i18n pluralization writes `{count} result | {count} results`, so English
 *    repeats a placeholder once per plural form while Chinese has no plural inflection. Comparing occurrence
 *    lists flagged three correct messages; comparing the distinct set is the right test.
 * 2. **Hedged violations.** `violationMayBeDeviceTransitions` reads "The violation *may be caused by* device
 *    transitions", which my first rule called a softened verdict. It is the opposite: the violation is proven and
 *    its *attribution* is a hypothesis. Acting on that finding would have pushed someone toward asserting a cause
 *    NuSMV never established — the exact dishonesty this product is built to avoid.
 */

const i18nSource = () => readFileSync(join(__dirname, '../i18n.ts'), 'utf8')

/**
 * Extract a locale block by brace matching.
 *
 * `occurrence` matters: the file holds two locale pairs — a small spec-template block first, then the main
 * message catalogue. Taking the first gave 14 keys and a vacuously clean result.
 */
const extractLocale = (source: string, name: string, occurrence: number): string | null => {
  let start = -1
  for (let n = 0; n <= occurrence; n++) {
    start = source.indexOf(`${name}: {`, start + 1)
    if (start < 0) return null
  }
  let depth = 0
  let i = source.indexOf('{', start)
  const from = i
  for (; i < source.length; i++) {
    if (source[i] === '{') depth++
    else if (source[i] === '}') { depth--; if (depth === 0) break }
  }
  return source.slice(from, i + 1)
}

const flatten = (block: string): Map<string, string> => {
  const out = new Map<string, string>()
  const path: string[] = []
  for (const raw of block.split('\n')) {
    const line = raw.trim()
    if (!line || line.startsWith('//') || line.startsWith('*') || line.startsWith('/*')) continue
    const open = /^([a-zA-Z_$][\w$]*)\s*:\s*\{$/.exec(line)
    if (open) { path.push(open[1]); continue }
    if (/^\}[,]?$/.test(line)) { path.pop(); continue }
    const leaf = /^([a-zA-Z_$][\w$]*)\s*:\s*(['"`])([\s\S]*)$/.exec(line)
    if (leaf) {
      const rest = leaf[3]
      const end = rest.lastIndexOf(leaf[2])
      out.set([...path, leaf[1]].join('.'), end > -1 ? rest.slice(0, end) : rest)
    }
  }
  return out
}

describe('locale parity', () => {
  const locales = () => {
    const source = i18nSource()
    const zh = extractLocale(source, "'zh-CN'", 1)
    const en = extractLocale(source, 'en', 1)
    expect(zh, 'the zh-CN message catalogue should be readable').toBeTruthy()
    expect(en, 'the en message catalogue should be readable').toBeTruthy()
    return { zh: flatten(zh as string), en: flatten(en as string) }
  }

  it('parses a realistic number of keys, so a clean result is not vacuous', () => {
    // The guard that caught my own broken extraction: 14 keys parsed, both "no gaps" rules passing, nothing
    // actually checked. Without this the spec would certify whatever it managed to read.
    const { zh, en } = locales()
    expect(zh.size, 'zh-CN key count').toBeGreaterThan(800)
    expect(en.size, 'en key count').toBeGreaterThan(800)
  })

  it('defines every key in both locales', () => {
    const { zh, en } = locales()
    const missingInEn = [...zh.keys()].filter(k => !en.has(k))
    const missingInZh = [...en.keys()].filter(k => !zh.has(k))
    // Named, not counted: a reader needs to know which key to add.
    expect(missingInEn, 'keys present in zh-CN but missing from en').toEqual([])
    expect(missingInZh, 'keys present in en but missing from zh-CN').toEqual([])
  })

  it('uses the same interpolation placeholders in both locales', () => {
    const { zh, en } = locales()
    // The distinct set, because pluralization legitimately repeats a placeholder per form.
    const setOf = (v: string) =>
      [...new Set([...v.matchAll(/\{(\w+)\}/g)].map(m => m[1]))].sort().join(',')
    const mismatched: string[] = []
    for (const [key, value] of zh) {
      const other = en.get(key)
      if (other === undefined) continue
      if (setOf(value) !== setOf(other)) {
        mismatched.push(`${key} [zh:${setOf(value) || 'none'} vs en:${setOf(other) || 'none'}]`)
      }
    }
    // A dropped placeholder means the number the sentence is about silently disappears for those users.
    expect(mismatched, 'placeholder sets should match').toEqual([])
  })

  it('never lets an inconclusive outcome borrow the vocabulary of a proof', () => {
    const { en } = locales()
    // The narrow, load-bearing rule. `BUDGET_EXHAUSTED` and `INCONCLUSIVE` mean the search or the check did not
    // decide; wording them as "safe" or "proven" would state a result the engine never reached.
    const claimsProof = /\b(safe|proven|proved|guaranteed|cannot happen|never happens)\b/i
    const offenders: string[] = []
    for (const [key, value] of en) {
      if (!/inconclusive|exhaust/i.test(key)) continue
      if (claimsProof.test(value)) offenders.push(`${key}: "${value.slice(0, 70)}"`)
    }
    expect(offenders, 'an undecided outcome must not read as a proof').toEqual([])
  })

  it('makes every history-boundary notice say why the undo history goes, in both locales', () => {
    /*
     * The four confirmations that clear the undo journal must name the *cause*, not only the count.
     *
     * Stating "this discards {historyEntries} entries" and stopping is what made losing undo read as an
     * unrelated side effect of clearing the scene — it was reported as a bug when it is the design. The reason
     * differs by boundary: a scene boundary leaves each entry with nothing to return to, a template boundary
     * removes the manifest an entry's device snapshot needs. Both are expressed as an em-dash aside, which is
     * what this checks for; without it a future edit can drop the explanation in one locale silently.
     */
    const { en, zh } = locales()
    // `flatten` returns dotted paths, so these carry their `app.` namespace.
    const boundaryKeys = [
      'app.sceneClearConfirmMessage',
      'app.sceneImportConfirmMessage',
      'app.resetDefaultTemplatesNotice',
      'app.templateDeleteNoReferences'
    ]
    const offenders: string[] = []
    for (const [label, table] of [['en', en], ['zh', zh]] as const) {
      for (const key of boundaryKeys) {
        const value = table.get(key)
        if (!value) {
          offenders.push(`${label}.${key} is missing`)
          continue
        }
        if (!value.includes('{historyEntries}')) offenders.push(`${label}.${key} omits the entry count`)
        // `—` (en) and `——` (zh) both contain U+2014.
        if (!value.includes('—')) offenders.push(`${label}.${key} states the count but not the reason`)
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })
})

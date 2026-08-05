import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * The two TypeScript mirrors of the backend's `RuleDto` must describe it the same way.
 *
 * `api/board.ts` declares `BackendRuleDto` for the live-board read, and `types/model.ts` declares `ModelRule` for
 * the frozen playback scene — and `ModelPlaybackSceneDto` is `record(List<DeviceNodeDto> nodes, List<RuleDto>
 * rules)`, so both really are mirroring the same Java DTO over two endpoints. Nothing compared them, and they had
 * drifted: `id?: number` versus `id: number | null`, and `ruleString?: string` versus `string | null`.
 *
 * The nullable forms are the accurate ones (`RuleDto.id` is a `Long`; `ruleString` comes from `optionalText`,
 * which returns null), so the playback mirror forbade a value the server can send. No live misread resulted —
 * `playbackScene.ts` uses `rule.id ?? ruleIndex` and `rule.id == null`, which cover both — but a type that
 * contradicts the wire is a trap for the next reader, and the *next* field to diverge might not be handled so
 * defensively.
 *
 * This asserts on the declarations rather than on behaviour, which is the only option across the language
 * boundary — the same approach as `credentialLimitsMirror.spec.ts`.
 */

const source = (path: string) => readFileSync(join(__dirname, path), 'utf8')

/** The body of an `interface X { … }` block. */
const interfaceBody = (text: string, name: string): string => {
  const at = text.indexOf(`interface ${name} {`)
  expect(at, `${name} should be declared`).toBeGreaterThan(-1)
  return text.slice(at, at + text.slice(at).indexOf('\n}'))
}

/**
 * Whether a field admits an explicit `null`, which is the axis the two mirrors disagreed on.
 *
 * Must test for `null` specifically, not for "absence" generally. My first version accepted `?:` as sufficient,
 * so narrowing `id?: number | null` back to `id?: number` still passed — it would have shipped a guard blind to
 * the very drift it was written for. `RuleDto.id` is a `Long` and `ruleString` comes from `optionalText`, so both
 * arrive as JSON `null`, and `?:` alone does not describe that: a caller reading `rule.id === undefined` to mean
 * "no id" is wrong on a `null`.
 */
const admitsNull = (body: string, field: string): boolean => {
  const line = body.split(/\r?\n/).find(row => new RegExp(`^\\s*${field}\\??\\s*:`).test(row))
  expect(line, `${field} should be declared`).toBeTruthy()
  return /\bnull\b/.test(line!)
}

/**
 * Field names declared in a block.
 *
 * Indentation-agnostic on purpose: `api/board.ts` indents four spaces and `types/model.ts` two, and my first
 * version keyed on `^\s{2,4}` — which silently extracted *nothing* from the backend mirror and compared an empty
 * set against a full one. A scan that can return empty without failing is the shape of a test that cannot fail,
 * so this asserts the extraction found something before comparing.
 */
const fieldNames = (body: string) => {
  const names = new Set(
    body.split(/\r?\n/)
      .map(row => /^\s+([A-Za-z][A-Za-z0-9]*)\??\s*:/.exec(row)?.[1])
      .filter((name): name is string => Boolean(name)))
  expect(names.size, 'the field scan should not come back empty').toBeGreaterThan(0)
  return names
}

describe('RuleDto mirrors agree', () => {
  const board = source('../../api/board.ts')
  const model = source('../model.ts')

  it('lets both mirrors accept an explicit null id and ruleString', () => {
    const backend = interfaceBody(board, 'BackendRuleDto')
    const playback = interfaceBody(model, 'ModelRule')

    for (const field of ['id', 'ruleString']) {
      expect(admitsNull(backend, field), `BackendRuleDto.${field} must admit null`).toBe(true)
      expect(admitsNull(playback, field), `ModelRule.${field} must admit null`).toBe(true)
    }
  })

  it('declares the same command field names in both mirrors', () => {
    // A field added to one mirror and not the other is how the optionality drift started. Names only: the two
    // legitimately spell their nested shapes differently (inline object vs named interface).
    const backendCommand = fieldNames(
      board.slice(board.indexOf('command: {'), board.indexOf('ruleString: string | null')))
    const modelCommand = fieldNames(interfaceBody(model, 'ModelRuleCommand'))

    expect([...modelCommand].sort()).toEqual([...backendCommand].sort())
  })
})

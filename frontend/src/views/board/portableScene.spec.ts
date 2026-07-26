import { describe, expect, it } from 'vitest'
import { createSceneCodec, SCENE_FILE_SCHEMA, SCENE_FILE_VERSION } from './portableScene'

// The codec is the trust boundary for imported scene files, so these tests assert that
// malformed input is REJECTED rather than coerced into a half-valid board. The translator is
// stubbed to echo its key, which keeps assertions about *which* rejection fired readable.
const t = (key: string, params?: Record<string, unknown>) =>
  params ? `${key}:${JSON.stringify(params)}` : key

const codec = createSceneCodec(t)

const minimalScene = () => ({
  schema: SCENE_FILE_SCHEMA,
  version: SCENE_FILE_VERSION,
  templates: [],
  devices: [],
  environmentVariables: [],
  rules: [],
  specs: []
})

describe('scene file envelope validation', () => {
  it('accepts an empty but well-formed scene', () => {
    const scene = codec.normalizeSceneFile(minimalScene())
    expect(scene.schema).toBe(SCENE_FILE_SCHEMA)
    expect(scene.version).toBe(SCENE_FILE_VERSION)
    expect(scene.devices).toEqual([])
  })

  it.each([
    ['a non-object payload', 'not-a-scene'],
    ['null', null],
    ['an array', []]
  ])('rejects %s instead of treating it as an empty scene', (_label, payload) => {
    expect(() => codec.normalizeSceneFile(payload)).toThrow(/sceneImportInvalidFile/)
  })

  it('rejects a foreign schema rather than guessing the format', () => {
    expect(() => codec.normalizeSceneFile({ ...minimalScene(), schema: 'some.other.tool' }))
      .toThrow(/sceneImportInvalidFile/)
  })

  it('reports the unsupported version instead of importing it best-effort', () => {
    expect(() => codec.normalizeSceneFile({ ...minimalScene(), version: SCENE_FILE_VERSION - 1 }))
      .toThrow(/sceneImportUnsupportedVersion/)
  })

  it('rejects an unknown top-level field so silent data loss cannot happen', () => {
    expect(() => codec.normalizeSceneFile({ ...minimalScene(), somethingElse: 1 }))
      .toThrow(/sceneImportUnknownField/)
  })

  it.each(['templates', 'devices', 'environmentVariables', 'rules', 'specs'])(
    'requires %s to be an array', field => {
      expect(() => codec.normalizeSceneFile({ ...minimalScene(), [field]: {} }))
        .toThrow(/sceneImportArrayRequired/)
    })
})

describe('scene device identity', () => {
  it('rejects duplicate device ids instead of silently keeping the last one', () => {
    const devices = [
      { id: 'dup', label: 'A' },
      { id: 'dup', label: 'B' }
    ] as any
    expect(() => codec.assertUniqueSceneDeviceIds(devices))
      .toThrow(/sceneImportDuplicateDevice/)
  })

  it('accepts distinct device ids', () => {
    const devices = [
      { id: 'a', label: 'A' },
      { id: 'b', label: 'B' }
    ] as any
    expect(() => codec.assertUniqueSceneDeviceIds(devices)).not.toThrow()
  })
})

describe('integer range validation', () => {
  it('accepts an in-range integer', () => {
    expect(codec.requireIntegerInRange(5, 'steps', 1, 10)).toBe(5)
  })

  it.each([
    ['a non-integer', 2.5],
    ['a string', '5'],
    ['NaN', Number.NaN],
    ['below the minimum', 0],
    ['above the maximum', 11]
  ])('rejects %s', (_label, value) => {
    expect(() => codec.requireIntegerInRange(value, 'steps', 1, 10)).toThrow(/integerBetween/)
  })

  it('falls back only for null/undefined, not for an invalid value', () => {
    expect(codec.optionalIntegerInRange(undefined, 'steps', 7, 1, 10)).toBe(7)
    expect(codec.optionalIntegerInRange(null, 'steps', 7, 1, 10)).toBe(7)
    expect(() => codec.optionalIntegerInRange(99, 'steps', 7, 1, 10)).toThrow(/integerBetween/)
  })
})

describe('canonicalization', () => {
  it('is stable under key order so an exported scene round-trips byte-identically', () => {
    const a = codec.canonicalizeSceneFile(minimalScene() as any)
    const reordered = {
      specs: [], rules: [], environmentVariables: [], devices: [], templates: [],
      version: SCENE_FILE_VERSION, schema: SCENE_FILE_SCHEMA
    }
    const b = codec.canonicalizeSceneFile(reordered as any)
    expect(JSON.stringify(a)).toBe(JSON.stringify(b))
  })
})

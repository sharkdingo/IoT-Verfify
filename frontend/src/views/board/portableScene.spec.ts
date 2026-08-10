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

describe('scene specification variable conditions', () => {
  // A specification condition is reference-checked against the scene's devices, so the fixture
  // carries the device it names and the template that device instantiates.
  const sceneWithCondition = (condition: Record<string, unknown>) => ({
    ...minimalScene(),
    templates: [{
      name: 'Temperature Sensor',
      manifest: {
        Name: 'Temperature Sensor',
        Description: '',
        Modes: ['SensorState'],
        InitState: 'working',
        ImpactedVariables: [],
        InternalVariables: [
          { Name: 'temperature', IsInside: true, FalsifiableWhenCompromised: true, LowerBound: 0, UpperBound: 50, Trust: 'trusted', Privacy: 'public' }
        ],
        WorkingStates: [{ Name: 'working', Dynamics: [], Description: '', Trust: 'trusted', Privacy: 'public' }],
        APIs: []
      }
    }],
    devices: [{
      id: 'sensor-1',
      templateName: 'Temperature Sensor',
      label: 'Temperature Sensor',
      position: { x: 0, y: 0 },
      state: 'working',
      width: 120,
      height: 100
    }],
    specs: [{
      templateId: '1',
      aConditions: [condition],
      ifConditions: [],
      thenConditions: []
    }]
  })

  const variableCondition = (variableSource?: string) => ({
    deviceId: 'sensor-1',
    targetType: 'variable',
    key: 'temperature',
    ...(variableSource ? { variableSource } : {}),
    relation: '>',
    value: '28'
  })

  it('rejects a variable condition that does not say which value it means', () => {
    // Assigning a side would silently change what the imported specification asserts, and the two
    // sides differ exactly when a device is compromised.
    expect(() => codec.normalizeSceneFile(sceneWithCondition(variableCondition())))
      .toThrow(/sceneImportMissingField/)
    expect(() => codec.normalizeSceneFile(sceneWithCondition(variableCondition('whatever'))))
      .toThrow(/sceneImportInvalidEnum/)
  })

  it('keeps an explicit variable source through import', () => {
    const scene = codec.normalizeSceneFile(sceneWithCondition(variableCondition('reported')))
    expect(scene.specs[0].aConditions[0]).toMatchObject({ variableSource: 'reported' })
  })

  it('refuses the field on a condition type that has no such question', () => {
    expect(() => codec.normalizeSceneFile(sceneWithCondition({
      deviceId: 'sensor-1',
      targetType: 'state',
      key: 'state',
      variableSource: 'environment',
      relation: '=',
      value: 'open'
    }))).toThrow(/sceneImportUnexpectedField/)
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

  it('matches backend null omission while preserving non-null manifest values', () => {
    const explicitNull = {
      ...minimalScene(),
      templates: [{
        name: 'Alarm',
        manifest: {
          Name: 'Alarm',
          Description: '',
          InternalVariables: [{
            Name: 'level',
            IsInside: true,
            FalsifiableWhenCompromised: false,
            Trust: 'trusted',
            Privacy: 'public',
            LowerBound: 0,
            UpperBound: 1
          }],
          APIs: [{
            Name: 'off',
            StartState: 'on',
            EndState: 'off',
            Trigger: null,
            Signal: false,
            AcceptsContent: false
          }]
        }
      }]
    }
    const omitted = {
      ...minimalScene(),
      templates: [{
        name: 'Alarm',
        manifest: {
          APIs: [{
            AcceptsContent: false,
            Signal: false,
            EndState: 'off',
            Name: 'off',
            StartState: 'on'
          }],
          InternalVariables: [{
            UpperBound: 1,
            LowerBound: 0,
            Privacy: 'public',
            Trust: 'trusted',
            FalsifiableWhenCompromised: false,
            IsInside: true,
            Name: 'level'
          }],
          Description: '',
          Name: 'Alarm'
        }
      }]
    }

    const canonical = codec.canonicalizeSceneFile(explicitNull as any)
    expect(canonical).toEqual(codec.canonicalizeSceneFile(omitted as any))
    expect(canonical.templates[0].manifest).toMatchObject({
      Description: ''
    })
    expect(canonical.templates[0].manifest.APIs?.[0]).toMatchObject({
      AcceptsContent: false,
      Signal: false
    })
    expect(canonical.templates[0].manifest.APIs?.[0]).not.toHaveProperty('Trigger')
    expect(canonical.templates[0].manifest.InternalVariables?.[0]).toMatchObject({
      FalsifiableWhenCompromised: false,
      LowerBound: 0
    })
  })
})

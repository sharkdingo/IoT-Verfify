import { beforeEach, describe, expect, it, vi } from 'vitest'

vi.mock('./http', () => ({
  default: {
    get: vi.fn(),
    post: vi.fn(),
    put: vi.fn(),
    patch: vi.fn(),
    delete: vi.fn()
  }
}))

import http from './http'
import boardApi, { BOARD_RESPONSE_INCOMPLETE_CODE } from './board'
import type { DeviceNode } from '@/types/node'
import type { Specification } from '@/types/spec'

const resultEnvelope = (data: unknown) => ({ data: { data } })

const device: DeviceNode = {
  id: 'device_1',
  templateName: 'Sensor',
  label: 'Hall sensor',
  position: { x: 10, y: 20 },
  state: 'Working',
  width: 176,
  height: 128
}

const completeDeviceCreation = () => ({
  operation: 'created',
  affectedDevices: [device],
  currentNodes: [device],
  environmentVariables: [],
  environmentChanges: [],
  currentSpecifications: [],
  updatedSpecificationCount: 0,
  currentCount: 1
})

const template = {
  id: 4,
  name: 'Sensor',
  manifest: { Name: 'Sensor' },
  defaultTemplate: true
}

const completeTemplateResetPreview = () => ({
  operation: 'preview',
  impactToken: 'reset-impact-token',
  canApply: true,
  templateChanges: [{
    templateName: 'Sensor',
    changeType: 'REFRESH_DEFAULT',
    semanticsChanged: false
  }],
  affectedDevices: [],
  blockers: [],
  environmentChanges: [],
  currentTemplates: [template],
  environmentVariables: []
})

describe('board mutation response contracts', () => {
  beforeEach(() => {
    vi.clearAllMocks()
  })

  it('accepts a complete authoritative device-creation result', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope(completeDeviceCreation()))

    const result = await boardApi.addNodes([device])

    expect(result.affectedDevices).toEqual([device])
    expect(result.currentNodes).toEqual([device])
  })

  it('rejects a successful HTTP response that omits environment effects', async () => {
    const incomplete = completeDeviceCreation() as Record<string, unknown>
    delete incomplete.environmentChanges
    vi.mocked(http.post).mockResolvedValue(resultEnvelope(incomplete))

    await expect(boardApi.addNodes([device])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects a device result whose affected set does not match the request', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      ...completeDeviceCreation(),
      affectedDevices: []
    }))

    await expect(boardApi.addNodes([device])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('accepts a targeted layout result that preserves device semantics', async () => {
    const moved = { ...device, position: { x: 40, y: 50 }, width: 190, height: 140 }
    const response = {
      operation: 'updated',
      mutationType: 'layout',
      changedFields: ['position.x', 'position.y', 'width', 'height'],
      previousDevice: device,
      currentDevice: moved,
      currentNodes: [moved],
      currentCount: 1
    }
    vi.mocked(http.put).mockResolvedValue(resultEnvelope(response))

    await expect(boardApi.updateNodeLayout('device_1', {
      position: { x: 40, y: 50 },
      width: 190,
      height: 140
    })).resolves.toEqual(response)
  })

  it('rejects a layout result that silently changes runtime state', async () => {
    const moved = {
      ...device,
      position: { x: 40, y: 50 },
      state: 'unexpected'
    }
    vi.mocked(http.put).mockResolvedValue(resultEnvelope({
      operation: 'updated',
      mutationType: 'layout',
      changedFields: ['position.x', 'position.y'],
      previousDevice: device,
      currentDevice: moved,
      currentNodes: [moved],
      currentCount: 1
    }))

    await expect(boardApi.updateNodeLayout('device_1', {
      position: { x: 40, y: 50 },
      width: 176,
      height: 128
    })).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('accepts a targeted runtime result that preserves layout and identity', async () => {
    const configured = {
      ...device,
      state: 'active',
      currentStateTrust: 'trusted',
      currentStatePrivacy: 'private'
    }
    const response = {
      operation: 'updated',
      mutationType: 'runtime',
      changedFields: ['state', 'currentStateTrust', 'currentStatePrivacy'],
      previousDevice: device,
      currentDevice: configured,
      currentNodes: [configured],
      currentCount: 1
    }
    vi.mocked(http.put).mockResolvedValue(resultEnvelope(response))

    await expect(boardApi.updateNodeRuntime('device_1', {
      state: 'active',
      currentStateTrust: 'trusted',
      currentStatePrivacy: 'private'
    })).resolves.toEqual(response)
  })

  it('rejects a scene replacement response that omits a required collection', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      nodes: [device],
      environmentVariables: [],
      rules: [],
      specs: []
    }))

    await expect(boardApi.saveBoardBatch({
      impactToken: 'confirmed-board-impact',
      nodes: [device],
      environmentVariables: [],
      rules: [],
      specs: [],
      templateSnapshots: []
    })).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('validates the authoritative scene-replacement preview', async () => {
    const preview = {
      impactToken: 'current-board-impact',
      deviceCount: 2,
      environmentVariableCount: 1,
      ruleCount: 3,
      specificationCount: 4
    }
    vi.mocked(http.get).mockResolvedValue(resultEnvelope(preview))

    await expect(boardApi.previewBoardReplacement()).resolves.toEqual(preview)
    expect(vi.mocked(http.get)).toHaveBeenCalledWith('/board/replacement-preview')
  })

  it('sends a full scene and its confirmed impact token without null-preserve semantics', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      nodes: [],
      environmentVariables: [],
      rules: [],
      specs: [],
      createdTemplates: []
    }))

    await boardApi.saveBoardBatch({
      impactToken: 'current-board-impact',
      nodes: [],
      environmentVariables: [],
      rules: [],
      specs: [],
      templateSnapshots: []
    })

    expect(vi.mocked(http.post)).toHaveBeenCalledWith('/board/batch', {
      impactToken: 'current-board-impact',
      nodes: [],
      environmentVariables: [],
      rules: [],
      specs: [],
      templateSnapshots: []
    })
  })

  it('sends only structured specification semantics and not display caches', async () => {
    const specification: Specification = {
      id: 'spec-1',
      templateId: '1',
      templateLabel: 'Caller cache',
      formula: 'CTLSPEC FALSE',
      devices: [{ deviceId: 'wrong', deviceLabel: 'Wrong', selectedApis: [] }],
      aConditions: [{
        id: 'condition-cache',
        side: 'a',
        deviceId: 'device_1',
        deviceLabel: 'Stale label',
        targetType: 'state',
        key: 'state',
        relation: 'EQ',
        value: 'Working'
      }],
      ifConditions: [],
      thenConditions: []
    }
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      operation: 'created',
      affectedItem: specification,
      currentItems: [specification],
      currentCount: 1
    }))

    await boardApi.addSpec(specification)

    expect(vi.mocked(http.post)).toHaveBeenCalledWith('/board/specs', {
      id: 'spec-1',
      templateId: '1',
      aConditions: [{
        deviceId: 'device_1',
        targetType: 'state',
        key: 'state',
        relation: '=',
        value: 'Working'
      }],
      ifConditions: [],
      thenConditions: []
    })
  })

  it('accepts an itemized field-level Environment Pool mutation result', async () => {
    const before = { name: 'temperature', value: '27', trust: 'untrusted', privacy: 'private' }
    const after = { ...before, trust: 'trusted' }
    const response = {
      operation: 'updated',
      patchResults: [{
        name: 'temperature',
        suppliedFields: ['trust'],
        changedFields: ['trust'],
        preservedFields: ['value', 'privacy'],
        previousValue: before,
        currentValue: after
      }],
      environmentVariables: [after],
      environmentChanges: [{
        changeType: 'UPDATED',
        name: 'temperature',
        previousValue: before,
        currentValue: after
      }],
      currentCount: 1
    }
    vi.mocked(http.post).mockResolvedValue(resultEnvelope(response))

    await expect(boardApi.saveEnvironment([
      { name: 'temperature', trust: 'trusted' }
    ])).resolves.toEqual(response)
  })

  it('rejects an Environment Pool mutation result without per-patch reasons', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({ environmentVariables: [] }))

    await expect(boardApi.saveEnvironment([
      { name: 'temperature', trust: 'trusted' }
    ])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects a patch explanation that hides an overwritten field', async () => {
    const before = { name: 'temperature', value: '27', trust: 'untrusted', privacy: 'private' }
    const after = { name: 'temperature', value: '0', trust: 'trusted', privacy: 'public' }
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      operation: 'updated',
      patchResults: [{
        name: 'temperature',
        suppliedFields: ['trust'],
        changedFields: ['trust'],
        preservedFields: ['value', 'privacy'],
        previousValue: before,
        currentValue: after
      }],
      environmentVariables: [after],
      environmentChanges: [{
        changeType: 'UPDATED',
        name: 'temperature',
        previousValue: before,
        currentValue: after
      }],
      currentCount: 1
    }))

    await expect(boardApi.saveEnvironment([
      { name: 'temperature', trust: 'trusted' }
    ])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects a device type import result without its effective manifest', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({ name: 'Sensor' }))

    await expect(boardApi.addDeviceTemplate({
      name: 'Sensor',
      manifest: { Name: 'Sensor' }
    })).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects a default-device-type reset preview without itemized impact', async () => {
    vi.mocked(http.get).mockResolvedValue(resultEnvelope({
      operation: 'preview',
      impactToken: 'token',
      canApply: true
    }))

    await expect(boardApi.previewDefaultTemplateReset()).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('accepts a complete default-device-type reset preview', async () => {
    vi.mocked(http.get).mockResolvedValue(resultEnvelope(completeTemplateResetPreview()))

    await expect(boardApi.previewDefaultTemplateReset()).resolves.toEqual(completeTemplateResetPreview())
  })

  it('requires a stable reason code for every default-type reset blocker', async () => {
    vi.mocked(http.get).mockResolvedValue(resultEnvelope({
      ...completeTemplateResetPreview(),
      canApply: false,
      blockers: [{
        itemLabel: 'Hall sensor',
        reason: 'Unknown device template after reset.'
      }]
    }))

    await expect(boardApi.previewDefaultTemplateReset()).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects a committed reset whose final catalog contradicts its changes', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      ...completeTemplateResetPreview(),
      operation: 'reset',
      templateChanges: [{
        templateName: 'Sensor',
        changeType: 'REMOVE_OBSOLETE_DEFAULT',
        semanticsChanged: true
      }]
    }))

    await expect(boardApi.resetDefaultTemplates('reset-impact-token')).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects an incomplete deterministic duplicate-check result', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({ isDuplicate: false }))

    await expect(boardApi.checkDuplicateRule({
      id: 'rule_candidate',
      name: 'Motion turns on the light',
      sources: [{ fromId: 'device_1', fromApi: 'motion', itemType: 'api' }],
      toId: 'device_1',
      toApi: 'turn_on'
    })).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects an internally inconsistent AI similarity result', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      isSimilar: false,
      isDuplicate: true,
      requiresReview: true,
      matchedRule: 'Existing rule',
      similarity: 1,
      reasonCode: 'AI_DUPLICATE',
      reason: 'same semantics',
      message: 'duplicate'
    }))

    await expect(boardApi.checkRuleSimilarity({
      id: 'rule_candidate',
      name: 'Motion turns on the light',
      sources: [{ fromId: 'device_1', fromApi: 'motion', itemType: 'api' }],
      toId: 'device_1',
      toApi: 'turn_on'
    })).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('maps the authoritative automatic-fix rule snapshot into Board rules', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      applied: true,
      strategy: 'remove',
      verificationRechecked: true,
      appliedSuggestion: {
        strategy: 'remove',
        description: 'Remove the conflicting rule',
        verified: true,
        parameterAdjustments: [],
        conditionAdjustments: [],
        removedRuleDescriptions: ['Old rule']
      },
      previousRuleCount: 2,
      currentRuleCount: 1,
      message: 'Recomputed, verified, and removed one rule.',
      rules: [{
        id: 9,
        conditions: [{
          deviceName: 'sensor_1',
          attribute: 'motion',
          targetType: 'api'
        }],
        command: {
          deviceName: 'light_1',
          action: 'turn_on',
          contentDevice: null,
          content: null
        },
        ruleString: 'Motion turns on the light'
      }]
    }))

    const result = await boardApi.applyFix(7, {
      suggestionToken: 'signed-remove-suggestion',
      strategy: 'remove',
      description: 'Remove the conflicting rule',
      verified: true,
      parameterAdjustments: [],
      conditionAdjustments: [],
      removedRuleDescriptions: ['Old rule']
    })

    expect(result.rules).toEqual([expect.objectContaining({
      id: '9',
      name: 'Motion turns on the light',
      toId: 'light_1'
    })])
  })

  it('rejects an automatic-fix result whose rule count contradicts its snapshot', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      applied: true,
      strategy: 'condition',
      verificationRechecked: true,
      appliedSuggestion: {
        strategy: 'condition',
        description: 'Adjust a condition',
        verified: true,
        parameterAdjustments: [],
        conditionAdjustments: [{
          action: 'remove',
          attribute: 'motion',
          targetType: 'api',
          description: 'Remove the motion event from the automation.',
          ruleDescription: 'Motion turns on the light',
          deviceLabel: 'Hall sensor'
        }],
        removedRuleDescriptions: []
      },
      previousRuleCount: 1,
      currentRuleCount: 1,
      message: 'Applied.',
      rules: []
    }))

    await expect(boardApi.applyFix(7, {
      suggestionToken: 'signed-condition-suggestion',
      strategy: 'condition',
      description: 'Adjust a condition',
      verified: true,
      parameterAdjustments: [],
      conditionAdjustments: [],
      removedRuleDescriptions: []
    })).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })
})

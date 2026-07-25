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
import { FIX_RESPONSE_INCOMPLETE_CODE } from '@/utils/fixResponse'
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

const completeDeviceRename = (overrides: Record<string, unknown> = {}) => {
  const renamed = { ...device, label: 'Kitchen sensor' }
  return {
    operation: 'renamed',
    affectedDevices: [renamed],
    currentNodes: [renamed],
    environmentVariables: [],
    environmentChanges: [],
    currentSpecifications: [],
    previousLabel: 'Hall sensor',
    updatedSpecificationCount: 0,
    currentCount: 1,
    ...overrides
  }
}

const deletedRule = {
  id: 7,
  conditions: [{
    deviceName: device.id,
    attribute: 'motion',
    targetType: 'api'
  }],
  command: {
    deviceName: device.id,
    action: 'notify',
    contentDevice: null,
    content: null
  },
  ruleString: 'Motion sends a notification'
}

const confirmedRule = {
  id: '7',
  name: 'Motion sends a notification',
  sources: [{
    fromId: device.id,
    fromApi: 'motion',
    itemType: 'api' as const
  }],
  toId: device.id,
  toApi: 'notify'
}

const deletedSpecification: Specification = {
  id: 'spec-1',
  templateId: '1',
  templateLabel: 'Always',
  aConditions: [],
  ifConditions: [],
  thenConditions: [],
  devices: [{
    deviceId: device.id,
    deviceLabel: device.label,
    selectedApis: []
  }]
}

const environmentVariable = {
  name: 'ambientTemperature',
  value: '22',
  trust: 'trusted',
  privacy: 'public'
}

const completeDeviceDeletion = (operation: 'preview' | 'deleted') => ({
  operation,
  impactToken: 'device-delete-impact-token',
  deletedDevice: device,
  removedRules: [deletedRule],
  removedSpecifications: [deletedSpecification],
  currentNodes: operation === 'preview' ? [device] : [],
  environmentVariables: operation === 'preview' ? [environmentVariable] : [],
  environmentChanges: [{
    changeType: 'REMOVED',
    name: environmentVariable.name,
    previousValue: environmentVariable,
    currentValue: null,
    previousModelTokenSource: 'UNKNOWN',
    currentModelTokenSource: 'UNKNOWN'
  }],
  currentRules: operation === 'preview' ? [deletedRule] : [],
  currentSpecifications: operation === 'preview' ? [deletedSpecification] : []
})

const template = {
  id: 4,
  name: 'Sensor',
  manifest: { Name: 'Sensor' },
  defaultTemplate: true
}

const completeTemplateDeletion = (operation: 'preview' | 'deleted') => ({
  operation,
  impactToken: 'template-delete-impact-token',
  canDelete: true,
  template,
  ...(operation === 'deleted' ? { deletedTemplate: template } : {}),
  blockers: [],
  currentTemplates: operation === 'preview' ? [template] : []
})

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

  it.each([
    ['an affected device without its node contract', { affectedDevices: [{}] }],
    ['an authoritative node without its node contract', { currentNodes: [{}] }],
    ['a malformed environment variable', { environmentVariables: [{}] }],
    ['a malformed environment change', { environmentChanges: [{}] }],
    ['a malformed current specification', { currentSpecifications: [{}] }]
  ])('rejects a device mutation with %s', async (_label, overrides) => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      ...completeDeviceCreation(),
      ...overrides
    }))

    await expect(boardApi.addNodes([device])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects a snapshot whose nested node is malformed despite HTTP 200', async () => {
    vi.mocked(http.get).mockResolvedValue(resultEnvelope({
      nodes: [{}],
      environmentVariables: [],
      rules: [],
      specifications: [],
      deviceTemplates: []
    }))

    await expect(boardApi.getSnapshot()).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects a snapshot containing duplicate authoritative identities', async () => {
    vi.mocked(http.get).mockResolvedValue(resultEnvelope({
      nodes: [device, { ...device }],
      environmentVariables: [],
      rules: [],
      specifications: [],
      deviceTemplates: []
    }))

    await expect(boardApi.getSnapshot()).rejects.toMatchObject({
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

  it('rejects a targeted update whose matching node snapshot is malformed', async () => {
    const malformed = {
      ...device,
      label: '',
      position: { x: 40, y: 50 },
      width: 190,
      height: 140
    }
    vi.mocked(http.put).mockResolvedValue(resultEnvelope({
      operation: 'updated',
      mutationType: 'layout',
      changedFields: ['position.x', 'position.y', 'width', 'height'],
      previousDevice: device,
      currentDevice: malformed,
      currentNodes: [malformed],
      currentCount: 1
    }))

    await expect(boardApi.updateNodeLayout('device_1', {
      position: { x: 40, y: 50 },
      width: 190,
      height: 140
    })).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
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
      expected: {
        state: device.state,
        variables: [],
        privacies: []
      },
      desired: {
        state: 'active',
        currentStateTrust: 'trusted',
        currentStatePrivacy: 'private'
      }
    })).resolves.toEqual(response)

    expect(http.put).toHaveBeenCalledWith('/board/nodes/device_1/runtime', {
      expected: {
        state: device.state,
        variables: [],
        privacies: []
      },
      desired: {
        state: 'active',
        currentStateTrust: 'trusted',
        currentStatePrivacy: 'private'
      }
    })
  })

  it('accepts inherited variable trust when the server serializes it as null', async () => {
    const configured = {
      ...device,
      variables: [{ name: 'mode', value: 'eco', trust: null }]
    }
    const response = {
      operation: 'updated',
      mutationType: 'runtime',
      changedFields: ['variables'],
      previousDevice: device,
      currentDevice: configured,
      currentNodes: [configured],
      currentCount: 1
    }
    vi.mocked(http.put).mockResolvedValue(resultEnvelope(response))

    await expect(boardApi.updateNodeRuntime('device_1', {
      expected: { state: device.state },
      desired: { variables: [{ name: 'mode', value: 'eco' }] }
    })).resolves.toEqual(response)
  })

  it('sends the label observed when the rename dialog opened', async () => {
    vi.mocked(http.patch).mockResolvedValue(resultEnvelope(completeDeviceRename()))

    await boardApi.renameNode('device_1', 'Kitchen sensor', 'Hall sensor')

    expect(vi.mocked(http.patch)).toHaveBeenCalledWith('/board/nodes/device_1/label', {
      label: 'Kitchen sensor',
      expectedLabel: 'Hall sensor'
    })
  })

  it.each([
    ['an unchanged affected device', { affectedDevices: [device] }],
    ['an unchanged authoritative device', { currentNodes: [device] }],
    ['a different previous label', { previousLabel: 'Renamed elsewhere' }],
    ['a negative specification count', { updatedSpecificationCount: -1 }],
    ['a fractional specification count', { updatedSpecificationCount: 0.5 }]
  ])('rejects a rename response with %s', async (_label, overrides) => {
    vi.mocked(http.patch).mockResolvedValue(resultEnvelope(completeDeviceRename(overrides)))

    await expect(boardApi.renameNode(
      'device_1',
      'Kitchen sensor',
      'Hall sensor'
    )).rejects.toMatchObject({ code: BOARD_RESPONSE_INCOMPLETE_CODE })
  })

  it('accepts and maps a complete authoritative device-deletion preview', async () => {
    vi.mocked(http.get).mockResolvedValue(resultEnvelope(completeDeviceDeletion('preview')))

    const result = await boardApi.previewNodeDeletion(device.id)

    expect(result.deletedDevice).toEqual(device)
    expect(result.removedRules).toEqual([expect.objectContaining({
      id: '7',
      name: 'Motion sends a notification',
      toId: device.id
    })])
  })

  it('accepts a nullable rule preview from the backend contract', async () => {
    const response = {
      ...completeDeviceDeletion('preview'),
      removedRules: [{ ...deletedRule, ruleString: null }]
    }
    vi.mocked(http.get).mockResolvedValue(resultEnvelope(response))

    await expect(boardApi.previewNodeDeletion(device.id)).resolves.toEqual(
      expect.objectContaining({ removedRules: [expect.objectContaining({ name: '' })] })
    )
  })

  it('accepts a complete deletion result that omits the deleted device', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope(completeDeviceDeletion('deleted')))

    await expect(boardApi.deleteNode(
      device.id,
      'device-delete-impact-token'
    )).resolves.toEqual(expect.objectContaining({
      operation: 'deleted',
      currentNodes: []
    }))
  })

  it.each([
    ['a deleted device without identity', () => ({
      ...completeDeviceDeletion('preview'),
      deletedDevice: {}
    })],
    ['a different deleted device', () => ({
      ...completeDeviceDeletion('preview'),
      deletedDevice: { ...device, id: 'device_2' }
    })],
    ['a current device without canvas coordinates', () => ({
      ...completeDeviceDeletion('preview'),
      currentNodes: [{ ...device, position: null }]
    })],
    ['a deleted device with an out-of-range canvas size', () => ({
      ...completeDeviceDeletion('preview'),
      deletedDevice: { ...device, width: 2001 }
    })],
    ['a current device with a malformed runtime collection', () => ({
      ...completeDeviceDeletion('preview'),
      currentNodes: [{ ...device, variables: { name: 'mode', value: 'active' } }]
    })],
    ['a current device with a null runtime member', () => ({
      ...completeDeviceDeletion('preview'),
      currentNodes: [{ ...device, variables: [null] }]
    })],
    ['a current device with duplicate runtime names', () => ({
      ...completeDeviceDeletion('preview'),
      currentNodes: [{
        ...device,
        variables: [
          { name: 'mode', value: 'active' },
          { name: 'mode', value: 'idle' }
        ]
      }]
    })],
    ['duplicate current device ids', () => ({
      ...completeDeviceDeletion('preview'),
      currentNodes: [device, { ...device }]
    })],
    ['a preview that omits its target', () => ({
      ...completeDeviceDeletion('preview'),
      currentNodes: []
    })],
    ['a null removed rule', () => ({
      ...completeDeviceDeletion('preview'),
      removedRules: [null]
    })],
    ['a rule without persisted identity', () => ({
      ...completeDeviceDeletion('preview'),
      removedRules: [{ ...deletedRule, id: null }]
    })],
    ['a malformed current rule command', () => ({
      ...completeDeviceDeletion('preview'),
      currentRules: [{ ...deletedRule, command: null }]
    })],
    ['duplicate removed rule identities', () => ({
      ...completeDeviceDeletion('preview'),
      removedRules: [deletedRule, { ...deletedRule }]
    })],
    ['duplicate current rule identities', () => ({
      ...completeDeviceDeletion('preview'),
      currentRules: [deletedRule, { ...deletedRule }]
    })],
    ['a previewed removed rule absent from current rules', () => ({
      ...completeDeviceDeletion('preview'),
      currentRules: []
    })],
    ['an invalid rule condition kind', () => ({
      ...completeDeviceDeletion('preview'),
      removedRules: [{
        ...deletedRule,
        conditions: [{ ...deletedRule.conditions[0], targetType: 'event' }]
      }]
    })],
    ['a non-text rule condition value', () => ({
      ...completeDeviceDeletion('preview'),
      removedRules: [{
        ...deletedRule,
        conditions: [{
          deviceName: device.id,
          attribute: 'temperature',
          targetType: 'variable',
          relation: '>',
          value: { degrees: 30 }
        }]
      }]
    })],
    ['a null removed specification', () => ({
      ...completeDeviceDeletion('preview'),
      removedSpecifications: [null]
    })],
    ['a malformed specification condition', () => ({
      ...completeDeviceDeletion('preview'),
      removedSpecifications: [{
        ...deletedSpecification,
        aConditions: [{}]
      }]
    })],
    ['duplicate removed specification identities', () => ({
      ...completeDeviceDeletion('preview'),
      removedSpecifications: [deletedSpecification, { ...deletedSpecification }]
    })],
    ['duplicate current specification identities', () => ({
      ...completeDeviceDeletion('preview'),
      currentSpecifications: [deletedSpecification, { ...deletedSpecification }]
    })],
    ['a previewed removed specification absent from current specifications', () => ({
      ...completeDeviceDeletion('preview'),
      currentSpecifications: []
    })],
    ['a trust specification without property scope', () => ({
      ...completeDeviceDeletion('preview'),
      removedSpecifications: [{
        ...deletedSpecification,
        aConditions: [{
          deviceId: device.id,
          targetType: 'trust',
          key: 'mode',
          relation: '=',
          value: 'trusted'
        }]
      }]
    })],
    ['a non-property specification carrying property scope', () => ({
      ...completeDeviceDeletion('preview'),
      removedSpecifications: [{
        ...deletedSpecification,
        aConditions: [{
          deviceId: device.id,
          targetType: 'state',
          key: 'state',
          propertyScope: 'state',
          relation: '=',
          value: 'active'
        }]
      }]
    })],
    ['an uncanonicalized specification target type', () => ({
      ...completeDeviceDeletion('preview'),
      removedSpecifications: [{
        ...deletedSpecification,
        aConditions: [{
          deviceId: device.id,
          targetType: 'STATE',
          key: 'state',
          relation: '=',
          value: 'active'
        }]
      }]
    })],
    ['a specification with an unsupported relation', () => ({
      ...completeDeviceDeletion('preview'),
      removedSpecifications: [{
        ...deletedSpecification,
        aConditions: [{
          deviceId: device.id,
          targetType: 'state',
          key: 'state',
          relation: 'approximately',
          value: 'active'
        }]
      }]
    })],
    ['an environment variable without a name', () => ({
      ...completeDeviceDeletion('preview'),
      environmentVariables: [{}]
    })],
    ['an environment variable without complete security labels', () => ({
      ...completeDeviceDeletion('preview'),
      environmentVariables: [{ name: 'ambientTemperature', value: '22' }]
    })],
    ['a null environment change', () => ({
      ...completeDeviceDeletion('preview'),
      environmentChanges: [null]
    })],
    ['an invalid environment change type', () => ({
      ...completeDeviceDeletion('preview'),
      environmentChanges: [{
        ...completeDeviceDeletion('preview').environmentChanges[0],
        changeType: 'REPLACED'
      }]
    })],
    ['an environment change whose values contradict its type', () => ({
      ...completeDeviceDeletion('preview'),
      environmentChanges: [{
        ...completeDeviceDeletion('preview').environmentChanges[0],
        changeType: 'UPDATED',
        currentValue: null
      }]
    })]
  ])('rejects a device-deletion preview with %s', async (_label, createResponse) => {
    vi.mocked(http.get).mockResolvedValue(resultEnvelope(createResponse()))

    await expect(boardApi.previewNodeDeletion(device.id)).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects a deletion result that still contains the deleted device', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      ...completeDeviceDeletion('deleted'),
      currentNodes: [device]
    }))

    await expect(boardApi.deleteNode(
      device.id,
      'device-delete-impact-token'
    )).rejects.toMatchObject({ code: BOARD_RESPONSE_INCOMPLETE_CODE })
  })

  it('rejects a device deletion result for a different confirmed impact token', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      ...completeDeviceDeletion('deleted'),
      impactToken: 'different-device-delete-impact-token'
    }))

    await expect(boardApi.deleteNode(
      device.id,
      'device-delete-impact-token'
    )).rejects.toMatchObject({ code: BOARD_RESPONSE_INCOMPLETE_CODE })
  })

  it.each([
    ['rule', { currentRules: [deletedRule] }],
    ['specification', { currentSpecifications: [deletedSpecification] }]
  ])('rejects a deletion result that retains a removed %s', async (_label, overrides) => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      ...completeDeviceDeletion('deleted'),
      ...overrides
    }))

    await expect(boardApi.deleteNode(
      device.id,
      'device-delete-impact-token'
    )).rejects.toMatchObject({ code: BOARD_RESPONSE_INCOMPLETE_CODE })
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

  it('rejects a specification mutation whose affected item is malformed', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      operation: 'created',
      affectedItem: {},
      currentItems: [deletedSpecification],
      currentCount: 1
    }))

    await expect(boardApi.addSpec({
      id: 'spec-1',
      templateId: '1',
      templateLabel: 'Always',
      aConditions: [],
      ifConditions: [],
      thenConditions: [],
      devices: []
    })).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects a specification creation response for a different requested id', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      operation: 'created',
      affectedItem: { ...deletedSpecification, id: 'spec-2' },
      currentItems: [{ ...deletedSpecification, id: 'spec-2' }],
      currentCount: 1
    }))

    await expect(boardApi.addSpec(deletedSpecification)).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects a rule mutation whose affected item is malformed', async () => {
    vi.mocked(http.delete).mockResolvedValue(resultEnvelope({
      operation: 'deleted',
      affectedItem: {},
      currentItems: [deletedRule],
      currentCount: 1
    }))

    await expect(boardApi.removeRule(confirmedRule)).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('sends the confirmed rule snapshot and rejects a deletion response for another id', async () => {
    vi.mocked(http.delete).mockResolvedValue(resultEnvelope({
      operation: 'deleted',
      affectedItem: { ...deletedRule, id: 8 },
      currentItems: [],
      currentCount: 0
    }))

    await expect(boardApi.removeRule(confirmedRule)).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
    expect(vi.mocked(http.delete)).toHaveBeenCalledWith('/board/rules/7', {
      data: expect.objectContaining({
        id: 7,
        ruleString: confirmedRule.name,
        conditions: [expect.objectContaining({
          deviceName: device.id,
          attribute: 'motion',
          targetType: 'api'
        })]
      })
    })
  })

  it('sends the complete expected and desired rule order for compare-and-set reordering', async () => {
    const secondRule = { ...deletedRule, id: 8, ruleString: 'Second rule' }
    vi.mocked(http.put).mockResolvedValue(resultEnvelope([secondRule, deletedRule]))

    await boardApi.reorderRules(['7', '8'], ['8', '7'])

    expect(vi.mocked(http.put)).toHaveBeenCalledWith('/board/rules/order', {
      expectedRuleIds: [7, 8],
      ruleIds: [8, 7]
    })
  })

  it('sends only authored specification fields with a confirmed deletion', async () => {
    vi.mocked(http.delete).mockResolvedValue(resultEnvelope({
      operation: 'deleted',
      affectedItem: deletedSpecification,
      currentItems: [],
      currentCount: 0
    }))

    await expect(boardApi.removeSpec(deletedSpecification)).resolves.toMatchObject({
      operation: 'deleted',
      affectedItem: { id: deletedSpecification.id }
    })
    expect(vi.mocked(http.delete)).toHaveBeenCalledWith('/board/specs/spec-1', {
      data: {
        id: 'spec-1',
        templateId: '1',
        aConditions: [],
        ifConditions: [],
        thenConditions: []
      }
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

    await expect(boardApi.saveEnvironment([{
      name: 'temperature',
      expected: { value: '27', trust: 'untrusted', privacy: 'private' },
      desired: { trust: 'trusted' }
    }])).resolves.toEqual(response)
  })

  it('rejects a null value in an authoritative Environment Pool mutation result', async () => {
    const before = { name: 'signal', value: 'manual', trust: 'untrusted', privacy: 'public' }
    const after = { ...before, value: null, trust: 'trusted' }
    const response = {
      operation: 'updated',
      patchResults: [{
        name: 'signal',
        suppliedFields: ['trust'],
        changedFields: ['trust'],
        preservedFields: ['value', 'privacy'],
        previousValue: before,
        currentValue: after
      }],
      environmentVariables: [after],
      environmentChanges: [{
        changeType: 'UPDATED',
        name: 'signal',
        previousValue: before,
        currentValue: after
      }],
      currentCount: 1
    }
    vi.mocked(http.post).mockResolvedValue(resultEnvelope(response))

    await expect(boardApi.saveEnvironment([{
      name: 'signal',
      expected: before,
      desired: { trust: 'trusted' }
    }])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects a null value from the authoritative Environment Pool read', async () => {
    const response = [{ name: 'signal', value: null, trust: 'untrusted', privacy: 'public' }]
    vi.mocked(http.get).mockResolvedValue(resultEnvelope(response))

    await expect(boardApi.getEnvironment()).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects an Environment Pool read that omits the authoritative value field', async () => {
    vi.mocked(http.get).mockResolvedValue(resultEnvelope([{
      name: 'signal',
      trust: 'untrusted',
      privacy: 'public'
    }]))

    await expect(boardApi.getEnvironment()).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects malformed Environment Pool patches before making a request', async () => {
    await expect(boardApi.saveEnvironment([{
      name: 'temperature',
      expected: { trust: 'untrusted', privacy: 'private' },
      desired: { trust: 'trusted' }
    } as any])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
    await expect(boardApi.saveEnvironment([{
      name: 'temperature',
      expected: { value: null, trust: 'untrusted', privacy: 'private' },
      desired: { trust: 'trusted' }
    } as any])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
    await expect(boardApi.saveEnvironment([{
      name: 'temperature',
      expected: { value: '27', trust: 'untrusted', privacy: 'private' },
      desired: { value: null }
    } as any])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
    await expect(boardApi.saveEnvironment([{
      name: 'temperature',
      expected: { value: '27', trust: 'untrusted', privacy: 'private' },
      desired: { trust: 7 }
    } as any])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
    await expect(boardApi.saveEnvironment([{
      name: 'temperature',
      expected: { value: '27', trust: 'untrusted', privacy: 'private' },
      desired: { value: ' ' }
    }])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
    await expect(boardApi.saveEnvironment([{
      name: 'temperature',
      expected: { value: '27', trust: 'untrusted', privacy: 'private' },
      desired: { trust: null }
    } as any])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
    expect(http.post).not.toHaveBeenCalled()
  })

  it('rejects a success response that did not apply the desired Environment Pool field', async () => {
    const unchanged = { name: 'temperature', value: '27', trust: 'untrusted', privacy: 'private' }
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      operation: 'unchanged',
      patchResults: [{
        name: 'temperature',
        suppliedFields: ['trust'],
        changedFields: [],
        preservedFields: ['value', 'privacy'],
        previousValue: unchanged,
        currentValue: unchanged
      }],
      environmentVariables: [unchanged],
      environmentChanges: [],
      currentCount: 1
    }))

    await expect(boardApi.saveEnvironment([{
      name: 'temperature',
      expected: unchanged,
      desired: { trust: 'trusted' }
    }])).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects an Environment Pool mutation result without per-patch reasons', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({ environmentVariables: [] }))

    await expect(boardApi.saveEnvironment([{
      name: 'temperature',
      expected: { value: '27', trust: 'untrusted', privacy: 'private' },
      desired: { trust: 'trusted' }
    }])).rejects.toMatchObject({
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

    await expect(boardApi.saveEnvironment([{
      name: 'temperature',
      expected: { value: '27', trust: 'untrusted', privacy: 'private' },
      desired: { trust: 'trusted' }
    }])).rejects.toMatchObject({
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

  it.each([
    ['an empty manifest', { id: 4, name: 'Sensor', manifest: {}, defaultTemplate: false }],
    ['a missing persisted id', { ...template, id: undefined }],
    ['missing template provenance', { ...template, defaultTemplate: undefined }],
    ['a mismatched manifest name', {
      id: 4,
      name: 'Sensor',
      manifest: { Name: 'Actuator' },
      defaultTemplate: false
    }]
  ])('rejects a device type response with %s', async (_label, response) => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope(response))

    await expect(boardApi.addDeviceTemplate({
      name: 'Sensor',
      manifest: { Name: 'Sensor' }
    })).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects duplicate device type identities in the catalog', async () => {
    vi.mocked(http.get).mockResolvedValue(resultEnvelope([
      template,
      { ...template, id: 5 }
    ]))

    await expect(boardApi.getDeviceTemplates()).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('accepts a device-type deletion preview for the requested template', async () => {
    vi.mocked(http.get).mockResolvedValue(resultEnvelope(completeTemplateDeletion('preview')))

    await expect(boardApi.previewDeviceTemplateDeletion(template.id)).resolves.toEqual(
      completeTemplateDeletion('preview')
    )
    expect(vi.mocked(http.get)).toHaveBeenCalledWith('/board/templates/4/deletion-preview')
  })

  it.each([
    ['the wrong operation', { operation: 'deleted' }],
    ['a blank impact token', { impactToken: ' ' }],
    ['a different target identity', {
      template: { ...template, id: 5 },
      currentTemplates: [{ ...template, id: 5 }]
    }],
    ['a catalog that omits the previewed target', { currentTemplates: [] }],
    ['a catalog whose target snapshot differs from the preview', {
      currentTemplates: [{ ...template, defaultTemplate: false }]
    }],
    ['duplicate catalog identities', {
      currentTemplates: [
        template,
        { ...template, name: 'Actuator', manifest: { Name: 'Actuator' } }
      ]
    }]
  ])('rejects a device-type deletion preview with %s', async (_label, overrides) => {
    vi.mocked(http.get).mockResolvedValue(resultEnvelope({
      ...completeTemplateDeletion('preview'),
      ...overrides
    }))

    await expect(boardApi.previewDeviceTemplateDeletion(template.id)).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
  })

  it('rejects a device-type deletion response for another requested template', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      ...completeTemplateDeletion('deleted'),
      template: { ...template, id: 5 },
      deletedTemplate: { ...template, id: 5 }
    }))

    await expect(boardApi.deleteDeviceTemplate(
      template.id,
      'template-delete-impact-token'
    )).rejects.toMatchObject({ code: BOARD_RESPONSE_INCOMPLETE_CODE })
  })

  it('accepts a device-type deletion result for the confirmed snapshot and token', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope(completeTemplateDeletion('deleted')))

    await expect(boardApi.deleteDeviceTemplate(
      template.id,
      'template-delete-impact-token'
    )).resolves.toEqual(completeTemplateDeletion('deleted'))
  })

  it('rejects a device-type deletion result for a different confirmed impact token', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      ...completeTemplateDeletion('deleted'),
      impactToken: 'different-template-delete-impact-token'
    }))

    await expect(boardApi.deleteDeviceTemplate(
      template.id,
      'template-delete-impact-token'
    )).rejects.toMatchObject({ code: BOARD_RESPONSE_INCOMPLETE_CODE })
  })

  it('rejects an Environment Pool response containing an unvalidated change row', async () => {
    const before = { name: 'temperature', value: '27', trust: 'untrusted', privacy: 'private' }
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      operation: 'updated',
      patchResults: [{
        name: 'temperature',
        suppliedFields: ['trust'],
        changedFields: ['trust'],
        preservedFields: ['value', 'privacy'],
        previousValue: before,
        currentValue: { ...before, trust: 'trusted' }
      }],
      environmentVariables: [{ ...before, trust: 'trusted' }],
      environmentChanges: [{}],
      currentCount: 1
    }))

    await expect(boardApi.saveEnvironment([{
      name: 'temperature',
      expected: before,
      desired: { trust: 'trusted' }
    }])).rejects.toMatchObject({
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

  it('rejects a reset preview containing a null environment value', async () => {
    const response = {
      ...completeTemplateResetPreview(),
      environmentVariables: [{
        name: 'signal',
        value: null,
        trust: 'untrusted',
        privacy: 'public'
      }]
    }
    vi.mocked(http.get).mockResolvedValue(resultEnvelope(response))

    await expect(boardApi.previewDefaultTemplateReset()).rejects.toMatchObject({
      code: BOARD_RESPONSE_INCOMPLETE_CODE
    })
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

  it('rejects invalid environment token provenance in a reset preview', async () => {
    vi.mocked(http.get).mockResolvedValue(resultEnvelope({
      ...completeTemplateResetPreview(),
      environmentChanges: [{
        changeType: 'ADDED',
        name: 'weather',
        currentValue: { name: 'weather', value: 'sunny' },
        previousModelTokenSource: 'UNKNOWN',
        currentModelTokenSource: 'UNVERIFIED'
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

  it('accepts a committed reset for the confirmed impact token', async () => {
    const response = {
      ...completeTemplateResetPreview(),
      operation: 'reset' as const
    }
    vi.mocked(http.post).mockResolvedValue(resultEnvelope(response))

    await expect(boardApi.resetDefaultTemplates('reset-impact-token')).resolves.toEqual(response)
  })

  it('rejects a committed reset for a different confirmed impact token', async () => {
    vi.mocked(http.post).mockResolvedValue(resultEnvelope({
      ...completeTemplateResetPreview(),
      operation: 'reset',
      impactToken: 'different-reset-impact-token'
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

  it('pins every automatic-fix lifecycle request to the initiating credential', async () => {
    const authToken = 'alice-owner-token'
    const requestId = 'fix-request-1'
    const signal = new AbortController().signal
    const transportError = new Error('transport lost')
    vi.mocked(http.post).mockRejectedValueOnce(transportError)

    await expect(boardApi.fixTrace(7, { strategies: ['parameter'] }, {
      authToken,
      requestId,
      signal
    })).rejects.toBe(transportError)
    expect(http.post).toHaveBeenCalledWith(
      '/verify/traces/7/fix',
      { strategies: ['parameter'] },
      expect.objectContaining({
        headers: { Authorization: `Bearer ${authToken}` },
        params: { requestId },
        signal
      })
    )

    vi.mocked(http.delete).mockResolvedValueOnce(resultEnvelope(true))
    await expect(boardApi.cancelFixRequest(requestId, authToken)).resolves.toBe(true)
    expect(http.delete).toHaveBeenCalledWith(
      `/verify/fix-requests/${requestId}`,
      {
        timeout: 2500,
        headers: { Authorization: `Bearer ${authToken}` }
      }
    )

    vi.mocked(http.get).mockResolvedValueOnce(resultEnvelope({
      requestId,
      state: 'RUNNING',
      stage: 'SEARCHING_AND_VERIFYING',
      elapsedMs: 10
    }))
    await expect(boardApi.getFixRequestStatus(requestId, authToken)).resolves.toMatchObject({
      requestId,
      state: 'RUNNING'
    })
    expect(http.get).toHaveBeenCalledWith(
      `/verify/fix-requests/${requestId}`,
      {
        timeout: 2500,
        headers: { Authorization: `Bearer ${authToken}` }
      }
    )
  })

  it('bounds interactive recommendation cancellation and status reads', async () => {
    const authToken = 'recommendation-owner-token'
    const requestId = 'recommendation-request-1'
    vi.mocked(http.delete).mockResolvedValueOnce(resultEnvelope(true))

    await expect(boardApi.cancelRecommendation(requestId, authToken)).resolves.toBe(true)
    expect(http.delete).toHaveBeenCalledWith(
      `/board/recommendations/${requestId}`,
      {
        timeout: 2500,
        headers: { Authorization: `Bearer ${authToken}` }
      }
    )

    vi.mocked(http.get).mockResolvedValueOnce(resultEnvelope({
      requestId,
      state: 'RUNNING',
      stage: 'RUNNING',
      elapsedMs: 10
    }))
    await expect(boardApi.getRecommendationStatus(requestId, authToken)).resolves.toMatchObject({
      requestId,
      state: 'RUNNING'
    })
    expect(http.get).toHaveBeenCalledWith(
      `/board/recommendations/${requestId}`,
      {
        timeout: 2500,
        headers: { Authorization: `Bearer ${authToken}` }
      }
    )
  })

  it('pins every recommendation POST to its explicit owner credential', async () => {
    const authToken = 'alice-recommendation-token'
    const standalone = {
      message: 'No applicable recommendations.',
      count: 0,
      requestedCount: 5,
      validatedCount: 0,
      filteredCount: 0,
      filteredItems: [],
      adjustedCount: 0,
      adjustedItems: [],
      rawCandidateCount: 0,
      inspectedCount: 0,
      truncatedCount: 0,
      recommendations: []
    }
    const scenarioRequest = {
      minDevices: 1,
      minRules: 1,
      minSpecs: 1,
      maxDevices: 4,
      maxRules: 4,
      maxSpecs: 4
    }
    vi.mocked(http.post)
      .mockResolvedValueOnce(resultEnvelope(standalone))
      .mockResolvedValueOnce(resultEnvelope(standalone))
      .mockResolvedValueOnce(resultEnvelope({
        ...standalone,
        requestedCount: 3,
        scenarioName: '',
        rationale: '',
        objectiveTargets: { minDevices: 1, minRules: 1, minSpecs: 1 },
        objectiveStatus: 'PARTIAL',
        objectiveIssues: [
          { code: 'NO_DEVICES', message: 'No devices.' },
          { code: 'NO_AUTOMATION_RULES', message: 'No rules.' },
          { code: 'NO_SPECIFICATIONS', message: 'No specifications.' }
        ],
        verificationReady: false,
        readinessIssues: [
          { code: 'NO_DEVICES', message: 'No devices.' },
          { code: 'NO_SPECIFICATIONS', message: 'No specifications.' }
        ],
        semanticWarnings: [],
        scene: {
          templates: [],
          devices: [],
          environmentVariables: [],
          rules: [],
          specs: []
        }
      }))

    await boardApi.recommendRelatedDevices({
      authToken,
      requestId: 'device-recommendation-1'
    })
    await boardApi.recommendSpecifications({
      authToken,
      requestId: 'spec-recommendation-1'
    })
    await boardApi.recommendScenario(scenarioRequest, {
      authToken,
      requestId: 'scenario-recommendation-1'
    })

    expect(vi.mocked(http.post).mock.calls[0][2]).toMatchObject({
      timeout: 0,
      headers: { Authorization: `Bearer ${authToken}` }
    })
    expect(vi.mocked(http.post).mock.calls[1][2]).toMatchObject({
      timeout: 0,
      headers: { Authorization: `Bearer ${authToken}` }
    })
    expect(vi.mocked(http.post).mock.calls[2][2]).toMatchObject({
      timeout: 0,
      headers: { Authorization: `Bearer ${authToken}` }
    })
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
      code: FIX_RESPONSE_INCOMPLETE_CODE
    })
  })
})

import type { ModelPlaybackScene } from '@/types/model'

type PlaybackSceneFailure = (detail: string) => never

const record = (value: unknown, field: string, fail: PlaybackSceneFailure): Record<string, any> => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) fail(`${field} must be an object`)
  return value as Record<string, any>
}

const nonBlank = (value: unknown, field: string, fail: PlaybackSceneFailure): string => {
  if (typeof value !== 'string' || !value.trim()) fail(`${field} must be non-blank text`)
  return value as string
}

const optionalText = (value: unknown, field: string, fail: PlaybackSceneFailure): void => {
  if (value !== undefined && value !== null && typeof value !== 'string') {
    fail(`${field} must be text when present`)
  }
}

const validateOptionalRuntimeEntries = (
  value: unknown,
  field: 'variables' | 'privacies',
  fail: PlaybackSceneFailure
): void => {
  if (value === undefined || value === null) return
  if (!Array.isArray(value) || value.length > 100) {
    fail(`playbackScene node ${field} must be an array of at most 100 entries`)
  }
  value.forEach((candidate, index) => {
    const entry = record(candidate, `playbackScene node ${field}[${index}]`, fail)
    optionalText(entry.name, `playbackScene node ${field}[${index}].name`, fail)
    if (field === 'variables') {
      optionalText(entry.value, `playbackScene node ${field}[${index}].value`, fail)
      optionalText(entry.trust, `playbackScene node ${field}[${index}].trust`, fail)
    } else {
      optionalText(entry.privacy, `playbackScene node ${field}[${index}].privacy`, fail)
    }
  })
}

export const validateModelPlaybackScene = (
  value: unknown,
  expectedDeviceCount: number,
  expectedRuleCount: number,
  fail: PlaybackSceneFailure
): ModelPlaybackScene => {
  const scene = record(value, 'playbackScene', fail)
  if (!Array.isArray(scene.nodes) || scene.nodes.length !== expectedDeviceCount) {
    fail('playbackScene.nodes must match modelSnapshot.deviceCount')
  }
  if (!Array.isArray(scene.rules) || scene.rules.length !== expectedRuleCount) {
    fail('playbackScene.rules must match modelSnapshot.ruleCount')
  }

  const nodeIds = new Set<string>()
  scene.nodes.forEach((candidate: unknown, index: number) => {
    const node = record(candidate, `playbackScene.nodes[${index}]`, fail)
    const id = nonBlank(node.id, `playbackScene.nodes[${index}].id`, fail)
    nonBlank(node.templateName, `playbackScene.nodes[${index}].templateName`, fail)
    nonBlank(node.label, `playbackScene.nodes[${index}].label`, fail)
    if (nodeIds.has(id)) fail('playbackScene node identities must be unique')
    nodeIds.add(id)
    const position = record(node.position, `playbackScene.nodes[${index}].position`, fail)
    if (!Number.isFinite(position.x) || !Number.isFinite(position.y)) {
      fail('playbackScene node coordinates must be finite numbers')
    }
    if (!Number.isInteger(node.width) || node.width < 80 || node.width > 2000
      || !Number.isInteger(node.height) || node.height < 60 || node.height > 2000) {
      fail('playbackScene node dimensions are invalid')
    }
    if (typeof node.state !== 'string') fail('playbackScene node state must be text')
    optionalText(node.currentStateTrust, 'playbackScene node currentStateTrust', fail)
    optionalText(node.currentStatePrivacy, 'playbackScene node currentStatePrivacy', fail)
    validateOptionalRuntimeEntries(node.variables, 'variables', fail)
    validateOptionalRuntimeEntries(node.privacies, 'privacies', fail)
  })

  scene.rules.forEach((candidate: unknown, index: number) => {
    const rule = record(candidate, `playbackScene.rules[${index}]`, fail)
    if (!Array.isArray(rule.conditions) || rule.conditions.length === 0) {
      fail('playbackScene rules must include trigger conditions')
    }
    rule.conditions.forEach((conditionValue: unknown, conditionIndex: number) => {
      const condition = record(
        conditionValue,
        `playbackScene.rules[${index}].conditions[${conditionIndex}]`,
        fail
      )
      const deviceName = nonBlank(condition.deviceName, 'playbackScene rule condition deviceName', fail)
      if (!nodeIds.has(deviceName)) fail('playbackScene rule condition references an unknown node')
      nonBlank(condition.attribute, 'playbackScene rule condition attribute', fail)
      if (!['api', 'variable', 'mode', 'state'].includes(condition.targetType)) {
        fail('playbackScene rule condition targetType is invalid')
      }
    })
    const command = record(rule.command, `playbackScene.rules[${index}].command`, fail)
    const targetId = nonBlank(command.deviceName, 'playbackScene rule command deviceName', fail)
    if (!nodeIds.has(targetId)) fail('playbackScene rule command references an unknown node')
    nonBlank(command.action, 'playbackScene rule command action', fail)
  })

  return scene as ModelPlaybackScene
}

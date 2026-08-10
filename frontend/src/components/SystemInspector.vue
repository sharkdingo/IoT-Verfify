<script setup lang="ts">
import HintTooltip from '@/components/common/HintTooltip.vue'
import { ref, reactive, computed, watch } from 'vue'
import { COLLAPSED_PANEL_RAIL_CSS } from '@/constants/boardLayout'
import type { DeviceNode } from '../types/node'
import type { DeviceTemplate, InternalVariable, WorkingState } from '../types/device'
import type {
  EnvironmentVariableUpdateRequest,
  ModelEnvironmentVariable
} from '@/types/model'
import type { RuleForm } from '../types/rule'
import type { Specification } from '../types/spec'
import { specTemplateDetails } from '../assets/config/specTemplates'
import { useI18n } from 'vue-i18n'
import { buildSpecFormula } from '@/utils/spec'
import { verdictVariableSourceKeys } from '@/views/board/verdictVariableSource'
import {
  canonicalNaturalChangeRate,
  naturalChangeCandidateValues,
  resolveImpactEnvironmentDefinition
} from '@/utils/device'
import { getTemplateVariableDefaultValue } from '@/utils/deviceRuntime'
import { formatBuiltInModelToken } from '@/utils/modelTokenDisplay'
import { hasModeledStateMachine, resolveEffectiveNodeState } from '@/utils/canvas/nodeState'
import InfoTooltip from '@/components/common/InfoTooltip.vue'
import { useRovingTablist } from '@/composables/useRovingTablist'
import { notifyBlocked } from '@/utils/feedback'
import { normalizeModelRelation } from '@/utils/modelRequest'

const { t, te } = useI18n()

// Props
interface Props {
  devices?: DeviceNode[]
  deviceTemplates?: DeviceTemplate[]
  environmentVariables?: ModelEnvironmentVariable[]
  rules?: RuleForm[]
  specifications?: Specification[]
  focusedDeviceId?: string | null
  focusedRuleId?: string | null
  focusedSpecId?: string | null
  collapsed?: boolean
  width?: number
  activeSection?: string
  readOnly?: boolean
  readOnlyMessage?: string
  environmentSaving?: boolean
  rulesReordering?: boolean
  /**
   * The authoritative board snapshot failed to load.
   *
   * Without this the panel renders "No devices on canvas" during a failed load -- a factual claim it
   * cannot actually verify, and one that reads identically to a genuinely empty board. The load
   * banner disambiguates it, but the empty state should not assert something it does not know.
   */
  dataUnavailable?: boolean
}

const props = withDefaults(defineProps<Props>(), {
  devices: () => [],
  deviceTemplates: () => [],
  environmentVariables: () => [],
  rules: () => [],
  specifications: () => [],
  width: 320,
  readOnly: false,
  readOnlyMessage: '',
  environmentSaving: false,
  rulesReordering: false,
  dataUnavailable: false
})

const ensureWritable = (): boolean => {
  if (!props.readOnly) return true
  notifyBlocked(props.readOnlyMessage || t('app.playbackReadOnlyCloseFirst'))
  return false
}

const mutationTitle = (fallback: string): string =>
  props.readOnly ? (props.readOnlyMessage || t('app.playbackReadOnlyCloseFirst')) : fallback

// Panel state
const localCollapsed = ref(typeof window !== 'undefined' && window.innerWidth < 768)
const environmentPoolExpanded = ref(false)
const expandedEnvironmentVariables = ref<Set<string>>(new Set())
type InspectorSection = 'devices' | 'rules' | 'specs'

const isEnvironmentVariableExpanded = (name: string) =>
  expandedEnvironmentVariables.value.has(name)

const toggleEnvironmentVariable = (name: string) => {
  const next = new Set(expandedEnvironmentVariables.value)
  if (next.has(name)) {
    next.delete(name)
  } else {
    next.add(name)
  }
  expandedEnvironmentVariables.value = next
}

const localActiveSection = ref<InspectorSection>('devices')
const sectionExpanded = reactive<Record<InspectorSection, boolean>>({
  devices: true,
  rules: true,
  specs: true
})
const sectionSearch = reactive<Record<InspectorSection, string>>({
  devices: '',
  rules: '',
  specs: ''
})

const isInspectorSection = (value?: string): value is InspectorSection =>
  value === 'devices' || value === 'rules' || value === 'specs'

// Emits
const emit = defineEmits<{
  'delete-device': [deviceId: string]
  'delete-rule': [ruleId: string]
  'move-rule': [ruleId: string, direction: 'up' | 'down']
  'delete-spec': [specId: string]
  'open-rule-builder': []
  'open-control-section': [section: 'devices' | 'rules' | 'specs']
  'device-click': [deviceId: string]
  'save-environment': [variables: EnvironmentVariableUpdateRequest[]]
  'update:collapsed': [value: boolean]
  'update:active-section': [value: InspectorSection]
}>()

const isCollapsed = computed({
  get: () => props.collapsed ?? localCollapsed.value,
  set: (value: boolean) => {
    localCollapsed.value = value
    emit('update:collapsed', value)
  }
})

const resolvedPanelWidth = computed(() =>
  Math.min(520, Math.max(240, Number.isFinite(props.width) ? props.width : 320)))

const panelWidth = computed(() => `${resolvedPanelWidth.value}px`)

/**
 * Whether a tab can show its icon without squeezing its label.
 *
 * Derived from the panel's own width rather than the viewport, because this panel is resizable
 * (240–520px) and a viewport query would hide the icon on a wide screen with a narrow panel and show
 * it on a narrow screen with a wide one — both wrong.
 *
 * The arithmetic, for one of three `grid-cols-3` tabs: the panel spends 32px on its own padding and
 * 8px on the tablist's, leaving `(width - 40) / 3` per tab; each tab spends 16px on `px-2`, 12px on two
 * gaps and about 20px on the count badge. The widest label ("Devices" at 43px, "规则" narrower) needs
 * roughly 48px of comfortable room, so the icon's 14px only fits from about 370px up. Below that the
 * label had 28px and read as "De…", which is worse than no icon.
 */
const tabIconsFit = computed(() => resolvedPanelWidth.value >= 370)

const activeSection = computed<InspectorSection>({
  // `activeSection` is optional: when a parent controls it, the prop is authoritative;
  // when it is absent the panel owns its own selection. Without this the uncontrolled
  // case silently ignored every selection change.
  get: () => isInspectorSection(props.activeSection) ? props.activeSection : localActiveSection.value,
  set: (value: InspectorSection) => {
    localActiveSection.value = value
    emit('update:active-section', value)
  }
})

// Convert authoritative device nodes to display format.
const displayDevices = computed(() => {
  return props.devices
    .map(device => {
      const template = props.deviceTemplates.find(candidate => {
        const expected = String(device.templateName || '').trim().toLowerCase()
        return expected && (
          String(candidate.name || '').trim().toLowerCase() === expected
          || String(candidate.manifest?.Name || '').trim().toLowerCase() === expected
        )
      })
      const hasStateMachine = hasModeledStateMachine(template?.manifest)
      const canonicalState = hasStateMachine
        ? resolveEffectiveNodeState(device.state, template?.manifest)
        : ''
      return {
        id: device.id,
        name: device.label,
        type: device.templateName || t('app.device'),
        state: template?.defaultTemplate === true
          ? formatModelToken(canonicalState)
          : canonicalState,
        canonicalState
      }
    })
})

const normalizeEntitySearch = (value?: string | null) =>
  String(value || '').trim().toLowerCase()

const matchesEntitySearch = (haystack: Array<unknown>, query: string) => {
  const normalizedQuery = normalizeEntitySearch(query)
  if (!normalizedQuery) return true
  return haystack.some(value => normalizeEntitySearch(String(value ?? '')).includes(normalizedQuery))
}

const normalizeLookupName = (value?: string | null) =>
  String(value || '').trim().toLowerCase()

const templateMatchesDevice = (template: DeviceTemplate, device: DeviceNode) => {
  const expected = normalizeLookupName(device.templateName)
  return expected
    && (
      normalizeLookupName(template.name) === expected
      || normalizeLookupName(template.manifest?.Name) === expected
    )
}

const findTemplateForDevice = (device: DeviceNode) =>
  props.deviceTemplates.find(template => templateMatchesDevice(template, device)) || null

const isBundledTemplate = (template?: DeviceTemplate | null) =>
  template?.defaultTemplate === true

const formatModelToken = (value: unknown) => formatBuiltInModelToken(
  value,
  key => te(key) ? t(key) : key
)

const isBundledDevice = (device?: DeviceNode) =>
  Boolean(device && isBundledTemplate(findTemplateForDevice(device)))

const getVariableRange = (variable: InternalVariable) => {
  if (Array.isArray(variable.Values) && variable.Values.length > 0) {
    return variable.Values.join(' / ')
  }
  if (variable.LowerBound !== undefined || variable.UpperBound !== undefined) {
    return `${variable.LowerBound ?? '-∞'} - ${variable.UpperBound ?? '∞'}`
  }
  return t('app.modelControlled')
}

const uniqueNonEmpty = (values: Array<string | undefined>) =>
  Array.from(new Set(values.map(value => String(value || '').trim()).filter(Boolean)))

/* The fourth copy of this rule lived here, and it carried the same single-bound laxity the schema forbids.
   `getTemplateVariableDefaultValue` in `utils/deviceRuntime.ts` is the owner — see the note there. */
const defaultEnvironmentValue = (variable: InternalVariable) =>
  getTemplateVariableDefaultValue(variable)

const normalizeTrust = (value?: string | null) =>
  value === 'trusted' ? 'trusted' : 'untrusted'

const normalizePrivacy = (value?: string | null) =>
  value === 'private' ? 'private' : 'public'

const environmentPoolByName = computed(() => {
  const result = new Map<string, ModelEnvironmentVariable>()
  for (const variable of props.environmentVariables || []) {
    const name = String(variable?.name || '').trim()
    if (name) result.set(normalizeLookupName(name), variable)
  }
  return result
})

type EnvironmentSourceRole = 'read' | 'impact'

interface EnvironmentSource {
  deviceId: string
  label: string
  role: EnvironmentSourceRole
  effects: EnvironmentEffect[]
}

interface EnvironmentEffect {
  state: string
  value: string
  bundled: boolean
}

interface EnvironmentGroup {
  name: string
  definition: InternalVariable
  bundled: boolean
  ranges: string[]
  sources: EnvironmentSource[]
  conflicts: string[]
}

const hasEnumDomain = (variable: InternalVariable) =>
  Array.isArray(variable.Values) && variable.Values.length > 0

const hasNumericDomain = (variable: InternalVariable) =>
  variable.LowerBound !== undefined && variable.UpperBound !== undefined

const environmentDefinitionIncompatibility = (
  leftName: string,
  left: InternalVariable,
  rightName: string,
  right: InternalVariable
): string | null => {
  if (leftName !== rightName) {
    return t('app.environmentConflictName', { left: leftName, right: rightName })
  }
  if (hasEnumDomain(left) !== hasEnumDomain(right)
      || hasNumericDomain(left) !== hasNumericDomain(right)) {
    return t('app.environmentConflictType')
  }
  if (hasNumericDomain(left)
      && (left.LowerBound !== right.LowerBound || left.UpperBound !== right.UpperBound)) {
    return t('app.environmentConflictRange', {
      left: `${left.LowerBound}..${left.UpperBound}`,
      right: `${right.LowerBound}..${right.UpperBound}`
    })
  }
  if (hasEnumDomain(left)
      && JSON.stringify(left.Values) !== JSON.stringify(right.Values)) {
    return t('app.environmentConflictValues')
  }
  const leftRate = canonicalNaturalChangeRate(left.NaturalChangeRate)
  const rightRate = canonicalNaturalChangeRate(right.NaturalChangeRate)
  if (leftRate !== rightRate) {
    return t('app.environmentConflictNaturalRate', { left: leftRate, right: rightRate })
  }
  const leftTrust = normalizeTrust(left.Trust)
  const rightTrust = normalizeTrust(right.Trust)
  if (leftTrust !== rightTrust) {
    return t('app.environmentConflictTrust', { left: t(`app.${leftTrust}`), right: t(`app.${rightTrust}`) })
  }
  const leftPrivacy = normalizePrivacy(left.Privacy)
  const rightPrivacy = normalizePrivacy(right.Privacy)
  if (leftPrivacy !== rightPrivacy) {
    return t('app.environmentConflictPrivacy', {
      left: t(`app.${leftPrivacy}`),
      right: t(`app.${rightPrivacy}`)
    })
  }
  return null
}

const environmentEffectsFor = (
  template: DeviceTemplate | null | undefined,
  name: string
): EnvironmentEffect[] => (template?.manifest?.WorkingStates || [])
  .flatMap((state: WorkingState) => (state.Dynamics || [])
    .filter(dynamic => dynamic.VariableName === name)
    .map(dynamic => ({
      state: state.Name,
      value: dynamic.ChangeRate !== undefined
        ? t('app.environmentRateEffect', { rate: dynamic.ChangeRate })
        : t('app.environmentValueEffect', {
            value: isBundledTemplate(template) ? formatModelToken(dynamic.Value) : String(dynamic.Value || '')
          }),
      bundled: isBundledTemplate(template)
    })))

const environmentDefinitionFor = (
  name: string,
  template?: DeviceTemplate | null,
  preferred?: InternalVariable
): InternalVariable => {
  if (preferred) return preferred
  const sameTemplateDefinition = resolveImpactEnvironmentDefinition(template?.manifest, name)
  if (sameTemplateDefinition) return sameTemplateDefinition
  return {
    Name: name,
    IsInside: false,
    FalsifiableWhenCompromised: false,
    Trust: 'untrusted',
    Privacy: 'public'
  }
}

const addEnvironmentGroup = (
  grouped: Map<string, EnvironmentGroup>,
  name: string,
  definition: InternalVariable,
  source?: EnvironmentSource,
  bundled = false
) => {
  const key = normalizeLookupName(name)
  const existing = grouped.get(key)
  const current = existing || {
    name,
    definition,
    bundled,
    ranges: [],
    sources: [],
    conflicts: []
  }
  if (existing) {
    const mismatch = environmentDefinitionIncompatibility(
      current.name, current.definition, name, definition)
    if (mismatch && !current.conflicts.includes(mismatch)) current.conflicts.push(mismatch)
  }
  if (existing) current.bundled = current.bundled && bundled
  current.ranges.push(getVariableRange(definition))
  if (source && !current.sources.some(item => item.deviceId === source.deviceId && item.role === source.role)) {
    current.sources.push(source)
  }
  grouped.set(key, current)
}

const environmentVariables = computed(() => {
  const grouped = new Map<string, EnvironmentGroup>()

  for (const device of props.devices) {
    const template = findTemplateForDevice(device)
    const variables = template?.manifest?.InternalVariables || []
    for (const variable of variables) {
      if (!variable?.Name || variable.IsInside === true) continue
      // Reads=false is an affect-only declaration: it supplies the domain and the device's effect
      // but no read. Claiming "reads this environment variable" for it would tell the user the
      // opposite of what the generator compiles -- the device gets no read mirror and its rules
      // cannot use the value as a condition source.
      if (variable.Reads === false) continue

      addEnvironmentGroup(grouped, variable.Name, variable, {
        deviceId: device.id,
        label: device.label,
        role: 'read',
        effects: []
      }, isBundledTemplate(template))
    }

    for (const impacted of template?.manifest?.ImpactedVariables || []) {
      const name = String(impacted || '').trim()
      if (!name) continue
      addEnvironmentGroup(grouped, name, environmentDefinitionFor(name, template), {
        deviceId: device.id,
        label: device.label,
        role: 'impact',
        effects: environmentEffectsFor(template, name)
      }, isBundledTemplate(template))
    }
  }

  for (const saved of props.environmentVariables || []) {
    const name = String(saved?.name || '').trim()
    if (!name || grouped.has(normalizeLookupName(name))) continue
    addEnvironmentGroup(grouped, name, environmentDefinitionFor(name))
  }

  return Array.from(grouped.values())
    .map(variable => {
      const ranges = uniqueNonEmpty(variable.ranges).map(range => variable.bundled
        ? range.split(' / ').map(formatModelToken).join(' / ')
        : range)
      const saved = environmentPoolByName.value.get(normalizeLookupName(variable.name))
      const authoritativeValue = typeof saved?.value === 'string' ? saved.value.trim() : ''
      const value = authoritativeValue !== ''
        ? String(saved!.value)
        : defaultEnvironmentValue(variable.definition)
      // A compare-and-set edit needs a non-blank authoritative baseline value. A variable with
      // no declared value domain materializes blank and is not verifiable, so its controls are
      // shown disabled with an explanation instead of silently discarding edits.
      const editable = authoritativeValue !== '' && variable.conflicts.length === 0
      const trust = normalizeTrust(saved?.trust || variable.definition.Trust)
      const privacy = normalizePrivacy(saved?.privacy || variable.definition.Privacy)
      return {
        ...variable,
        displayName: variable.bundled ? formatModelToken(variable.name) : variable.name,
        rangeLabel: variable.conflicts.length > 0
          ? t('app.conflictingDefinitions')
          : (ranges.length === 1 ? ranges[0] : t('app.mixedRanges')),
        naturalChangeRateLabel: hasNumericDomain(variable.definition)
          ? (variable.definition.NaturalChangeRate
              ? t('app.environmentNumericEvolution', {
                  rate: variable.definition.NaturalChangeRate,
                  candidates: naturalChangeCandidateValues(variable.definition.NaturalChangeRate)
                })
              : t('app.environmentNaturalRateMissing'))
          // Branch on authorship exactly as the generator does: a value some device declares it
          // writes holds when no effect applies, while one nobody writes is an exogenous input the
          // verifier may move freely. Describing both as "nondeterministic" told the user the
          // opposite of what gets verified for every device-written value.
          : (variable.sources.some(source => source.role === 'impact')
              ? t('app.environmentDiscreteWrittenEvolution')
              : t('app.environmentDiscreteExogenousEvolution')),
        evolutionEffects: variable.sources.flatMap(source => source.effects.map(effect => ({
          ...effect,
          deviceId: source.deviceId,
          deviceLabel: source.label,
          stateLabel: effect.bundled ? formatModelToken(effect.state) : effect.state
        }))),
        value,
        editable,
        valueLabel: value
          ? (variable.bundled ? formatModelToken(value) : value)
          : t('app.modelControlled'),
        valueTitle: value
          ? (variable.bundled ? formatModelToken(value) : value)
          : t('app.modelControlled'),
        trust,
        privacy,
        trustLabel: t(`app.${trust}`),
        privacyLabel: t(`app.${privacy}`),
        enumValues: Array.isArray(variable.definition.Values) ? variable.definition.Values : [],
        lowerBound: variable.definition.LowerBound,
        upperBound: variable.definition.UpperBound
      }
    })
    .sort((a, b) => a.name.localeCompare(b.name))
})

watch(environmentVariables, variables => {
  const availableNames = new Set(variables.map(variable => variable.name))
  const next = new Set(
    Array.from(expandedEnvironmentVariables.value)
      .filter(name => availableNames.has(name))
  )
  if (next.size !== expandedEnvironmentVariables.value.size) {
    expandedEnvironmentVariables.value = next
  }
})

const getEnvironmentSourceTitle = (source: EnvironmentSource) =>
  `${source.role === 'impact' ? t('app.affectsEnvironment') : t('app.readsEnvironment')}: ${source.label}`

type EnvironmentVariableEdit = Partial<Record<'value' | 'trust' | 'privacy', string>>

const updateEnvironmentVariable = (
  name: string,
  patch: EnvironmentVariableEdit
) => {
  if (!ensureWritable()) return
  const displayed = environmentVariables.value.find(variable => variable.name === name)
  if (!displayed?.editable) return
  const saved = environmentPoolByName.value.get(normalizeLookupName(name))
  const authoritativeValue = typeof saved?.value === 'string' ? saved.value.trim() : ''
  if (!authoritativeValue) return
  // The displayed effective labels combine the authoritative row with the same template fallbacks
  // the backend materializes. Reuse them so the CAS baseline cannot contradict the visible value.
  const expected: EnvironmentVariableUpdateRequest['expected'] = {
    value: authoritativeValue,
    trust: displayed.trust,
    privacy: displayed.privacy
  }
  const desired: EnvironmentVariableUpdateRequest['desired'] = {}
  for (const field of ['value', 'trust', 'privacy'] as const) {
    const next = patch[field]
    if (Object.prototype.hasOwnProperty.call(patch, field) && typeof next === 'string') {
      desired[field] = next
    }
  }
  emit('save-environment', [{ name, expected, desired }])
}

const eventValue = (event: Event) =>
  (event.target as HTMLInputElement | HTMLSelectElement | null)?.value || ''

const formatEnvironmentValue = (variable: EnvironmentGroup, value: string) =>
  variable.bundled ? formatModelToken(value) : value

/**
 * A relation as a reading glyph, keyed on the canonical form rather than on an enum that never arrives.
 *
 * The map used to be keyed on `EQ`/`GTE`/`LTE`. Nothing persists those: `RuleBuilderDialog` authors symbol form
 * (`'>='`, `'in'`) and `BoardStorageServiceImpl` canonicalises to symbols on save, so every enum key was dead and
 * only the `|| relation` fallthrough ran — which is why this panel printed a raw `>=` while `FixResultDialog`
 * printed "Greater or equal" for the same condition. In a product where the condition text *is* the claim being
 * verified, three renderings of one operator is three chances to misread it.
 *
 * `normalizeModelRelation` already accepts both spellings and returns the symbol, so it goes in front and this
 * map only has to turn a symbol into its glyph.
 */
const getRelationLabel = (relation: string): string => {
  const canonical = normalizeModelRelation(relation) ?? relation
  const glyphs: Record<string, string> = {
    '=': '=',
    '!=': '≠',
    '>': '>',
    '>=': '≥',
    '<': '<',
    '<=': '≤',
    'in': '∈',
    'not in': '∉'
  }
  return glyphs[canonical] || canonical
}

const hasConditionValue = (value: unknown) =>
  value !== null && value !== undefined && value !== ''

const resolveDevice = (ref?: string) =>
  props.devices.find(device => device.id === ref)

const isValueBasedRuleSource = (sourceType?: string) =>
  sourceType === 'variable' || sourceType === 'mode' || sourceType === 'state'

// Convert real rules to display format
const displayRules = computed(() => {
  return props.rules.map((rule, index) => {
    const targetNode = resolveDevice(rule.toId)
    
    // 构建更详细的源设备描述
    const sourceDescriptions = rule.sources.map(s => {
      const sourceNode = resolveDevice(s.fromId)
      const localizeSource = isBundledDevice(sourceNode)
      const sourceProperty = localizeSource ? formatModelToken(s.fromApi) : s.fromApi
      const sourceValue = localizeSource ? formatModelToken(s.value) : s.value
      let desc = `${sourceNode?.label || t('app.unknown')}`
      
      // 如果有 itemType、relation、value 信息，显示更完整
      const sourceType = s.itemType
      if (isValueBasedRuleSource(sourceType) && s.relation && hasConditionValue(s.value)) {
        desc += ` ${sourceProperty} ${getRelationLabel(s.relation)} ${sourceValue}`
      } else if (sourceType === 'api') {
        desc += ` ${t('app.triggers')} ${sourceProperty}`
      } else {
        // 如果有 relation 和 value，也显示
        if (s.relation && hasConditionValue(s.value)) {
          desc += ` ${sourceProperty} ${getRelationLabel(s.relation)} ${sourceValue}`
        } else {
          desc += ` ${sourceProperty}`
        }
      }
      return desc
    })

    return {
      originalId: rule.id, // 保留原始id用于删除操作
      executionOrder: index + 1,
      isFirst: index === 0,
      isLast: index === props.rules.length - 1,
      id: rule.id ? rule.id.replace('rule_', '') : 'unknown',
      name: rule.name || t('app.ruleFrom', { source: (rule.id ? rule.id.replace('rule_', '') : '').split('_')[1] || t('app.unknown') }),
      description: t('app.ifThenDescription', {
        source: sourceDescriptions.join(` ${t('app.and')} `),
        target: targetNode?.label || t('app.unknown'),
        action: isBundledDevice(targetNode)
          ? formatModelToken(rule.toApi || t('app.notAvailableShort'))
          : rule.toApi || t('app.notAvailableShort')
      }),
      status: t('app.active'),
      color: 'blue' as const,
      enabled: true, // Add enabled status
      searchText: [
        rule.id,
        rule.name,
        sourceDescriptions.join(' '),
        targetNode?.id,
        targetNode?.label,
        rule.toApi,
        rule.contentDevice,
        resolveDevice(rule.contentDevice)?.label,
        rule.content
      ].join(' ')
    }
  })
})

const getSpecificationDeviceInfo = (spec: Specification): string => {
  const namedRefs = (spec.devices || [])
    .map(device => device.deviceLabel || device.deviceId)
    .filter(Boolean)

  if (namedRefs.length > 0) {
    return namedRefs.join(', ')
  }

  const conditionRefs = [
    ...(spec.aConditions || []),
    ...(spec.ifConditions || []),
    ...(spec.thenConditions || [])
  ]
    .map(condition => condition.deviceLabel || condition.deviceId)
    .filter(Boolean)

  const uniqueRefs = Array.from(new Set(conditionRefs))
  return uniqueRefs.length > 0 ? uniqueRefs.join(', ') : t('app.global')
}

// Convert real specifications to display format
const displaySpecs = computed(() => {
  return props.specifications.map(spec => {
    const template = specTemplateDetails.find(candidate => candidate.id === spec.templateId)
    const specType = template?.labelKey
      ? t(template.labelKey)
      : spec.templateLabel || template?.label || t('app.unknown')

    const deviceInfo = ` (${getSpecificationDeviceInfo(spec)})`

    return {
      id: spec.id,
      name: `${specType}${deviceInfo}`,
      formula: buildSpecFormula(spec, {
        nodes: props.devices
      }),
      // The formula alone renders the two readings as one differing token in a monospace string, and an
      // unrecorded one as a literal `<unresolved>`. This is the surface where a user scans their whole
      // specification set, so it names the reading in the same words the editor and verdict rows use.
      variableSourceLabels: verdictVariableSourceKeys(spec)
        .map(key => ({ key, label: t(key), unresolved: key === 'app.specVariableSourceUnresolvedShort' })),
      status: t('app.active'),
      searchText: [
        spec.id,
        spec.templateId,
        spec.templateLabel,
        specType,
        deviceInfo,
        ...(spec.devices || []).flatMap(device => [device.deviceId, device.deviceLabel, ...(device.selectedApis || [])]),
        ...(spec.aConditions || []).flatMap(condition => [condition.deviceId, condition.deviceLabel, condition.targetType, condition.propertyScope, condition.variableSource, condition.key, condition.relation, condition.value]),
        ...(spec.ifConditions || []).flatMap(condition => [condition.deviceId, condition.deviceLabel, condition.targetType, condition.propertyScope, condition.variableSource, condition.key, condition.relation, condition.value]),
        ...(spec.thenConditions || []).flatMap(condition => [condition.deviceId, condition.deviceLabel, condition.targetType, condition.propertyScope, condition.variableSource, condition.key, condition.relation, condition.value])
      ].join(' ')
    }
  })
})

const filteredDevices = computed(() =>
  displayDevices.value.filter(device =>
    matchesEntitySearch(
      [device.id, device.name, device.type, device.state, device.canonicalState],
      sectionSearch.devices
    )
  )
)

const filteredRules = computed(() =>
  displayRules.value.filter(rule =>
    matchesEntitySearch([rule.id, rule.name, rule.description, rule.searchText], sectionSearch.rules)
  )
)

const filteredSpecs = computed(() =>
  displaySpecs.value.filter(spec =>
    matchesEntitySearch([spec.id, spec.name, spec.formula, spec.searchText], sectionSearch.specs)
  )
)

const sectionCounts = computed(() => ({
  devices: { total: displayDevices.value.length, filtered: filteredDevices.value.length },
  rules: { total: displayRules.value.length, filtered: filteredRules.value.length },
  specs: { total: displaySpecs.value.length, filtered: filteredSpecs.value.length }
}))

const clearSectionSearch = (section: InspectorSection) => {
  sectionSearch[section] = ''
}

const toggleEntitySection = (section: InspectorSection) => {
  sectionExpanded[section] = !sectionExpanded[section]
}

const inspectorTabs = computed(() => [
  {
    id: 'devices' as const,
    label: t('app.devicesTool'),
    icon: 'devices',
    count: sectionCounts.value.devices.total
  },
  {
    id: 'rules' as const,
    label: t('app.rulesTool'),
    icon: 'rule',
    count: sectionCounts.value.rules.total
  },
  {
    id: 'specs' as const,
    label: t('app.specificationsTool'),
    icon: 'fact_check',
    count: sectionCounts.value.specs.total
  }
])

const { handleTablistKeydown: handleInspectorTabKeydown } = useRovingTablist<InspectorSection>({
  tabIds: () => inspectorTabs.value.map(tab => tab.id),
  select: id => { activeSection.value = id },
  tabElementId: id => `inspector-tab-${id}`
})

// Methods
const handleDeleteDevice = (deviceId: string) => {
  if (!ensureWritable()) return
  emit('delete-device', deviceId)
}

const handleDeleteRule = (ruleId: string) => {
  if (!ensureWritable()) return
  emit('delete-rule', ruleId)
}

const handleMoveRule = (ruleId: string, direction: 'up' | 'down') => {
  if (!ensureWritable() || props.rulesReordering || sectionSearch.rules) return
  emit('move-rule', ruleId, direction)
}

const handleAddRule = () => {
  if (!ensureWritable()) return
  emit('open-control-section', 'rules')
  emit('open-rule-builder')
}

const handleAddDevice = () => {
  if (!ensureWritable()) return
  emit('open-control-section', 'devices')
}

const handleAddSpec = () => {
  if (!ensureWritable()) return
  emit('open-control-section', 'specs')
}

const handleDeviceClick = (deviceId: string) => {
  emit('device-click', deviceId)
}

const handleDeleteSpec = (specId: string) => {
  if (!ensureWritable()) return
  emit('delete-spec', specId)
}

const togglePanel = () => {
  isCollapsed.value = !isCollapsed.value
}

const isFullTextClipped = (target: HTMLElement) => {
  const horizontalOverflow = target.scrollWidth - target.clientWidth > 1
  const verticalOverflow = target.scrollHeight - target.clientHeight > 1
  return horizontalOverflow || verticalOverflow
}

const syncFullTextTitle = (event: PointerEvent | FocusEvent) => {
  if (typeof window === 'undefined') return
  const root = event.currentTarget as HTMLElement | null
  const target = (event.target as HTMLElement | null)?.closest<HTMLElement>('[data-full-text]')
  if (!root || !target || !root.contains(target)) return

  const text = target.dataset.fullText?.trim()
  if (!text || !isFullTextClipped(target)) {
    target.removeAttribute('title')
    return
  }

  target.setAttribute('title', text)
}
</script>

<template>
  <!-- Collapsed width comes from COLLAPSED_PANEL_RAIL_CSS, the same constant ControlCenter and Board.vue's
       canvas-fit math read. It was a `3.5rem` literal in each of the two panels plus a `56` in Board.vue,
       agreeing only by way of comments pointing at each other — and the CSS token that shared the job had
       already drifted to 48px, which is what the rationale in the constant records. -->
  <aside
    data-testid="system-inspector"
    class="absolute right-0 top-0 bottom-0 glass-panel board-side-panel z-40 flex flex-col overflow-hidden border-l transition-all duration-300 ease-in-out"
    :class="isCollapsed ? 'is-collapsed' : 'is-expanded'"
    :aria-disabled="props.readOnly ? 'true' : undefined"
    :style="{ width: isCollapsed ? COLLAPSED_PANEL_RAIL_CSS : panelWidth }"
    @pointerover="syncFullTextTitle"
    @focusin="syncFullTextTitle"
  >
    <div
      class="board-panel-header relative overflow-hidden border-b"
      :class="isCollapsed ? 'p-0.5' : 'p-4'"
    >
      <div v-if="!isCollapsed" class="flex items-center justify-between w-full">
        <div class="flex min-w-0 items-center gap-3">
          <HintTooltip :content="t('app.collapse')">
            <button
              type="button"
              @click="togglePanel"
              class="board-panel-toggle inline-flex h-11 w-11 shrink-0 items-center justify-center overflow-hidden rounded-lg text-slate-500 transition-all hover:bg-slate-100 hover:text-slate-800"
              :aria-label="t('app.collapse')"
            >
              <span class="material-symbols-outlined text-base" aria-hidden="true">dock_to_left</span>
            </button>
          </HintTooltip>
          <div class="p-2 board-chip-info rounded-lg border board-border-subtle shadow-sm">
            <span class="material-symbols-outlined board-text-info">fact_check</span>
          </div>
          <div class="min-w-0">
            <h2 class="board-panel-title text-sm font-bold leading-none truncate" :data-full-text="t('app.systemInspector')">{{ t('app.systemInspector') }}</h2>
            <p class="board-panel-subtitle text-[length:var(--iot-font-min)] font-medium mt-0.5 truncate" :data-full-text="t('app.currentBoardContent')">{{ t('app.currentBoardContent') }}</p>
          </div>
        </div>
      </div>
      <div v-else class="flex items-center justify-center">
        <HintTooltip :content="t('app.expand')">
          <button
            type="button"
            @click="togglePanel"
            class="board-panel-toggle inline-flex h-11 w-11 shrink-0 items-center justify-center overflow-hidden rounded-lg text-slate-500 transition-all hover:bg-slate-100 hover:text-slate-800"
            :aria-label="t('app.expand')"
          >
            <span class="material-symbols-outlined text-base" aria-hidden="true">dock_to_left</span>
          </button>
        </HintTooltip>
      </div>
    </div>

    <div
      v-if="!isCollapsed"
      class="board-panel-body flex-1 iot-scroll-region transition-all duration-300 p-4 space-y-4"
    >
      <div
        class="board-segmented grid grid-cols-3 gap-1 rounded-xl border p-1"
        role="tablist"
        :aria-label="t('app.currentBoardContent')"
      >
        <button
          v-for="tab in inspectorTabs"
          :key="tab.id"
          :id="`inspector-tab-${tab.id}`"
          type="button"
          role="tab"
          :data-testid="`inspector-tab-${tab.id}`"
          :aria-selected="activeSection === tab.id"
          :aria-controls="activeSection === tab.id ? `inspector-panel-${tab.id}` : undefined"
          :tabindex="activeSection === tab.id ? 0 : -1"
          @click="activeSection = tab.id"
          @keydown="handleInspectorTabKeydown($event, tab.id)"
          :class="[
            // min-h-11: the tabs measured 33px, and a tab strip is a primary navigation target.
            'min-w-0 min-h-11 rounded-lg px-2 py-2 text-[11px] font-bold transition-all flex items-center justify-start gap-1.5',
            activeSection === tab.id
              ? 'bg-[color:var(--accent-fill)] text-white shadow-sm'
              : 'text-slate-500 hover:bg-white hover:text-slate-800'
          ]"
        >
          <!--
            The icon is hidden below the width where the label fits beside it.

            Budget in this 320px panel: three `grid-cols-3` tabs get ~96px each, and `px-2` (16px) plus
            the icon (14px), two gaps (12px) and the count badge (~20px) left the label **28px** where
            "Devices" needs 43px — so the tab that names the section rendered as "De…". The icon and the
            label say the same thing, and only the label says it unambiguously, so the icon yields.
            It is `aria-hidden` either way, so nothing is lost to assistive technology.
          -->
          <span v-if="tabIconsFit" class="material-symbols-outlined text-sm" aria-hidden="true">{{ tab.icon }}</span>
          <span class="min-w-0 flex-1 truncate text-left" :data-full-text="tab.label">{{ tab.label }}</span>
          <!--
            The ACTIVE badge darkens its ground instead of lightening it.

            Measured on a 12-device board: `bg-white/20 text-white` puts white text on the accent fill lightened by
            20% white — **3.62:1**, under the 4.5 floor that applies because this text is 11px. Lightening a fill and
            then writing white on it moves both sides toward each other, so `white/30` is worse still (3.02:1).
            `black/20` darkens the same fill instead: **7.24:1**, and it reads as a recessed pill rather than a
            washed-out one, which is also the more honest depth cue for a count sitting inside its tab.

            The inactive badge measures 4.54:1 (`rgb(97,113,135)` on `rgb(241,245,249)`) and needed no change — I
            changed it first on a class-name guess before measuring the computed colours, which is what identified the
            active badge as the real offender.

            It took a dense board to surface at all: the count is the whole point of the badge — how a reader knows a
            section holds twelve devices without opening it — and with two devices the digit is easy to overlook.
          -->
          <span
            class="shrink-0 rounded-full px-1.5 py-0.5 text-[length:var(--iot-font-min)] leading-none"
            :class="activeSection === tab.id ? 'bg-black/20 text-white' : 'bg-slate-200 text-slate-600'"
          >
            {{ tab.count }}
          </span>
        </button>
      </div>

      <slot name="overview" />

      <!-- Uses the shared warning role rather than raw amber utilities. The previous
           `board-chip-warning` had no dark counterpart for the tint, so on a near-black ground it
           composited into the "muddy brown/olive" surface two dark-theme reviews flagged as
           looking like a light-theme panel carried over. The role is theme-aware. -->
      <section
        data-testid="environment-pool"
        aria-labelledby="environment-pool-title"
        class="board-surface-info rounded-xl p-3 shadow-sm"
      >
        <div class="mb-2 flex items-start gap-2">
          <button
            type="button"
            data-testid="toggle-environment-pool"
            class="flex min-w-0 flex-1 items-start justify-between gap-3 rounded-lg text-left transition-colors hover:bg-[color-mix(in_srgb,var(--warning)_10%,transparent)] focus:outline-none focus:ring-2 focus:ring-[color:var(--warning-border)]"
            :aria-expanded="environmentPoolExpanded"
            @click="environmentPoolExpanded = !environmentPoolExpanded"
          >
          <div class="min-w-0 p-1">
            <div class="flex min-w-0 items-center gap-2">
              <span class="material-symbols-outlined board-text-info text-base" aria-hidden="true">public</span>
              <!--
                `tracking-widest` on an all-caps heading pushed this 3px past its 167px row, so it
                rendered as "ENVIRONMENT PO…" -- named in every visual review of the inspector. The
                wide tracking bought nothing at this size; `tracking-wide` fits and still reads as a
                section label. Colour comes from the warning role rather than raw amber utilities,
                which had a light-only value for the icon.
              -->
              <!--
                The id exists so the enclosing <section> can point at this heading. A bare <section> is an implicit
                `region` landmark, and an unnamed region is invisible in a screen reader's landmark list — measured, it
                was the one unnamed landmark on the board. Labelling by reference rather than with an aria-label keeps
                one translated string instead of two that can drift apart.
              -->
              <h3 id="environment-pool-title" class="board-text-info truncate text-xs font-bold uppercase tracking-wide" :data-full-text="t('app.environmentPool')">
                {{ t('app.environmentPool') }}
              </h3>
            </div>
            <p v-if="environmentPoolExpanded" class="mt-1 text-[11px] font-medium leading-snug board-text-info">
              {{ t('app.environmentPoolShortHint') }}
            </p>
            <div
              v-else-if="environmentVariables.length > 0"
              class="mt-1 flex max-w-full flex-wrap gap-1"
              :title="environmentVariables.map(variable => variable.displayName).join(', ')"
            >
              <span
                v-for="variable in environmentVariables.slice(0, 3)"
                :key="variable.name"
                class="max-w-[6.5rem] truncate board-chip-info rounded-full px-1.5 py-0.5 text-[length:var(--iot-font-min)] font-bold"
              >
                {{ variable.displayName }}
              </span>
              <span
                v-if="environmentVariables.length > 3"
                class="board-chip-info rounded-full px-1.5 py-0.5 text-[length:var(--iot-font-min)] font-bold"
              >
                +{{ environmentVariables.length - 3 }}
              </span>
            </div>
          </div>
          <span class="mt-1 inline-flex shrink-0 items-center gap-1 rounded-full board-chip-info px-2 py-0.5 text-[length:var(--iot-font-min)] font-bold board-text-info">
            {{ environmentVariables.length }}
            <span class="material-symbols-outlined text-sm" aria-hidden="true">
              {{ environmentPoolExpanded ? 'expand_less' : 'expand_more' }}
            </span>
          </span>
          </button>
          <InfoTooltip
            :text="t('app.environmentPoolHint')"
            :label="t('app.showHelpFor', { topic: t('app.environmentPool') })"
            placement="left"
            test-id="environment-pool-help"
          />
        </div>

        <div v-if="environmentPoolExpanded && environmentVariables.length > 0" class="space-y-2">
          <article
            v-for="variable in environmentVariables"
            :key="variable.name"
            class="rounded-lg border border-white/70 bg-white/85 p-2.5 shadow-sm dark:border-slate-700 dark:bg-slate-900/80"
          >
            <button
              type="button"
              class="flex w-full min-w-0 items-center justify-between gap-2 rounded-md p-1 text-left transition-colors hover:board-chip-info focus:outline-none focus:ring-2 focus:ring-[color:var(--accent-border)] dark:hover:bg-[color:var(--warning-surface)]"
              :aria-expanded="isEnvironmentVariableExpanded(variable.name)"
              @click="toggleEnvironmentVariable(variable.name)"
            >
              <span class="flex min-w-0 items-center gap-2">
                <span class="material-symbols-outlined text-sm board-text-info" aria-hidden="true">
                  {{ isEnvironmentVariableExpanded(variable.name) ? 'expand_less' : 'expand_more' }}
                </span>
                <span class="min-w-0">
                  <span class="block truncate text-sm font-extrabold text-slate-800 dark:text-slate-100" :data-full-text="variable.displayName">
                    {{ variable.displayName }}
                  </span>
                </span>
              </span>
              <span class="flex shrink-0 items-center gap-1.5">
                <span class="max-w-[5.5rem] truncate rounded-full bg-slate-100 px-2 py-0.5 text-[length:var(--iot-font-min)] font-bold text-slate-500 dark:bg-slate-800 dark:text-slate-300" :data-full-text="variable.rangeLabel">
                  {{ variable.rangeLabel }}
                </span>
                <span class="max-w-[4.5rem] truncate rounded-full board-chip-info px-2 py-0.5 text-[length:var(--iot-font-min)] font-bold board-text-info" :data-full-text="variable.valueLabel">
                  {{ variable.valueLabel }}
                </span>
              </span>
            </button>

            <div v-if="isEnvironmentVariableExpanded(variable.name)" class="mt-2 space-y-2">
              <div class="grid grid-cols-1 gap-2 text-[length:var(--iot-font-min)]">
                <label class="min-w-0 rounded-md bg-slate-50 p-1.5 dark:bg-slate-800">
                  <span class="block font-bold uppercase text-slate-500">{{ t('app.modelInitialValue') }}</span>
                  <select
                    v-if="variable.enumValues.length > 0"
                    :data-testid="`environment-value-${variable.name}`"
                    :value="variable.value"
                    :aria-label="`${variable.displayName} ${t('app.modelInitialValue')}`"
                    :disabled="props.readOnly || props.environmentSaving || !variable.editable"
                    :aria-busy="props.environmentSaving ? 'true' : undefined"
                    class="mt-1 w-full rounded border border-slate-200 bg-white px-2 py-1 font-semibold text-slate-700 outline-none focus:border-[color:var(--accent-border)] disabled:cursor-wait disabled:opacity-60 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
                    @change="updateEnvironmentVariable(variable.name, { value: eventValue($event) })"
                  >
                    <option v-for="option in variable.enumValues" :key="option" :value="option">
                      {{ formatEnvironmentValue(variable, option) }}
                    </option>
                  </select>
                  <input
                    v-else
                    :data-testid="`environment-value-${variable.name}`"
                    :type="variable.lowerBound !== undefined || variable.upperBound !== undefined ? 'number' : 'text'"
                    :min="variable.lowerBound"
                    :max="variable.upperBound"
                    :value="variable.value"
                    :title="variable.valueTitle"
                    :aria-label="`${variable.displayName} ${t('app.modelInitialValue')}`"
                    :disabled="props.readOnly || props.environmentSaving || !variable.editable"
                    :aria-busy="props.environmentSaving ? 'true' : undefined"
                    class="mt-1 w-full rounded border border-slate-200 bg-white px-2 py-1 font-semibold text-slate-700 outline-none focus:border-[color:var(--accent-border)] disabled:cursor-wait disabled:opacity-60 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
                    @change="updateEnvironmentVariable(variable.name, { value: eventValue($event) })"
                  />
                  <p
                    v-if="variable.conflicts.length > 0"
                    :data-testid="`environment-conflict-${variable.name}`"
                    class="mt-1 text-[length:var(--iot-font-min)] leading-4 board-text-danger"
                  >
                    {{ t('app.environmentDefinitionConflict', { reasons: variable.conflicts.join('; ') }) }}
                  </p>
                  <p
                    v-else-if="!variable.editable"
                    :data-testid="`environment-not-editable-${variable.name}`"
                    class="mt-1 text-[length:var(--iot-font-min)] leading-4 board-text-info"
                  >
                    {{ t('app.environmentValueNotEditable') }}
                  </p>
                </label>
                <div
                  :data-testid="`environment-evolution-${variable.name}`"
                  class="rounded-md border border-slate-200 bg-white/70 p-2 text-[length:var(--iot-font-min)] leading-4 text-slate-500 dark:border-slate-700 dark:bg-slate-900/60 dark:text-slate-300"
                >
                  <p class="font-bold uppercase text-slate-500">{{ t('app.modelEvolution') }}</p>
                  <p>{{ t('app.naturalChangeRate') }}: <strong>{{ variable.naturalChangeRateLabel }}</strong></p>
                  <ul v-if="variable.evolutionEffects.length > 0" class="mt-1 space-y-0.5">
                    <li v-for="effect in variable.evolutionEffects" :key="`${effect.deviceId}:${effect.state}:${effect.value}`">
                      {{ effect.deviceLabel }} · {{ effect.stateLabel }}: {{ effect.value }}
                    </li>
                  </ul>
                  <p v-else class="mt-1">{{ t('app.environmentNoDeviceEffects') }}</p>
                  <p class="mt-1 text-slate-500">{{ t('app.environmentEvolutionHint') }}</p>
                </div>
                <details class="rounded-md border border-slate-200 bg-white/70 p-1.5 dark:border-slate-700 dark:bg-slate-900/60">
                  <summary class="cursor-pointer text-[length:var(--iot-font-min)] font-bold text-slate-500">{{ t('app.advancedTrustPrivacyOverrides') }}</summary>
                  <p class="mt-1 text-[length:var(--iot-font-min)] leading-4 text-slate-500">{{ t('app.environmentTrustOverrideHint') }}</p>
                  <div class="mt-1.5 grid grid-cols-2 gap-1.5">
                  <label class="min-w-0 rounded-md bg-slate-50 p-1.5 dark:bg-slate-800">
                    <span class="block font-bold uppercase text-slate-500">{{ t('app.trust') }}</span>
                    <select
                      :data-testid="`environment-trust-${variable.name}`"
                      :value="variable.trust"
                      :aria-label="`${variable.displayName} ${t('app.trust')}`"
                      :disabled="props.readOnly || props.environmentSaving || !variable.editable"
                      :aria-busy="props.environmentSaving ? 'true' : undefined"
                      class="mt-1 w-full rounded border border-slate-200 bg-white px-2 py-1 font-semibold text-slate-700 outline-none focus:border-[color:var(--accent-border)] disabled:cursor-wait disabled:opacity-60 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
                      @change="updateEnvironmentVariable(variable.name, { trust: eventValue($event) })"
                    >
                      <option value="trusted">{{ t('app.trusted') }}</option>
                      <option value="untrusted">{{ t('app.untrusted') }}</option>
                    </select>
                  </label>
                  <label class="min-w-0 rounded-md bg-slate-50 p-1.5 dark:bg-slate-800">
                    <span class="block font-bold uppercase text-slate-500">{{ t('app.privacy') }}</span>
                    <select
                      :data-testid="`environment-privacy-${variable.name}`"
                      :value="variable.privacy"
                      :aria-label="`${variable.displayName} ${t('app.privacy')}`"
                      :disabled="props.readOnly || props.environmentSaving || !variable.editable"
                      :aria-busy="props.environmentSaving ? 'true' : undefined"
                      class="mt-1 w-full rounded border border-slate-200 bg-white px-2 py-1 font-semibold text-slate-700 outline-none focus:border-[color:var(--accent-border)] disabled:cursor-wait disabled:opacity-60 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
                      @change="updateEnvironmentVariable(variable.name, { privacy: eventValue($event) })"
                    >
                      <option value="public">{{ t('app.public') }}</option>
                      <option value="private">{{ t('app.private') }}</option>
                    </select>
                  </label>
                  </div>
                </details>
              </div>

              <div class="flex flex-wrap gap-1">
                <!-- The `v-for` sits on the wrapper: `source` comes from the loop, so a tooltip hoisted above it
                     would reference a variable that is out of scope there. -->
                <HintTooltip
                  v-for="source in variable.sources"
                  :key="`${source.deviceId}:${source.role}`"
                  :content="getEnvironmentSourceTitle(source)"
                >
                  <button
                    type="button"
                    class="board-chip-info max-w-full truncate rounded-full px-2 py-0.5 text-[length:var(--iot-font-min)] font-bold transition-colors"
                    @click="handleDeviceClick(source.deviceId)"
                  >
                    {{ source.label }}
                  </button>
                </HintTooltip>
              </div>
            </div>
          </article>
        </div>

        <div v-else-if="environmentPoolExpanded" class="rounded-lg border border-dashed board-border-subtle board-chip-info px-3 py-4 text-center text-xs font-medium">
          {{ t('app.noEnvironmentVariables') }}
        </div>
      </section>

      <!-- Device List Section -->
      <div
        v-if="activeSection === 'devices'"
        id="inspector-panel-devices"
        role="tabpanel"
        aria-labelledby="inspector-tab-devices"
        data-testid="inspector-section-devices"
      >
        <div class="mb-3 flex items-center justify-between gap-2">
          <button
            type="button"
            data-testid="inspector-section-toggle-devices"
            class="flex min-h-11 min-w-0 flex-1 items-center gap-2 rounded-lg px-1 py-1 text-left transition-colors hover:bg-slate-100 dark:hover:bg-slate-800"
            :aria-expanded="sectionExpanded.devices"
            @click="toggleEntitySection('devices')"
          >
            <span class="material-symbols-outlined text-slate-400" aria-hidden="true">
              {{ sectionExpanded.devices ? 'expand_more' : 'chevron_right' }}
            </span>
            <span class="material-symbols-outlined text-slate-400" aria-hidden="true">devices</span>
            <h3 class="min-w-0 truncate text-xs font-bold uppercase tracking-widest text-slate-500" :data-full-text="t('app.devicesTool')">
              {{ t('app.devicesTool') }}
            </h3>
            <span class="ml-auto shrink-0 rounded-full bg-slate-100 px-2 py-0.5 text-[length:var(--iot-font-min)] font-bold text-slate-500">
              {{ sectionCounts.devices.filtered }}/{{ sectionCounts.devices.total }}
            </span>
          </button>
          <!-- A 44px target. Measured at **26×36px**, the smallest control in this panel and the primary way to
               add a device to the board — `p-1.5` around a `text-sm` glyph gives whatever size the glyph happens
               to be, which is not a target size. -->
          <HintTooltip :content="mutationTitle(t('app.openDeviceCreator'))">
            <button
              type="button"
              data-testid="inspector-add-device"
              @click="handleAddDevice"
              :disabled="props.readOnly"
              class="inline-flex h-11 w-11 shrink-0 items-center justify-center rounded-lg text-slate-500 transition-all hover:board-text-info hover:board-chip-info"
              :aria-label="t('app.openDeviceCreator')"
            >
              <span class="material-symbols-outlined text-sm">add</span>
            </button>
          </HintTooltip>
        </div>

        <div v-if="sectionExpanded.devices" class="space-y-2.5">
          <label class="relative block">
            <span class="material-symbols-outlined pointer-events-none absolute left-2.5 top-1/2 -translate-y-1/2 text-sm text-slate-400" aria-hidden="true">search</span>
            <input
              v-model="sectionSearch.devices"
              data-testid="inspector-search-devices"
              type="search"
              class="w-full min-h-11 rounded-lg border border-slate-200 bg-white py-2 pl-8 pr-8 text-xs font-semibold text-slate-700 outline-none transition focus:border-[color:var(--accent-border)] focus:ring-2 focus:ring-[color:var(--accent-border)] dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
              :placeholder="t('app.searchDevice')"
              :aria-label="t('app.searchDevice')"
            />
            <HintTooltip :content="t('app.clearSearch')">
              <button
                v-if="sectionSearch.devices"
                type="button"
                class="absolute right-1.5 top-1/2 inline-flex h-6 w-6 -translate-y-1/2 items-center justify-center rounded-md text-slate-500 hover:bg-slate-100 hover:text-slate-700"
                :aria-label="t('app.clearSearch')"
                @click="clearSectionSearch('devices')"
              >
                <span class="material-symbols-outlined text-sm" aria-hidden="true">close</span>
              </button>
            </HintTooltip>
          </label>

          <div
            v-for="device in filteredDevices"
            :key="device.id"
            :data-device-id="device.id"
            class="group relative p-4 rounded-xl bg-white border border-slate-200/60 hover:border-[color:var(--accent)]/50 shadow-sm hover:shadow-md transition-all"
            :class="device.id === props.focusedDeviceId ? 'ring-2 ring-[color:var(--accent-border)] board-border-subtle board-chip-info shadow-md' : ''"
          >
            <!-- Hover gradient background -->
            <div class="pointer-events-none absolute inset-0 bg-[color:var(--accent-surface)] opacity-0 group-hover:opacity-100 transition-opacity duration-300"></div>

            <div class="relative flex min-w-0 items-center justify-between gap-2">
              <!--
                The name gets its own line; the qualifiers get the next one.

                Three items competed for one 320px row before this — name, template chip, state chip —
                and the name lost every time. It carried `flex-1`, i.e. `flex-basis: 0`, so it entered
                the squeeze at zero width and grew only from whatever the chips left over, while each
                chip sized from its own content first. Measured at 1440px: "Air Conditioner" was given
                **23px of the 102px it needs (77% lost)**, rendering as "A…", with "Window" at 23/55px.
                An earlier pass tried to fix this by re-ranking the flex factors, but no ranking wins
                when the row cannot hold all three: at 320px the chips' own ceilings (4.5rem + 4rem)
                plus the icon and delete button already consume the width.

                Reviews across six passes, both themes, both locales, desktop and mobile, all reported
                the same thing — unidentifiable device names. `title` and `data-full-text` were present
                throughout, which is why it kept being recorded as "recoverable" and left alone. A
                tooltip is not identification: it answers one device at a time, on hover, and never
                helps a keyboard or touch user scanning a list for the one they want.
              -->
              <HintTooltip :content="device.name">
                <button
                  type="button"
                  class="flex min-h-11 min-w-0 flex-1 flex-col items-start justify-center gap-0.5 rounded-md py-1 text-left focus-visible:outline focus-visible:outline-3 focus-visible:outline-offset-2 focus-visible:outline-[color:var(--accent)]"
                  :aria-label="device.name"
                  @click="handleDeviceClick(device.id)"
                >
                  <span class="flex min-w-0 max-w-full items-center gap-2">
                    <span class="flex h-7 w-7 shrink-0 items-center justify-center rounded-md border board-border-subtle board-chip-info board-text-info">
                      <span class="material-symbols-outlined text-base" aria-hidden="true">devices_other</span>
                    </span>
                    <span class="min-w-0 truncate text-sm font-semibold text-slate-700 group-hover:board-text-info transition-colors" :data-full-text="device.name">
                      {{ device.name }}
                    </span>
                  </span>
                  <!--
                    Secondary line, indented to the name's text edge. The chips keep `data-full-text` for
                    the inspector's on-demand tooltip, but now they truncate against the full panel width
                    instead of against whatever the name did not take.
                  -->
                  <span v-if="device.type || device.state" class="flex min-w-0 max-w-full items-center gap-1 pl-9">
                    <span v-if="device.type" class="min-w-0 shrink truncate px-2 py-0.5 rounded-full text-[length:var(--iot-font-min)] font-medium bg-slate-100 text-slate-500 border border-slate-200" :data-full-text="device.type">
                      {{ device.type }}
                    </span>
                    <span v-if="device.state" class="min-w-0 shrink truncate px-2 py-0.5 rounded text-[length:var(--iot-font-min)] font-medium board-chip-info board-text-info border board-border-subtle" :data-full-text="device.state">
                      {{ device.state }}
                    </span>
                  </span>
                </button>
              </HintTooltip>
              <HintTooltip :content="mutationTitle(t('app.removeDevice'))">
                <button
                  type="button"
                  @click.stop="handleDeleteDevice(device.id)"
                  :disabled="props.readOnly"
                  class="relative z-10 inline-flex h-11 w-11 shrink-0 items-center justify-center rounded-lg text-slate-500 opacity-0 transition-all hover:board-chip-danger hover:board-text-danger focus:opacity-100 group-hover:opacity-100 group-focus-within:opacity-100"
                  :aria-label="t('app.removeDevice')"
                >
                  <span class="material-symbols-outlined text-sm">close</span>
                </button>
              </HintTooltip>
            </div>
          </div>

          <div v-if="displayDevices.length === 0" class="text-center py-6 text-slate-500 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">devices</span>
            <!-- "No devices" is a claim about the board. During a failed load the panel does not know
                 whether the board is empty, so it says what it actually knows instead. -->
            <p v-if="props.dataUnavailable" class="text-xs mb-3">{{ t('app.boardDataUnavailableShort') }}</p>
            <p v-else class="text-xs mb-3">{{ t('app.noDevicesOnCanvas') }}</p>
            <button
              type="button"
              @click="handleAddDevice"
              :disabled="props.readOnly"
              class="mx-auto inline-flex items-center gap-1.5 rounded-lg bg-[color:var(--accent-fill)] px-3 py-1.5 text-xs font-bold text-white shadow-sm hover:bg-[color:var(--accent-fill-hover)]"
            >
              <span class="material-symbols-outlined text-sm">add</span>
              {{ t('app.openDeviceCreator') }}
            </button>
          </div>
          <div v-else-if="filteredDevices.length === 0" class="text-center py-6 text-slate-500 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">search_off</span>
            <p class="text-xs font-semibold">{{ t('app.noMatchingDevices') }}</p>
            <p class="mt-1 text-[11px]">{{ t('app.tryDifferentSearchTerm') }}</p>
          </div>
        </div>
      </div>

      <!-- Active Global Rules Section -->
      <div
        v-if="activeSection === 'rules'"
        id="inspector-panel-rules"
        role="tabpanel"
        aria-labelledby="inspector-tab-rules"
        data-testid="inspector-section-rules"
      >
        <div class="mb-3 flex items-center justify-between gap-2">
          <button
            type="button"
            data-testid="inspector-section-toggle-rules"
            class="flex min-h-11 min-w-0 flex-1 items-center gap-2 rounded-lg px-1 py-1 text-left transition-colors hover:bg-slate-100 dark:hover:bg-slate-800"
            :aria-expanded="sectionExpanded.rules"
            @click="toggleEntitySection('rules')"
          >
            <span class="material-symbols-outlined text-slate-400" aria-hidden="true">
              {{ sectionExpanded.rules ? 'expand_more' : 'chevron_right' }}
            </span>
            <span class="material-symbols-outlined text-slate-400" aria-hidden="true">rule</span>
            <h3 class="min-w-0 truncate text-xs font-bold uppercase tracking-widest text-slate-500" :data-full-text="t('app.rulesTool')">
              {{ t('app.rulesTool') }}
            </h3>
            <span class="ml-auto shrink-0 rounded-full bg-slate-100 px-2 py-0.5 text-[length:var(--iot-font-min)] font-bold text-slate-500">
              {{ sectionCounts.rules.filtered }}/{{ sectionCounts.rules.total }}
            </span>
          </button>
          <HintTooltip :content="mutationTitle(t('app.createRule'))">
            <button
              type="button"
              data-testid="inspector-add-rule"
              @click="handleAddRule"
              :disabled="props.readOnly"
              class="text-slate-500 hover:board-text-info hover:board-chip-info p-1.5 rounded-lg transition-all"
              :aria-label="t('app.createRule')"
            >
              <span class="material-symbols-outlined text-sm">add</span>
            </button>
          </HintTooltip>
        </div>

        <div v-if="sectionExpanded.rules" class="space-y-3">
          <label class="relative block">
            <span class="material-symbols-outlined pointer-events-none absolute left-2.5 top-1/2 -translate-y-1/2 text-sm text-slate-400" aria-hidden="true">search</span>
            <input
              v-model="sectionSearch.rules"
              data-testid="inspector-search-rules"
              type="search"
              class="w-full min-h-11 rounded-lg border border-slate-200 bg-white py-2 pl-8 pr-8 text-xs font-semibold text-slate-700 outline-none transition focus:border-[color:var(--accent-border)] focus:ring-2 focus:ring-[color:var(--accent-border)] dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
              :placeholder="t('app.searchRules')"
              :aria-label="t('app.searchRules')"
            />
            <HintTooltip :content="t('app.clearSearch')">
              <button
                v-if="sectionSearch.rules"
                type="button"
                class="absolute right-1.5 top-1/2 inline-flex h-6 w-6 -translate-y-1/2 items-center justify-center rounded-md text-slate-500 hover:bg-slate-100 hover:text-slate-700"
                :aria-label="t('app.clearSearch')"
                @click="clearSectionSearch('rules')"
              >
                <span class="material-symbols-outlined text-sm" aria-hidden="true">close</span>
              </button>
            </HintTooltip>
          </label>

          <div
            v-if="displayRules.length > 1"
            data-testid="rule-execution-order-hint"
            class="flex items-start gap-2 rounded-lg board-surface-warning px-2.5 py-2 text-[11px] font-medium leading-4 board-text-warning"
          >
            <span class="material-symbols-outlined mt-0.5 text-sm" aria-hidden="true">low_priority</span>
            <span>{{ t('app.ruleExecutionOrderHint') }}</span>
          </div>

          <div
            v-for="rule in filteredRules"
            :key="rule.id"
            :data-rule-id="rule.originalId"
            tabindex="-1"
            class="p-3 rounded-lg border relative transition-all hover:shadow-md group board-chip-info board-border-subtle hover:border-[color:var(--accent-border)]"
            :class="rule.originalId && rule.originalId === props.focusedRuleId ? 'ring-2 ring-[color:var(--accent-border)] border-[color:var(--accent-border)] shadow-md' : ''"
          >
            <!-- 蓝色背景装饰 -->
            <div class="absolute left-0 top-0 bottom-0 w-1 bg-[color:var(--accent)] rounded-l-lg"></div>
            
            <div class="flex items-start justify-between mb-2">
              <div class="flex min-w-0 items-center gap-2">
                <span class="material-symbols-outlined text-sm board-text-info">
                  auto_awesome
                </span>
                <h4 class="min-w-0 truncate text-sm font-bold board-text-info" :data-full-text="rule.name">
                  {{ rule.name }}
                </h4>
                <span
                  class="shrink-0 rounded board-chip-info px-1.5 py-0.5 text-[length:var(--iot-font-min)] font-bold board-text-info"
                  :title="t('app.ruleExecutionOrder')"
                >
                  #{{ rule.executionOrder }}
                </span>
              </div>

              <div class="flex shrink-0 items-center gap-0.5">
                <HintTooltip :content="mutationTitle(sectionSearch.rules ? t('app.ruleOrderSearchDisabled') : t('app.moveRuleEarlier'))">
                  <button
                    type="button"
                    :disabled="props.readOnly || props.rulesReordering || !!sectionSearch.rules || rule.isFirst"
                    class="rounded p-1 board-text-info transition hover:board-chip-info disabled:cursor-not-allowed disabled:opacity-30"
                    :aria-label="t('app.moveRuleEarlier')"
                    @click.stop="rule.originalId && handleMoveRule(rule.originalId, 'up')"
                  >
                    <span class="material-symbols-outlined text-sm" aria-hidden="true">arrow_upward</span>
                  </button>
                </HintTooltip>
                <HintTooltip :content="mutationTitle(sectionSearch.rules ? t('app.ruleOrderSearchDisabled') : t('app.moveRuleLater'))">
                  <button
                    type="button"
                    :disabled="props.readOnly || props.rulesReordering || !!sectionSearch.rules || rule.isLast"
                    class="rounded p-1 board-text-info transition hover:board-chip-info disabled:cursor-not-allowed disabled:opacity-30"
                    :aria-label="t('app.moveRuleLater')"
                    @click.stop="rule.originalId && handleMoveRule(rule.originalId, 'down')"
                  >
                    <span class="material-symbols-outlined text-sm" aria-hidden="true">arrow_downward</span>
                  </button>
                </HintTooltip>
                <HintTooltip :content="mutationTitle(t('app.deleteRule'))">
                  <button
                    type="button"
                    @click.stop="rule.originalId && handleDeleteRule(rule.originalId)"
                    :disabled="props.readOnly"
                    class="rounded p-1 board-text-muted transition hover:board-chip-danger hover:board-text-danger"
                    :aria-label="t('app.deleteRule')"
                  >
                    <span class="material-symbols-outlined text-sm" aria-hidden="true">delete</span>
                  </button>
                </HintTooltip>
              </div>
            </div>

            <p class="ml-6 line-clamp-2 break-words text-[11px] font-medium leading-tight board-text-info" :data-full-text="rule.description">
              {{ rule.description }}
            </p>
          </div>

          <!-- Empty state when no rules -->
          <div v-if="displayRules.length === 0" class="text-center py-6 text-slate-500 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">rule</span>
            <p class="text-xs mb-3">{{ t('app.noRulesActive') }}</p>
            <button
              type="button"
              @click="handleAddRule"
              :disabled="props.readOnly"
              class="mx-auto inline-flex items-center gap-1.5 rounded-lg bg-[color:var(--accent-fill)] px-3 py-1.5 text-xs font-bold text-white shadow-sm hover:bg-[color:var(--accent-fill-hover)]"
            >
              <span class="material-symbols-outlined text-sm">add</span>
              {{ t('app.createRule') }}
            </button>
          </div>
          <div v-else-if="filteredRules.length === 0" class="text-center py-6 text-slate-500 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">search_off</span>
            <p class="text-xs font-semibold">{{ t('app.noMatchingRules') }}</p>
            <p class="mt-1 text-[11px]">{{ t('app.tryDifferentSearchTerm') }}</p>
          </div>
        </div>
      </div>

      <!-- Specifications Section -->
      <div
        v-if="activeSection === 'specs'"
        id="inspector-panel-specs"
        role="tabpanel"
        aria-labelledby="inspector-tab-specs"
        data-testid="inspector-section-specs"
      >
        <div class="mb-3 flex items-center justify-between gap-2">
          <button
            type="button"
            data-testid="inspector-section-toggle-specs"
            class="flex min-h-11 min-w-0 flex-1 items-center gap-2 rounded-lg px-1 py-1 text-left transition-colors hover:bg-slate-100 dark:hover:bg-slate-800"
            :aria-expanded="sectionExpanded.specs"
            @click="toggleEntitySection('specs')"
          >
            <span class="material-symbols-outlined text-slate-400" aria-hidden="true">
              {{ sectionExpanded.specs ? 'expand_more' : 'chevron_right' }}
            </span>
            <span class="material-symbols-outlined text-slate-400" aria-hidden="true">fact_check</span>
            <h3 class="min-w-0 truncate text-xs font-bold uppercase tracking-widest text-slate-500" :data-full-text="t('app.specificationsTool')">
              {{ t('app.specificationsTool') }}
            </h3>
            <span class="ml-auto shrink-0 rounded-full bg-slate-100 px-2 py-0.5 text-[length:var(--iot-font-min)] font-bold text-slate-500">
              {{ sectionCounts.specs.filtered }}/{{ sectionCounts.specs.total }}
            </span>
          </button>
          <HintTooltip :content="mutationTitle(t('app.openSpecificationCreator'))">
            <button
              type="button"
              data-testid="inspector-add-spec"
              @click="handleAddSpec"
              :disabled="props.readOnly"
              class="text-slate-500 hover:board-text-info hover:board-chip-info p-1.5 rounded-lg transition-all"
              :aria-label="t('app.openSpecificationCreator')"
            >
              <span class="material-symbols-outlined text-sm">add</span>
            </button>
          </HintTooltip>
        </div>

        <div v-if="sectionExpanded.specs" class="space-y-3">
          <label class="relative block">
            <span class="material-symbols-outlined pointer-events-none absolute left-2.5 top-1/2 -translate-y-1/2 text-sm text-slate-400" aria-hidden="true">search</span>
            <input
              v-model="sectionSearch.specs"
              data-testid="inspector-search-specs"
              type="search"
              class="w-full min-h-11 rounded-lg border border-slate-200 bg-white py-2 pl-8 pr-8 text-xs font-semibold text-slate-700 outline-none transition focus:border-[color:var(--accent-border)] focus:ring-2 focus:ring-[color:var(--accent-border)] dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
              :placeholder="t('app.searchSpecifications')"
              :aria-label="t('app.searchSpecifications')"
            />
            <HintTooltip :content="t('app.clearSearch')">
              <button
                v-if="sectionSearch.specs"
                type="button"
                class="absolute right-1.5 top-1/2 inline-flex h-6 w-6 -translate-y-1/2 items-center justify-center rounded-md text-slate-500 hover:bg-slate-100 hover:text-slate-700"
                :aria-label="t('app.clearSearch')"
                @click="clearSectionSearch('specs')"
              >
                <span class="material-symbols-outlined text-sm" aria-hidden="true">close</span>
              </button>
            </HintTooltip>
          </label>

          <div
            v-for="spec in filteredSpecs"
            :key="spec.id"
            :data-spec-id="spec.id"
            tabindex="-1"
            class="p-3 rounded-lg border board-border-subtle relative transition-all hover:shadow-md bg-white group"
            :class="spec.id === props.focusedSpecId ? 'ring-2 ring-[color:var(--accent-border)] board-border-subtle shadow-md' : ''"
          >

            <div class="relative flex items-start justify-between mb-2">
              <div class="flex min-w-0 items-center gap-2">
                <span class="material-symbols-outlined text-sm board-text-info">policy</span>
                <h4 class="min-w-0 truncate text-sm font-bold text-slate-800" :data-full-text="spec.name">
                  {{ spec.name }}
                </h4>
              </div>
              <HintTooltip :content="mutationTitle(t('app.deleteSpecification'))">
                <button
                  type="button"
                  @click="handleDeleteSpec(spec.id)"
                  :disabled="props.readOnly"
                  class="text-slate-500 hover:board-text-danger p-1 rounded hover:board-chip-danger opacity-0 group-hover:opacity-100 group-focus-within:opacity-100 focus:opacity-100 transition-all"
                  :aria-label="t('app.deleteSpecification')"
                >
                  <span class="material-symbols-outlined text-xs">delete</span>
                </button>
              </HintTooltip>
            </div>

            <div class="ml-7 mb-1 text-[length:var(--iot-font-min)] font-bold uppercase tracking-wide text-slate-500">
              {{ t('app.formulaPreview') }}
            </div>
            <!-- No scroll region: this wraps. `whitespace-pre-wrap break-all` and horizontal scrolling
                 are mutually exclusive, so the `overflow-x-auto` that used to be here never did
                 anything — and converting it to the horizontal primitive would have added
                 `overflow-y: hidden`, clipping any formula longer than one line. -->
            <p class="ml-7 block max-w-full whitespace-pre-wrap break-all rounded border border-slate-100 bg-slate-50 p-1.5 font-mono text-[11px] leading-tight text-slate-600" :data-full-text="spec.formula">
              {{ spec.formula }}
            </p>
            <!-- Which reading each variable condition asks about, in the user's words rather than as the
                 `Environment.` / `<device>.` token inside the formula above. -->
            <div v-if="spec.variableSourceLabels.length" class="ml-7 mt-1 flex flex-wrap gap-1">
              <!-- An unresolved reading blocks the run, so it must not read as a neutral fact here. -->
              <span
                v-for="entry in spec.variableSourceLabels"
                :key="entry.key"
                class="rounded border px-1.5 py-0.5 text-[length:var(--iot-font-min)] font-semibold"
                :class="entry.unresolved
                  ? 'board-chip-danger board-text-danger border-[color:var(--danger-border)]'
                  : 'border-slate-200 bg-slate-100 text-slate-600'"
                data-testid="inspector-spec-variable-source"
              >{{ entry.label }}</span>
            </div>
          </div>

          <!-- Empty state when no specifications -->
          <div v-if="displaySpecs.length === 0" class="text-center py-6 text-slate-500 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">fact_check</span>
            <p class="text-xs mb-3">{{ t('app.noSpecificationsVerified') }}</p>
            <button
              type="button"
              @click="handleAddSpec"
              :disabled="props.readOnly"
              class="mx-auto inline-flex items-center gap-1.5 rounded-lg bg-[color:var(--accent-fill)] px-3 py-1.5 text-xs font-bold text-white shadow-sm hover:bg-[color:var(--accent-fill-hover)]"
            >
              <span class="material-symbols-outlined text-sm">add</span>
              {{ t('app.openSpecificationCreator') }}
            </button>
          </div>
          <div v-else-if="filteredSpecs.length === 0" class="text-center py-6 text-slate-500 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">search_off</span>
            <p class="text-xs font-semibold">{{ t('app.noMatchingSpecifications') }}</p>
            <p class="mt-1 text-[11px]">{{ t('app.tryDifferentSearchTerm') }}</p>
          </div>
        </div>
      </div>
    </div>
  </aside>

</template>

<style scoped>
/* Glass panel effect */
.glass-panel {
  background: var(--board-panel-bg);
  backdrop-filter: blur(16px);
  border: 1px solid var(--board-border);
}

[data-full-text] {
  position: relative;
}

[data-full-text]:hover,
[data-full-text]:focus-visible {
  z-index: 60;
}

.line-clamp-2 {
  display: -webkit-box;
  overflow: hidden;
  -webkit-box-orient: vertical;
  -webkit-line-clamp: 2;
}

/* Material Symbols font */
.material-symbols-outlined {
  font-family: 'Material Symbols Outlined';
}
</style>

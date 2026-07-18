<script setup lang="ts">
import { ref, reactive, computed, watch } from 'vue'
import type { DeviceNode } from '../types/node'
import type { DeviceTemplate, InternalVariable } from '../types/device'
import type { ModelEnvironmentVariable } from '@/types/model'
import type { RuleForm } from '../types/rule'
import type { Specification } from '../types/spec'
import { specTemplateDetails } from '../assets/config/specTemplates'
import { useI18n } from 'vue-i18n'
import { buildSpecFormula } from '@/utils/spec'
import { ElMessage } from 'element-plus'
import { resolveImpactEnvironmentDefinition } from '@/utils/device'
import InfoTooltip from '@/components/common/InfoTooltip.vue'

const { t } = useI18n()

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
  rulesReordering?: boolean
}

const props = withDefaults(defineProps<Props>(), {
  devices: () => [],
  deviceTemplates: () => [],
  environmentVariables: () => [],
  rules: () => [],
  specifications: () => [],
  width: 320,
  activeSection: 'devices',
  readOnly: false,
  rulesReordering: false
})

const ensureWritable = (): boolean => {
  if (!props.readOnly) return true
  ElMessage.warning({ message: t('app.playbackReadOnlyCloseFirst'), type: 'warning' })
  return false
}

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
  'toggle-rule': [ruleId: string, enabled: boolean]
  'save-environment': [variables: ModelEnvironmentVariable[]]
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

const panelWidth = computed(() => {
  const width = Number.isFinite(props.width) ? props.width : 320
  return `${Math.min(520, Math.max(240, width))}px`
})

const activeSection = computed<InspectorSection>({
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
      const hasStateMachine = Array.isArray(template?.manifest?.Modes)
        && template.manifest.Modes.length > 0
      return {
        id: device.id,
        name: device.label,
        type: device.templateName || t('app.device'),
        state: hasStateMachine ? (device.state || '') : ''
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

const defaultEnvironmentValue = (variable: InternalVariable) => {
  if (Array.isArray(variable.Values) && variable.Values.length > 0) {
    return String(variable.Values[0] || '')
  }
  if (variable.LowerBound !== undefined && variable.LowerBound !== null) {
    return String(variable.LowerBound)
  }
  return ''
}

const normalizeTrust = (value?: string | null) =>
  value === 'trusted' ? 'trusted' : 'untrusted'

const normalizePrivacy = (value?: string | null) =>
  value === 'private' ? 'private' : 'public'

const environmentPoolByName = computed(() => {
  const result = new Map<string, ModelEnvironmentVariable>()
  for (const variable of props.environmentVariables || []) {
    const name = String(variable?.name || '').trim()
    if (name) result.set(name, variable)
  }
  return result
})

type EnvironmentSourceRole = 'read' | 'impact'

interface EnvironmentSource {
  deviceId: string
  label: string
  role: EnvironmentSourceRole
}

interface EnvironmentGroup {
  name: string
  definition: InternalVariable
  ranges: string[]
  sources: EnvironmentSource[]
}

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
  source?: EnvironmentSource
) => {
  const current = grouped.get(name) || {
    name,
    definition,
    ranges: [],
    sources: []
  }
  if (!current.definition || current.definition.Name === name && !current.definition.Values && current.definition.LowerBound === undefined) {
    current.definition = definition
  }
  current.ranges.push(getVariableRange(definition))
  if (source && !current.sources.some(item => item.deviceId === source.deviceId && item.role === source.role)) {
    current.sources.push(source)
  }
  grouped.set(name, current)
}

const environmentVariables = computed(() => {
  const grouped = new Map<string, EnvironmentGroup>()

  for (const device of props.devices) {
    const template = findTemplateForDevice(device)
    const variables = template?.manifest?.InternalVariables || []
    for (const variable of variables) {
      if (!variable?.Name || variable.IsInside === true) continue

      addEnvironmentGroup(grouped, variable.Name, variable, {
        deviceId: device.id,
        label: device.label,
        role: 'read'
      })
    }

    for (const impacted of template?.manifest?.ImpactedVariables || []) {
      const name = String(impacted || '').trim()
      if (!name) continue
      addEnvironmentGroup(grouped, name, environmentDefinitionFor(name, template), {
        deviceId: device.id,
        label: device.label,
        role: 'impact'
      })
    }
  }

  for (const saved of props.environmentVariables || []) {
    const name = String(saved?.name || '').trim()
    if (!name || grouped.has(name)) continue
    addEnvironmentGroup(grouped, name, environmentDefinitionFor(name))
  }

  return Array.from(grouped.values())
    .map(variable => {
      const ranges = uniqueNonEmpty(variable.ranges)
      const saved = environmentPoolByName.value.get(variable.name)
      const value = saved?.value !== null && saved?.value !== undefined && String(saved.value).trim() !== ''
        ? String(saved.value)
        : defaultEnvironmentValue(variable.definition)
      const trust = normalizeTrust(saved?.trust || variable.definition.Trust)
      const privacy = normalizePrivacy(saved?.privacy || variable.definition.Privacy)
      return {
        ...variable,
        rangeLabel: ranges.length === 1 ? ranges[0] : t('app.mixedRanges'),
        value,
        valueLabel: value || t('app.modelControlled'),
        valueTitle: value || t('app.modelControlled'),
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

const updateEnvironmentVariable = (
  name: string,
  patch: Partial<ModelEnvironmentVariable>
) => {
  if (!ensureWritable()) return
  // The backend treats this endpoint as a name-keyed patch. Sending one field avoids
  // rebuilding the whole pool from possibly stale props when users edit quickly.
  emit('save-environment', [{ name, ...patch }])
}

const eventValue = (event: Event) =>
  (event.target as HTMLInputElement | HTMLSelectElement | null)?.value || ''

// 关系代码转可读标签
const getRelationLabel = (relation: string): string => {
  const relationMap: Record<string, string> = {
    'EQ': '=',
    'NEQ': '≠',
    'GT': '>',
    'GTE': '≥',
    'LT': '<',
    'LTE': '≤',
    'in': '∈',
    'not_in': '∉',
    'not in': '∉'
  }
  return relationMap[relation] || relation
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
      let desc = `${sourceNode?.label || t('app.unknown')}`
      
      // 如果有 itemType、relation、value 信息，显示更完整
      const sourceType = s.itemType
      if (isValueBasedRuleSource(sourceType) && s.relation && hasConditionValue(s.value)) {
        desc += ` ${s.fromApi} ${getRelationLabel(s.relation)} ${s.value}`
      } else if (sourceType === 'api') {
        desc += ` ${t('app.triggers')} ${s.fromApi}`
      } else {
        // 如果有 relation 和 value，也显示
        if (s.relation && hasConditionValue(s.value)) {
          desc += ` ${s.fromApi} ${getRelationLabel(s.relation)} ${s.value}`
        } else {
          desc += ` ${s.fromApi}`
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
        action: rule.toApi || 'N/A'
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
        nodes: props.devices,
        deviceTemplates: props.deviceTemplates
      }),
      status: t('app.active'),
      searchText: [
        spec.id,
        spec.templateId,
        spec.templateLabel,
        specType,
        deviceInfo,
        ...(spec.devices || []).flatMap(device => [device.deviceId, device.deviceLabel, ...(device.selectedApis || [])]),
        ...(spec.aConditions || []).flatMap(condition => [condition.deviceId, condition.deviceLabel, condition.targetType, condition.propertyScope, condition.key, condition.relation, condition.value]),
        ...(spec.ifConditions || []).flatMap(condition => [condition.deviceId, condition.deviceLabel, condition.targetType, condition.propertyScope, condition.key, condition.relation, condition.value]),
        ...(spec.thenConditions || []).flatMap(condition => [condition.deviceId, condition.deviceLabel, condition.targetType, condition.propertyScope, condition.key, condition.relation, condition.value])
      ].join(' ')
    }
  })
})

const filteredDevices = computed(() =>
  displayDevices.value.filter(device =>
    matchesEntitySearch([device.id, device.name, device.type, device.state], sectionSearch.devices)
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
  <aside
    data-testid="system-inspector"
    class="absolute right-0 top-0 bottom-0 glass-panel board-side-panel z-40 flex flex-col overflow-hidden border-l transition-all duration-300 ease-in-out"
    :class="isCollapsed ? 'is-collapsed' : 'is-expanded'"
    :style="{ width: isCollapsed ? '3rem' : panelWidth }"
    @pointerover="syncFullTextTitle"
    @focusin="syncFullTextTitle"
  >
    <div
      class="board-panel-header relative overflow-hidden border-b"
      :class="isCollapsed ? 'p-0.5' : 'p-4'"
    >
      <div v-if="!isCollapsed" class="flex items-center justify-between w-full">
        <div class="flex min-w-0 items-center gap-3">
          <button
            type="button"
            @click="togglePanel"
            class="board-panel-toggle inline-flex h-11 w-11 shrink-0 items-center justify-center overflow-hidden rounded-lg text-slate-400 transition-all hover:bg-slate-100 hover:text-slate-800"
            :title="t('app.collapse')"
            :aria-label="t('app.collapse')"
          >
            <span class="material-symbols-outlined text-base" aria-hidden="true">dock_to_left</span>
          </button>
          <div class="p-2 bg-blue-50 rounded-lg border border-blue-100/50 shadow-sm">
            <span class="material-symbols-outlined text-blue-600">fact_check</span>
          </div>
          <div class="min-w-0">
            <h2 class="board-panel-title text-sm font-bold leading-none truncate" :data-full-text="t('app.systemInspector')">{{ t('app.systemInspector') }}</h2>
            <p class="board-panel-subtitle text-[10px] font-medium mt-0.5 truncate" :data-full-text="t('app.currentBoardContent')">{{ t('app.currentBoardContent') }}</p>
          </div>
        </div>
      </div>
      <div v-else class="flex items-center justify-center">
        <button
          type="button"
          @click="togglePanel"
          class="board-panel-toggle inline-flex h-11 w-11 shrink-0 items-center justify-center overflow-hidden rounded-lg text-slate-400 transition-all hover:bg-slate-100 hover:text-slate-800"
          :title="t('app.expand')"
          :aria-label="t('app.expand')"
        >
          <span class="material-symbols-outlined text-base" aria-hidden="true">dock_to_left</span>
        </button>
      </div>
    </div>

    <div
      v-if="!isCollapsed"
      class="board-panel-body flex-1 overflow-y-auto custom-scrollbar transition-all duration-300 p-4 space-y-4"
    >
      <div
        class="board-segmented grid grid-cols-3 gap-1 rounded-xl border p-1"
        role="tablist"
        :aria-label="t('app.currentBoardContent')"
      >
        <button
          v-for="tab in inspectorTabs"
          :key="tab.id"
          type="button"
          role="tab"
          :data-testid="`inspector-tab-${tab.id}`"
          :aria-selected="activeSection === tab.id"
          :aria-pressed="activeSection === tab.id"
          @click="activeSection = tab.id"
          :class="[
            'min-w-0 rounded-lg px-2 py-2 text-[11px] font-bold transition-all flex items-center justify-start gap-1.5',
            activeSection === tab.id
              ? 'bg-blue-600 text-white shadow-sm'
              : 'text-slate-500 hover:bg-white hover:text-slate-800'
          ]"
        >
          <span class="material-symbols-outlined text-sm" aria-hidden="true">{{ tab.icon }}</span>
          <span class="min-w-0 flex-1 truncate text-left" :data-full-text="tab.label">{{ tab.label }}</span>
          <span
            class="shrink-0 rounded-full px-1.5 py-0.5 text-[10px] leading-none"
            :class="activeSection === tab.id ? 'bg-white/20 text-white' : 'bg-slate-200 text-slate-500'"
          >
            {{ tab.count }}
          </span>
        </button>
      </div>

      <slot name="overview" />

      <section
        data-testid="environment-pool"
        class="rounded-xl border border-amber-100 bg-amber-50/60 p-3 shadow-sm dark:border-amber-500/20 dark:bg-amber-500/10"
      >
        <div class="mb-2 flex items-start gap-2">
          <button
            type="button"
            data-testid="toggle-environment-pool"
            class="flex min-w-0 flex-1 items-start justify-between gap-3 rounded-lg text-left transition-colors hover:bg-amber-100/70 focus:outline-none focus:ring-2 focus:ring-amber-400 dark:hover:bg-amber-400/10"
            :aria-expanded="environmentPoolExpanded"
            @click="environmentPoolExpanded = !environmentPoolExpanded"
          >
          <div class="min-w-0 p-1">
            <div class="flex min-w-0 items-center gap-2">
              <span class="material-symbols-outlined text-base text-amber-600 dark:text-amber-300" aria-hidden="true">public</span>
              <h3 class="truncate text-xs font-bold uppercase tracking-widest text-amber-700 dark:text-amber-200" :data-full-text="t('app.environmentPool')">
                {{ t('app.environmentPool') }}
              </h3>
            </div>
            <p v-if="environmentPoolExpanded" class="mt-1 text-[11px] font-medium leading-snug text-amber-700/75 dark:text-amber-100/75">
              {{ t('app.environmentPoolShortHint') }}
            </p>
            <div
              v-else-if="environmentVariables.length > 0"
              class="mt-1 flex max-w-full flex-wrap gap-1"
              :title="environmentVariables.map(variable => variable.name).join(', ')"
            >
              <span
                v-for="variable in environmentVariables.slice(0, 3)"
                :key="variable.name"
                class="max-w-[6.5rem] truncate rounded-full bg-white/70 px-1.5 py-0.5 text-[10px] font-bold text-amber-700 dark:bg-slate-950/40 dark:text-amber-100"
              >
                {{ variable.name }}
              </span>
              <span
                v-if="environmentVariables.length > 3"
                class="rounded-full bg-white/70 px-1.5 py-0.5 text-[10px] font-bold text-amber-700 dark:bg-slate-950/40 dark:text-amber-100"
              >
                +{{ environmentVariables.length - 3 }}
              </span>
            </div>
          </div>
          <span class="mt-1 inline-flex shrink-0 items-center gap-1 rounded-full bg-amber-100 px-2 py-0.5 text-[10px] font-bold text-amber-700 dark:bg-amber-400/20 dark:text-amber-100">
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
            tone="amber"
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
              class="flex w-full min-w-0 items-center justify-between gap-2 rounded-md p-1 text-left transition-colors hover:bg-amber-50 focus:outline-none focus:ring-2 focus:ring-amber-400 dark:hover:bg-amber-400/10"
              :aria-expanded="isEnvironmentVariableExpanded(variable.name)"
              @click="toggleEnvironmentVariable(variable.name)"
            >
              <span class="flex min-w-0 items-center gap-2">
                <span class="material-symbols-outlined text-sm text-amber-600 dark:text-amber-300" aria-hidden="true">
                  {{ isEnvironmentVariableExpanded(variable.name) ? 'expand_less' : 'expand_more' }}
                </span>
                <span class="min-w-0">
                  <span class="block truncate text-sm font-extrabold text-slate-800 dark:text-slate-100" :data-full-text="variable.name">
                    {{ variable.name }}
                  </span>
                </span>
              </span>
              <span class="flex shrink-0 items-center gap-1.5">
                <span class="max-w-[5.5rem] truncate rounded-full bg-slate-100 px-2 py-0.5 text-[10px] font-bold text-slate-500 dark:bg-slate-800 dark:text-slate-300" :data-full-text="variable.rangeLabel">
                  {{ variable.rangeLabel }}
                </span>
                <span class="max-w-[4.5rem] truncate rounded-full bg-amber-100 px-2 py-0.5 text-[10px] font-bold text-amber-700 dark:bg-amber-400/20 dark:text-amber-100" :data-full-text="variable.valueLabel">
                  {{ variable.valueLabel }}
                </span>
              </span>
            </button>

            <div v-if="isEnvironmentVariableExpanded(variable.name)" class="mt-2 space-y-2">
              <div class="grid grid-cols-1 gap-2 text-[10px]">
                <label class="min-w-0 rounded-md bg-slate-50 p-1.5 dark:bg-slate-800">
                  <span class="block font-bold uppercase text-slate-400">{{ t('app.value') }}</span>
                  <select
                    v-if="variable.enumValues.length > 0"
                    :data-testid="`environment-value-${variable.name}`"
                    class="mt-1 w-full rounded border border-slate-200 bg-white px-2 py-1 font-semibold text-slate-700 outline-none focus:border-blue-400 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
                    :value="variable.value"
                    :aria-label="`${variable.name} ${t('app.value')}`"
                    @change="updateEnvironmentVariable(variable.name, { value: eventValue($event) })"
                  >
                    <option v-for="option in variable.enumValues" :key="option" :value="option">{{ option }}</option>
                  </select>
                  <input
                    v-else
                    :data-testid="`environment-value-${variable.name}`"
                    class="mt-1 w-full rounded border border-slate-200 bg-white px-2 py-1 font-semibold text-slate-700 outline-none focus:border-blue-400 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
                    :type="variable.lowerBound !== undefined || variable.upperBound !== undefined ? 'number' : 'text'"
                    :min="variable.lowerBound"
                    :max="variable.upperBound"
                    :value="variable.value"
                    :title="variable.valueTitle"
                    :aria-label="`${variable.name} ${t('app.value')}`"
                    @change="updateEnvironmentVariable(variable.name, { value: eventValue($event) })"
                  />
                </label>
                <details class="rounded-md border border-slate-200 bg-white/70 p-1.5 dark:border-slate-700 dark:bg-slate-900/60">
                  <summary class="cursor-pointer text-[10px] font-bold text-slate-500">{{ t('app.advancedTrustPrivacyOverrides') }}</summary>
                  <p class="mt-1 text-[10px] leading-4 text-slate-400">{{ t('app.environmentTrustOverrideHint') }}</p>
                  <div class="mt-1.5 grid grid-cols-2 gap-1.5">
                  <label class="min-w-0 rounded-md bg-slate-50 p-1.5 dark:bg-slate-800">
                    <span class="block font-bold uppercase text-slate-400">{{ t('app.trust') }}</span>
                    <select
                      :data-testid="`environment-trust-${variable.name}`"
                      class="mt-1 w-full rounded border border-slate-200 bg-white px-2 py-1 font-semibold text-slate-700 outline-none focus:border-blue-400 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
                      :value="variable.trust"
                      :aria-label="`${variable.name} ${t('app.trust')}`"
                      @change="updateEnvironmentVariable(variable.name, { trust: eventValue($event) })"
                    >
                      <option value="trusted">{{ t('app.trusted') }}</option>
                      <option value="untrusted">{{ t('app.untrusted') }}</option>
                    </select>
                  </label>
                  <label class="min-w-0 rounded-md bg-slate-50 p-1.5 dark:bg-slate-800">
                    <span class="block font-bold uppercase text-slate-400">{{ t('app.privacy') }}</span>
                    <select
                      :data-testid="`environment-privacy-${variable.name}`"
                      class="mt-1 w-full rounded border border-slate-200 bg-white px-2 py-1 font-semibold text-slate-700 outline-none focus:border-blue-400 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
                      :value="variable.privacy"
                      :aria-label="`${variable.name} ${t('app.privacy')}`"
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
                <button
                  v-for="source in variable.sources"
                  :key="`${source.deviceId}:${source.role}`"
                  type="button"
                  class="max-w-full truncate rounded-full border border-amber-200 bg-amber-50 px-2 py-0.5 text-[10px] font-bold text-amber-700 transition-colors hover:border-amber-400 hover:bg-amber-100 dark:border-amber-400/30 dark:bg-amber-400/10 dark:text-amber-100"
                  :title="getEnvironmentSourceTitle(source)"
                  @click="handleDeviceClick(source.deviceId)"
                >
                  {{ source.label }}
                </button>
              </div>
            </div>
          </article>
        </div>

        <div v-else-if="environmentPoolExpanded" class="rounded-lg border border-dashed border-amber-200 bg-white/60 px-3 py-4 text-center text-xs font-medium text-amber-700/70 dark:border-amber-400/20 dark:bg-slate-900/40 dark:text-amber-100/70">
          {{ t('app.noEnvironmentVariables') }}
        </div>
      </section>

      <!-- Device List Section -->
      <div v-if="activeSection === 'devices'" data-testid="inspector-section-devices">
        <div class="mb-3 flex items-center justify-between gap-2">
          <button
            type="button"
            data-testid="inspector-section-toggle-devices"
            class="flex min-w-0 flex-1 items-center gap-2 rounded-lg px-1 py-1 text-left transition-colors hover:bg-slate-100 dark:hover:bg-slate-800"
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
            <span class="ml-auto shrink-0 rounded-full bg-slate-100 px-2 py-0.5 text-[10px] font-bold text-slate-500">
              {{ sectionCounts.devices.filtered }}/{{ sectionCounts.devices.total }}
            </span>
          </button>
          <button
            type="button"
            data-testid="inspector-add-device"
            @click="handleAddDevice"
            class="text-slate-400 hover:text-blue-600 hover:bg-blue-50 p-1.5 rounded-lg transition-all"
            :title="t('app.openDeviceCreator')"
            :aria-label="t('app.openDeviceCreator')"
          >
            <span class="material-symbols-outlined text-sm">add</span>
          </button>
        </div>

        <div v-if="sectionExpanded.devices" class="space-y-2.5">
          <label class="relative block">
            <span class="material-symbols-outlined pointer-events-none absolute left-2.5 top-1/2 -translate-y-1/2 text-sm text-slate-400" aria-hidden="true">search</span>
            <input
              v-model="sectionSearch.devices"
              data-testid="inspector-search-devices"
              type="search"
              class="w-full rounded-lg border border-slate-200 bg-white py-2 pl-8 pr-8 text-xs font-semibold text-slate-700 outline-none transition focus:border-blue-400 focus:ring-2 focus:ring-blue-100 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
              :placeholder="t('app.searchDevice')"
              :aria-label="t('app.searchDevice')"
            />
            <button
              v-if="sectionSearch.devices"
              type="button"
              class="absolute right-1.5 top-1/2 inline-flex h-6 w-6 -translate-y-1/2 items-center justify-center rounded-md text-slate-400 hover:bg-slate-100 hover:text-slate-700"
              :title="t('app.clearSearch')"
              :aria-label="t('app.clearSearch')"
              @click="clearSectionSearch('devices')"
            >
              <span class="material-symbols-outlined text-sm" aria-hidden="true">close</span>
            </button>
          </label>

          <div
            v-for="device in filteredDevices"
            :key="device.id"
            :data-device-id="device.id"
            class="group relative p-4 rounded-xl bg-white border border-slate-200/60 hover:border-blue-300/50 shadow-sm hover:shadow-md transition-all"
            :class="device.id === props.focusedDeviceId ? 'ring-2 ring-blue-400 border-blue-300 bg-blue-50/70 shadow-md' : ''"
          >
            <!-- Hover gradient background -->
            <div class="pointer-events-none absolute inset-0 bg-gradient-to-r from-blue-50/0 to-indigo-50/0 opacity-0 group-hover:opacity-100 transition-opacity duration-300"></div>

            <div class="relative flex min-w-0 items-center justify-between gap-2">
              <button
                type="button"
                class="flex min-h-11 min-w-0 flex-1 items-center gap-3 rounded-md py-1 text-left focus-visible:outline focus-visible:outline-3 focus-visible:outline-offset-2 focus-visible:outline-blue-400"
                :aria-label="device.name"
                @click="handleDeviceClick(device.id)"
              >
                <div class="flex h-7 w-7 shrink-0 items-center justify-center rounded-md border border-cyan-100 bg-cyan-50 text-cyan-700">
                  <span class="material-symbols-outlined text-base" aria-hidden="true">devices_other</span>
                </div>
                <span class="min-w-0 truncate text-sm font-semibold text-slate-700 group-hover:text-blue-600 transition-colors" :data-full-text="device.name">
                  {{ device.name }}
                </span>
                <span v-if="device.type" class="max-w-[7rem] shrink-0 truncate px-2 py-0.5 rounded-full text-[10px] font-medium bg-slate-100 text-slate-500 border border-slate-200" :data-full-text="device.type">
                  {{ device.type }}
                </span>
                <span v-if="device.state" class="max-w-[6rem] shrink-0 truncate px-2 py-0.5 rounded text-[10px] font-medium bg-cyan-50 text-cyan-700 border border-cyan-100" :data-full-text="device.state">
                  {{ device.state }}
                </span>
              </button>
              <button
                type="button"
                @click.stop="handleDeleteDevice(device.id)"
                class="relative z-10 inline-flex h-11 w-11 shrink-0 items-center justify-center rounded-lg text-slate-300 opacity-0 transition-all hover:bg-red-50 hover:text-red-500 focus:opacity-100 group-hover:opacity-100 group-focus-within:opacity-100"
                :title="t('app.removeDevice')"
                :aria-label="t('app.removeDevice')"
              >
                <span class="material-symbols-outlined text-sm">close</span>
              </button>
            </div>
          </div>

          <div v-if="displayDevices.length === 0" class="text-center py-6 text-slate-400 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">devices</span>
            <p class="text-xs mb-3">{{ t('app.noDevicesOnCanvas') }}</p>
            <button
              type="button"
              @click="handleAddDevice"
              class="mx-auto inline-flex items-center gap-1.5 rounded-lg bg-blue-600 px-3 py-1.5 text-xs font-bold text-white shadow-sm hover:bg-blue-700"
            >
              <span class="material-symbols-outlined text-sm">add</span>
              {{ t('app.openDeviceCreator') }}
            </button>
          </div>
          <div v-else-if="filteredDevices.length === 0" class="text-center py-6 text-slate-400 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">search_off</span>
            <p class="text-xs font-semibold">{{ t('app.noMatchingDevices') }}</p>
            <p class="mt-1 text-[11px]">{{ t('app.tryDifferentSearchTerm') }}</p>
          </div>
        </div>
      </div>

      <!-- Active Global Rules Section -->
      <div v-if="activeSection === 'rules'" data-testid="inspector-section-rules">
        <div class="mb-3 flex items-center justify-between gap-2">
          <button
            type="button"
            data-testid="inspector-section-toggle-rules"
            class="flex min-w-0 flex-1 items-center gap-2 rounded-lg px-1 py-1 text-left transition-colors hover:bg-slate-100 dark:hover:bg-slate-800"
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
            <span class="ml-auto shrink-0 rounded-full bg-slate-100 px-2 py-0.5 text-[10px] font-bold text-slate-500">
              {{ sectionCounts.rules.filtered }}/{{ sectionCounts.rules.total }}
            </span>
          </button>
          <button
            type="button"
            data-testid="inspector-add-rule"
            @click="handleAddRule"
            class="text-slate-400 hover:text-blue-600 hover:bg-blue-50 p-1.5 rounded-lg transition-all"
            :title="t('app.createRule')"
            :aria-label="t('app.createRule')"
          >
            <span class="material-symbols-outlined text-sm">add</span>
          </button>
        </div>

        <div v-if="sectionExpanded.rules" class="space-y-3">
          <label class="relative block">
            <span class="material-symbols-outlined pointer-events-none absolute left-2.5 top-1/2 -translate-y-1/2 text-sm text-slate-400" aria-hidden="true">search</span>
            <input
              v-model="sectionSearch.rules"
              data-testid="inspector-search-rules"
              type="search"
              class="w-full rounded-lg border border-slate-200 bg-white py-2 pl-8 pr-8 text-xs font-semibold text-slate-700 outline-none transition focus:border-blue-400 focus:ring-2 focus:ring-blue-100 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
              :placeholder="t('app.searchRules')"
              :aria-label="t('app.searchRules')"
            />
            <button
              v-if="sectionSearch.rules"
              type="button"
              class="absolute right-1.5 top-1/2 inline-flex h-6 w-6 -translate-y-1/2 items-center justify-center rounded-md text-slate-400 hover:bg-slate-100 hover:text-slate-700"
              :title="t('app.clearSearch')"
              :aria-label="t('app.clearSearch')"
              @click="clearSectionSearch('rules')"
            >
              <span class="material-symbols-outlined text-sm" aria-hidden="true">close</span>
            </button>
          </label>

          <div
            v-if="displayRules.length > 1"
            data-testid="rule-execution-order-hint"
            class="flex items-start gap-2 rounded-lg border border-amber-200 bg-amber-50 px-2.5 py-2 text-[11px] font-medium leading-4 text-amber-900 dark:border-amber-800 dark:bg-amber-950/30 dark:text-amber-200"
          >
            <span class="material-symbols-outlined mt-0.5 text-sm" aria-hidden="true">low_priority</span>
            <span>{{ t('app.ruleExecutionOrderHint') }}</span>
          </div>

          <div
            v-for="rule in filteredRules"
            :key="rule.id"
            :data-rule-id="rule.originalId"
            tabindex="0"
            class="p-3 rounded-lg border relative transition-all hover:shadow-md group bg-blue-50 border-blue-200 hover:border-blue-400"
            :class="rule.originalId && rule.originalId === props.focusedRuleId ? 'ring-2 ring-blue-400 border-blue-400 shadow-md' : ''"
          >
            <!-- 蓝色背景装饰 -->
            <div class="absolute left-0 top-0 bottom-0 w-1 bg-blue-500 rounded-l-lg"></div>
            
            <div class="flex items-start justify-between mb-2">
              <div class="flex min-w-0 items-center gap-2">
                <span class="material-symbols-outlined text-sm text-blue-600">
                  auto_awesome
                </span>
                <h4 class="min-w-0 truncate text-sm font-bold text-blue-800" :data-full-text="rule.name">
                  {{ rule.name }}
                </h4>
                <span
                  class="shrink-0 rounded bg-blue-100 px-1.5 py-0.5 text-[10px] font-bold text-blue-700"
                  :title="t('app.ruleExecutionOrder')"
                >
                  #{{ rule.executionOrder }}
                </span>
              </div>

              <div class="flex shrink-0 items-center gap-0.5">
                <button
                  type="button"
                  :disabled="props.rulesReordering || !!sectionSearch.rules || rule.isFirst"
                  class="rounded p-1 text-blue-500 transition hover:bg-blue-100 disabled:cursor-not-allowed disabled:opacity-30"
                  :title="sectionSearch.rules ? t('app.ruleOrderSearchDisabled') : t('app.moveRuleEarlier')"
                  :aria-label="t('app.moveRuleEarlier')"
                  @click.stop="rule.originalId && handleMoveRule(rule.originalId, 'up')"
                >
                  <span class="material-symbols-outlined text-sm" aria-hidden="true">arrow_upward</span>
                </button>
                <button
                  type="button"
                  :disabled="props.rulesReordering || !!sectionSearch.rules || rule.isLast"
                  class="rounded p-1 text-blue-500 transition hover:bg-blue-100 disabled:cursor-not-allowed disabled:opacity-30"
                  :title="sectionSearch.rules ? t('app.ruleOrderSearchDisabled') : t('app.moveRuleLater')"
                  :aria-label="t('app.moveRuleLater')"
                  @click.stop="rule.originalId && handleMoveRule(rule.originalId, 'down')"
                >
                  <span class="material-symbols-outlined text-sm" aria-hidden="true">arrow_downward</span>
                </button>
                <button
                  type="button"
                  @click.stop="rule.originalId && handleDeleteRule(rule.originalId)"
                  class="rounded p-1 text-blue-400 transition hover:bg-red-50 hover:text-red-500"
                  :title="t('app.deleteRule')"
                  :aria-label="t('app.deleteRule')"
                >
                  <span class="material-symbols-outlined text-sm" aria-hidden="true">delete</span>
                </button>
              </div>
            </div>

            <p class="ml-6 line-clamp-2 break-words text-[11px] font-medium leading-tight text-blue-600" :data-full-text="rule.description">
              {{ rule.description }}
            </p>
          </div>

          <!-- Empty state when no rules -->
          <div v-if="displayRules.length === 0" class="text-center py-6 text-slate-400 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">rule</span>
            <p class="text-xs mb-3">{{ t('app.noRulesActive') }}</p>
            <button
              type="button"
              @click="handleAddRule"
              class="mx-auto inline-flex items-center gap-1.5 rounded-lg bg-blue-600 px-3 py-1.5 text-xs font-bold text-white shadow-sm hover:bg-blue-700"
            >
              <span class="material-symbols-outlined text-sm">add</span>
              {{ t('app.createRule') }}
            </button>
          </div>
          <div v-else-if="filteredRules.length === 0" class="text-center py-6 text-slate-400 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">search_off</span>
            <p class="text-xs font-semibold">{{ t('app.noMatchingRules') }}</p>
            <p class="mt-1 text-[11px]">{{ t('app.tryDifferentSearchTerm') }}</p>
          </div>
        </div>
      </div>

      <!-- Specifications Section -->
      <div v-if="activeSection === 'specs'" data-testid="inspector-section-specs">
        <div class="mb-3 flex items-center justify-between gap-2">
          <button
            type="button"
            data-testid="inspector-section-toggle-specs"
            class="flex min-w-0 flex-1 items-center gap-2 rounded-lg px-1 py-1 text-left transition-colors hover:bg-slate-100 dark:hover:bg-slate-800"
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
            <span class="ml-auto shrink-0 rounded-full bg-slate-100 px-2 py-0.5 text-[10px] font-bold text-slate-500">
              {{ sectionCounts.specs.filtered }}/{{ sectionCounts.specs.total }}
            </span>
          </button>
          <button
            type="button"
            data-testid="inspector-add-spec"
            @click="handleAddSpec"
            class="text-slate-400 hover:text-blue-600 hover:bg-blue-50 p-1.5 rounded-lg transition-all"
            :title="t('app.openSpecificationCreator')"
            :aria-label="t('app.openSpecificationCreator')"
          >
            <span class="material-symbols-outlined text-sm">add</span>
          </button>
        </div>

        <div v-if="sectionExpanded.specs" class="space-y-3">
          <label class="relative block">
            <span class="material-symbols-outlined pointer-events-none absolute left-2.5 top-1/2 -translate-y-1/2 text-sm text-slate-400" aria-hidden="true">search</span>
            <input
              v-model="sectionSearch.specs"
              data-testid="inspector-search-specs"
              type="search"
              class="w-full rounded-lg border border-slate-200 bg-white py-2 pl-8 pr-8 text-xs font-semibold text-slate-700 outline-none transition focus:border-blue-400 focus:ring-2 focus:ring-blue-100 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100"
              :placeholder="t('app.searchSpecifications')"
              :aria-label="t('app.searchSpecifications')"
            />
            <button
              v-if="sectionSearch.specs"
              type="button"
              class="absolute right-1.5 top-1/2 inline-flex h-6 w-6 -translate-y-1/2 items-center justify-center rounded-md text-slate-400 hover:bg-slate-100 hover:text-slate-700"
              :title="t('app.clearSearch')"
              :aria-label="t('app.clearSearch')"
              @click="clearSectionSearch('specs')"
            >
              <span class="material-symbols-outlined text-sm" aria-hidden="true">close</span>
            </button>
          </label>

          <div
            v-for="spec in filteredSpecs"
            :key="spec.id"
            :data-spec-id="spec.id"
            tabindex="0"
            class="p-3 rounded-lg border border-cyan-100 relative transition-all hover:shadow-md bg-white group"
            :class="spec.id === props.focusedSpecId ? 'ring-2 ring-cyan-300 border-cyan-300 shadow-md' : ''"
          >
            <!-- Subtle background pulse -->
            <div class="absolute inset-0 bg-cyan-50/30 pointer-events-none"></div>

            <div class="relative flex items-start justify-between mb-2">
              <div class="flex min-w-0 items-center gap-2">
                <span class="material-symbols-outlined text-sm text-cyan-600">policy</span>
                <h4 class="min-w-0 truncate text-sm font-bold text-slate-800" :data-full-text="spec.name">
                  {{ spec.name }}
                </h4>
              </div>
              <button
                type="button"
                @click="handleDeleteSpec(spec.id)"
                class="text-slate-300 hover:text-red-500 p-1 rounded hover:bg-red-50 opacity-0 group-hover:opacity-100 group-focus-within:opacity-100 focus:opacity-100 transition-all"
                :title="t('app.deleteSpecification')"
                :aria-label="t('app.deleteSpecification')"
              >
                <span class="material-symbols-outlined text-xs">delete</span>
              </button>
            </div>

            <div class="ml-7 mb-1 text-[10px] font-bold uppercase tracking-wide text-slate-400">
              {{ t('app.formulaPreview') }}
            </div>
            <p class="ml-7 block max-w-full overflow-x-auto whitespace-pre-wrap break-all rounded border border-slate-100 bg-slate-50 p-1.5 font-mono text-[11px] leading-tight text-slate-600" :data-full-text="spec.formula">
              {{ spec.formula }}
            </p>
          </div>

          <!-- Empty state when no specifications -->
          <div v-if="displaySpecs.length === 0" class="text-center py-6 text-slate-400 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">fact_check</span>
            <p class="text-xs mb-3">{{ t('app.noSpecificationsVerified') }}</p>
            <button
              type="button"
              @click="handleAddSpec"
              class="mx-auto inline-flex items-center gap-1.5 rounded-lg bg-blue-600 px-3 py-1.5 text-xs font-bold text-white shadow-sm hover:bg-blue-700"
            >
              <span class="material-symbols-outlined text-sm">add</span>
              {{ t('app.openSpecificationCreator') }}
            </button>
          </div>
          <div v-else-if="filteredSpecs.length === 0" class="text-center py-6 text-slate-400 border border-dashed border-slate-200 rounded-lg">
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
  background: var(--board-panel-bg, rgba(255, 255, 255, 0.7));
  backdrop-filter: blur(16px);
  border: 1px solid var(--board-border, rgba(226, 232, 240, 0.8));
}

/* Custom scrollbar */
.custom-scrollbar::-webkit-scrollbar {
  width: 4px;
}

.custom-scrollbar::-webkit-scrollbar-track {
  background: rgba(0, 0, 0, 0.02);
}

.custom-scrollbar::-webkit-scrollbar-thumb {
  background: rgba(0, 0, 0, 0.1);
  border-radius: 10px;
}

.custom-scrollbar::-webkit-scrollbar-thumb:hover {
  background: rgba(0, 0, 0, 0.2);
}

/* Utility classes */
.text-primary {
  color: #2563EB;
}

.bg-online {
  background-color: #059669;
}

.bg-offline {
  background-color: #dc2626;
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

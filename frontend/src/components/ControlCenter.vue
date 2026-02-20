<script setup lang="ts">
import { ref, reactive, computed } from 'vue'
import { useRouter } from 'vue-router'
import { ElMessage as ElMessageRaw } from 'element-plus'
import { 
  specTemplateDetails, 
  relationOperators, 
  targetTypes 
} from '@/assets/config/specTemplates.ts'
import type { 
  SpecTemplateId, 
  SpecTemplateType, 
  SpecCondition, 
  SpecSide,
} from '@/types/spec'
import { getCachedManifestForNode } from '@/utils/templateCache'
import { getDefaultDeviceIcon } from '@/utils/device'

// Element-Plus typings vary by version; we use an `any` alias to keep runtime behavior (e.g. `center`) without TS errors.
const ElMessage = ElMessageRaw as any

const router = useRouter()

// Props
interface Props {
  deviceTemplates?: any[]
  nodes?: any[]
  edges?: any[]
  canvasPan?: { x: number; y: number }
  canvasZoom?: number
}

const props = withDefaults(defineProps<Props>(), {
  deviceTemplates: () => [],
  nodes: () => [],
  edges: () => [],
  canvasPan: () => ({ x: 0, y: 0 }),
  canvasZoom: 1
})

// Device form data
const deviceForm = reactive({
  name: '',
  type: '',
  id: 'AUTO'
})

// Device types - dynamically loaded from backend device templates
const deviceTypes = computed(() => {
  // Only use templates loaded from backend
  return props.deviceTemplates
    .map((tpl: any) => tpl.manifest?.Name || tpl.name)
    .filter((name: string) => name) // Remove empty names
})

// Get template icon SVG
const getTemplateIcon = (template: any): string => {
  const name = template.manifest?.Name || template.name
  return getDefaultDeviceIcon(name)
}

// Specification form data
const specForm = reactive({
  templateId: '' as SpecTemplateId | '',
  templateType: '' as SpecTemplateType | '',
  selectedDevices: [] as Array<{deviceId: string, deviceLabel: string, selectedApis: string[]}>,
  formula: '',
  aConditions: [] as unknown as SpecCondition[],
  ifConditions: [] as unknown as SpecCondition[],
  thenConditions: [] as unknown as SpecCondition[]
})

// Specification dialog state
const showSpecDialog = ref(false)
const editingConditionIndex = ref(-1)
const editingConditionSide = ref<SpecSide>('a')

// Editing condition data
const editingConditionData = reactive<Partial<SpecCondition>>({
  id: '',
  side: 'a',
  deviceId: '',
  deviceLabel: '',
  targetType: 'state',
  key: '',
  relation: '=',
  value: ''
})

// Dialog states
const showDeleteConfirmDialog = ref(false)
const templateToDelete = ref<any>(null)

// Get current template details
const currentTemplateDetail = computed(() => {
  if (!specForm.templateId) return null
  return specTemplateDetails.find(t => t.id === specForm.templateId)
})

// Get required sides for current template
const requiredSides = computed(() => {
  return currentTemplateDetail.value?.requiredSides || []
})

// Check if a side is required for current template
const isSideRequired = (side: SpecSide) => {
  return requiredSides.value.includes(side)
}

// Get conditions for a specific side
const getConditionsForSide = (side: SpecSide): SpecCondition[] => {
  switch (side) {
    case 'a': return specForm.aConditions
    case 'if': return specForm.ifConditions
    case 'then': return specForm.thenConditions
    default: return []
  }
}

// Generate unique ID for condition
const generateConditionId = () => {
  return `cond-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`
}

// Open condition dialog for adding/editing
const openConditionDialog = (side: SpecSide, index: number = -1) => {
  editingConditionSide.value = side
  editingConditionIndex.value = index
  
  if (index >= 0) {
    // Edit existing condition
    const conditions = getConditionsForSide(side)
    const condition = conditions[index]
    Object.assign(editingConditionData, condition)
  } else {
    // Add new condition - reset to defaults
    Object.assign(editingConditionData, {
      id: generateConditionId(),
      side,
      deviceId: '',
      deviceLabel: '',
      targetType: 'state',
      key: '',
      relation: '=',
      value: ''
    })
  }
  showSpecDialog.value = true
}

// Save condition from dialog
const saveCondition = () => {
  if (!editingConditionData.deviceId) {
    ElMessage.warning({
      message: 'Please select a device',
      center: true
    })
    return
  }
  if (!editingConditionData.targetType) {
    ElMessage.warning({
      message: 'Please select a type',
      center: true
    })
    return
  }
  if (editingConditionData.targetType !== 'state' && !editingConditionData.key) {
    ElMessage.warning({
      message: 'Please select a property',
      center: true
    })
    return
  }
  
  const device = props.nodes.find(n => n.label === editingConditionData.deviceId)
  const condition: SpecCondition = {
    id: editingConditionData.id || generateConditionId(),
    side: editingConditionSide.value,
    deviceId: editingConditionData.deviceId,  // Now stores node.label (for backend compatibility)
    deviceLabel: device?.label || editingConditionData.deviceId,
    targetType: editingConditionData.targetType || 'state',
    key: editingConditionData.key,
    relation: editingConditionData.relation || '=',
    value: editingConditionData.value || ''
  }
  
  switch (editingConditionSide.value) {
    case 'a':
      if (editingConditionIndex.value >= 0) {
        specForm.aConditions[editingConditionIndex.value] = condition
      } else {
        specForm.aConditions.push(condition)
      }
      break
    case 'if':
      if (editingConditionIndex.value >= 0) {
        specForm.ifConditions[editingConditionIndex.value] = condition
      } else {
        specForm.ifConditions.push(condition)
      }
      break
    case 'then':
      if (editingConditionIndex.value >= 0) {
        specForm.thenConditions[editingConditionIndex.value] = condition
      } else {
        specForm.thenConditions.push(condition)
      }
      break
  }
  
  showSpecDialog.value = false
  updateFormula()
}

// Remove condition
const removeCondition = (side: SpecSide, index: number) => {
  switch (side) {
    case 'a':
      specForm.aConditions.splice(index, 1)
      break
    case 'if':
      specForm.ifConditions.splice(index, 1)
      break
    case 'then':
      specForm.thenConditions.splice(index, 1)
      break
  }
  updateFormula()
}

// Get device display name
const getDeviceLabel = (deviceIdOrLabel: string) => {
  // deviceIdOrLabel can be either node.id or node.label (for backward compatibility)
  const device = props.nodes.find(n => n.id === deviceIdOrLabel || n.label === deviceIdOrLabel)
  return device?.label || deviceIdOrLabel
}

// Get device template
const getDeviceTemplate = (deviceIdOrLabel: string) => {
  // deviceIdOrLabel can be either node.id or node.label (for backward compatibility)
  const device = props.nodes.find(n => n.id === deviceIdOrLabel || n.label === deviceIdOrLabel)
  if (!device) return null

  // Try different ways to match the template
  let template = props.deviceTemplates.find(t => t.manifest?.Name === device.templateName)

  // If not found, try with lowercase comparison
  if (!template) {
    template = props.deviceTemplates.find(t =>
      t.manifest?.Name?.toLowerCase() === device.templateName?.toLowerCase()
    )
  }

  // If still not found, try to match by checking if template name is part of device templateName
  if (!template && device.templateName) {
    template = props.deviceTemplates.find(t =>
      device.templateName.toLowerCase().includes(t.manifest?.Name?.toLowerCase()) ||
      t.manifest?.Name?.toLowerCase().includes(device.templateName?.toLowerCase())
    )
  }

  // If template is missing (e.g. deleted), fallback to cached manifest snapshot for THIS node.
  if (!template) {
    const cachedManifest = getCachedManifestForNode(device.id)
    if (cachedManifest) {
      return { manifest: cachedManifest }
    }
  }

  return template || null
}

// Get available keys based on target type for a device
const getAvailableKeys = (deviceId: string, targetType: string): Array<{label: string, value: string}> => {
  const template = getDeviceTemplate(deviceId)
  if (!template || !template.manifest) return []

  const keys: Array<{label: string, value: string}> = []

  // Internal Variables
  if (targetType === 'variable' && template.manifest.InternalVariables) {
    template.manifest.InternalVariables.forEach((v: any) => {
      keys.push({ label: v.Name, value: v.Name })
    })
  }

  // Impacted Variables (外部影响变量)
  if (targetType === 'variable' && template.manifest.ImpactedVariables) {
    template.manifest.ImpactedVariables.forEach((v: any) => {
      const varName = typeof v === 'string' ? v : (v.Name || v.name || '')
      if (varName && !keys.some(k => k.value === varName)) {
        keys.push({ label: varName, value: varName })
      }
    })
  }

  if (targetType === 'state' && template.manifest.WorkingStates) {
    template.manifest.WorkingStates.forEach((s: any) => {
      keys.push({ label: s.Name, value: s.Name })
    })
  }

  if (targetType === 'api' && template.manifest.APIs) {
    template.manifest.APIs.forEach((api: any) => {
      keys.push({ label: api.Name, value: api.Name })
    })
  }

  return keys
}

// Computed available keys for current editing condition
const availableKeys = computed(() => {
  if (!editingConditionData.deviceId) return []
  return getAvailableKeys(editingConditionData.deviceId, editingConditionData.targetType || 'state')
})

// Handle target type change to reset related fields
const handleTargetTypeChange = () => {
  editingConditionData.key = ''
  editingConditionData.value = ''
  // Reset relation to default based on new type
  if (editingConditionData.targetType === 'state') {
    editingConditionData.relation = 'in'
  } else {
    editingConditionData.relation = '='
  }
}

// Check if relation and value fields should be shown
// Show for Variable and State. Hidden for API type.
// Also, ensure it's shown if key is not selected (handled by disabled state), but here we specifically want Value for State.
const showRelationAndValue = computed(() => {
  // Always show relation/value for State type
  if (editingConditionData.targetType === 'state') return true
  // Hide for API type
  return editingConditionData.targetType !== 'api'
})

// Filter relation operators based on target type
const filteredRelationOperators = computed(() => {
  if (editingConditionData.targetType === 'state') {
    return relationOperators.filter(op => ['in', 'not_in'].includes(op.value))
  }
  return relationOperators
})

// Helper to safely get relation value for template logic
const currentRelation = computed(() => editingConditionData.relation || '=')

// Computed available states for the selected device (for 'in'/'not_in' selection)
const availableStates = computed(() => {
  if (!editingConditionData.deviceId) return []
  // Find the node by label (deviceId now stores label)
  const node = props.nodes.find(n => n.label === editingConditionData.deviceId)
  const manifest = node ? getCachedManifestForNode(node.id) : null
  if (!manifest || !manifest.WorkingStates) return []
  return manifest.WorkingStates.map((s: any) => s.Name)
})

// Get relation label (accepts string for flexibility)
const getRelationLabel = (relation: string) => {
  return relationOperators.find(r => r.value === relation)?.label || relation
}

// Update LTL formula based on conditions
const updateFormula = () => {
  if (!currentTemplateDetail.value) {
    specForm.formula = ''
    return
  }

  const template = currentTemplateDetail.value

  // Helper to convert conditions to string
  const conditionsToString = (conditions: SpecCondition[]) => {
    return conditions.map(c => {
      const deviceName = c.deviceLabel.toLowerCase().replace(/\s+/g, '_')
      const key = c.key
      const relation = c.relation === '!=' ? '≠' : c.relation
      const value = c.value ? ` ${relation} "${c.value}"` : ''
      return `${deviceName}_${key}${value}`
    }).join(' ∧ ')
  }

  // Build formula based on template type
  let formula = ''
  switch (template.type) {
    case 'always':
      // □A - Always A
      const aStr = conditionsToString(specForm.aConditions)
      formula = aStr ? `□(${aStr})` : '□A'
      break
    case 'eventually':
      // ◇A - Eventually A
      const evA = conditionsToString(specForm.aConditions)
      formula = evA ? `◇(${evA})` : '◇A'
      break
    case 'never':
      // □¬A - Never A
      const neverA = conditionsToString(specForm.aConditions)
      formula = neverA ? `□¬(${neverA})` : '□¬A'
      break
    case 'immediate':
      // □(A → B) - Immediate response
      const ifStr = conditionsToString(specForm.ifConditions)
      const thenStr = conditionsToString(specForm.thenConditions)
      if (ifStr && thenStr) {
        formula = `□((${ifStr}) → (${thenStr}))`
      } else if (ifStr) {
        formula = `□((${ifStr}) → B)`
      } else {
        formula = '□(A → B)'
      }
      break
    case 'response':
      // □(A → ◇B) - Eventual response
      const respIf = conditionsToString(specForm.ifConditions)
      const respThen = conditionsToString(specForm.thenConditions)
      if (respIf && respThen) {
        formula = `□((${respIf}) → ◇(${respThen}))`
      } else if (respIf) {
        formula = `□((${respIf}) → ◇B)`
      } else {
        formula = '□(A → ◇B)'
      }
      break
    case 'persistence':
      // □(A → □B) - Persistence
      const persIf = conditionsToString(specForm.ifConditions)
      const persThen = conditionsToString(specForm.thenConditions)
      if (persIf && persThen) {
        formula = `□((${persIf}) → □(${persThen}))`
      } else if (persIf) {
        formula = `□((${persIf}) → □B)`
      } else {
        formula = '□(A → □B)'
      }
      break
    case 'safety':
      // □(untrusted → ¬A) - Safety
      const safeIf = conditionsToString(specForm.ifConditions)
      const safeThen = conditionsToString(specForm.thenConditions)
      if (safeIf && safeThen) {
        formula = `□((${safeIf}) → ¬(${safeThen}))`
      } else if (safeIf) {
        formula = `□((${safeIf}) → ¬A)`
      } else {
        formula = '□(untrusted → ¬A)'
      }
      break
  }

  specForm.formula = formula
}

// Generate natural language rule description
const naturalLanguageRule = computed(() => {
  if (!currentTemplateDetail.value || specForm.templateType === '') {
    return 'Configure conditions above to generate rule description...'
  }

  const template = currentTemplateDetail.value
  const type = template.type

  // Helper to format conditions in natural language
  const formatConditions = (conditions: SpecCondition[]): string => {
    if (conditions.length === 0) return ''

    return conditions.map(c => {
      const deviceName = c.deviceLabel
      const keyName = c.key
      const relationText = getRelationLabel(c.relation || '=')
      const valueText = c.value ? ` ${relationText} "${c.value}"` : ''

      let prefix = ''
      if (c.targetType === 'variable') {
        prefix = `variable ${keyName} of`
      } else if (c.targetType === 'state') {
        prefix = `state ${keyName} of`
      } else if (c.targetType === 'api') {
        prefix = `API ${keyName} of`
      } else {
        prefix = keyName
      }

      return `${prefix} ${deviceName}${valueText}`
    }).join(' AND ')
  }

  const aConditions = formatConditions(specForm.aConditions)
  const ifConditions = formatConditions(specForm.ifConditions)
  const thenConditions = formatConditions(specForm.thenConditions)

  // Generate natural language based on template type
  switch (type) {
    case 'always':
      if (aConditions) {
        return `Always, ${aConditions} must hold true`
      }
      return 'Always condition must be satisfied'

    case 'eventually':
      if (aConditions) {
        return `Eventually, ${aConditions} must become true`
      }
      return 'Eventually condition must be satisfied'

    case 'never':
      if (aConditions) {
        return `${aConditions} must never happen`
      }
      return 'Never condition must be satisfied'

    case 'immediate':
      if (ifConditions && thenConditions) {
        return `When ${ifConditions} happens, then ${thenConditions} must happen at the same time`
      } else if (ifConditions) {
        return `When ${ifConditions} happens, some action must occur simultaneously`
      }
      return 'Configure conditions to define the immediate response rule'

    case 'response':
      if (ifConditions && thenConditions) {
        return `When ${ifConditions} happens, then ${thenConditions} must eventually happen (response pattern)`
      } else if (ifConditions) {
        return `When ${ifConditions} happens, some response must eventually occur`
      }
      return 'Configure conditions to define the response rule'

    case 'persistence':
      if (ifConditions && thenConditions) {
        return `When ${ifConditions} happens, then ${thenConditions} must happen and remain true forever`
      } else if (ifConditions) {
        return `When ${ifConditions} happens, some persistent condition must be maintained`
      }
      return 'Configure conditions to define the persistence rule'

    case 'safety':
      if (ifConditions && thenConditions) {
        return `When ${ifConditions} is detected (untrusted), ${thenConditions} must not happen`
      } else if (ifConditions) {
        return `When ${ifConditions} is detected, unsafe conditions must be prevented`
      }
      return 'Configure conditions to define the safety rule'

    default:
      return 'Configure conditions to generate rule description'
  }
})

// Handle template selection
const handleTemplateChange = () => {
  const template = currentTemplateDetail.value
  if (template) {
    specForm.templateType = template.type
    // Clear conditions when template changes
    specForm.aConditions = []
    specForm.ifConditions = []
    specForm.thenConditions = []
    updateFormula()
  }
}

// Validate specification before creation
const validateSpecification = () => {
  if (!specForm.templateId) {
    ElMessage.warning({
      message: 'Please select a template',
      center: true
    })
    return false
  }
  
  const template = currentTemplateDetail.value
  if (!template) return false
  
  // Check required conditions
  for (const side of template.requiredSides) {
    const conditions = getConditionsForSide(side)
    if (conditions.length === 0) {
      ElMessage.warning({
        message: `Please add at least one condition for "${side.toUpperCase()}"`,
        center: true
      })
      return false
    }
  }
  
  return true
}

// Create specification
const createSpecification = () => {
  if (!validateSpecification()) {
    return
  }
  
  emit('add-spec', {
    templateId: specForm.templateId,
    templateType: specForm.templateType,
    devices: specForm.selectedDevices,
    formula: specForm.formula,
    aConditions: specForm.aConditions,
    ifConditions: specForm.ifConditions,
    thenConditions: specForm.thenConditions
  })
  
  // Reset form
  resetSpecForm()
}

// Reset specification form
const resetSpecForm = () => {
  specForm.templateId = ''
  specForm.templateType = ''
  specForm.selectedDevices = []
  specForm.formula = ''
  specForm.aConditions = []
  specForm.ifConditions = []
  specForm.thenConditions = []
}

const handleCreateDevice = async () => {
  console.log('Available templates:', props.deviceTemplates)
  console.log('Selected type:', deviceForm.type)

  if (!deviceForm.name.trim()) {
    ElMessage({
      message: 'Enter device name',
      type: 'warning',
      center: true
    })
    return
  }

  if (!deviceForm.type) {
    ElMessage({
      message: 'Please select a device template',
      type: 'warning',
      center: true
    })
    return
  }

  // Find the selected template from backend templates
  let template = props.deviceTemplates.find((tpl: any) => 
    (tpl.manifest?.Name || tpl.name) === deviceForm.type
  )
  
  if (!template) {
    // Try lowercase match
    template = props.deviceTemplates.find((tpl: any) => 
      (tpl.manifest?.Name || tpl.name)?.toLowerCase() === deviceForm.type.toLowerCase()
    )
  }
  
  if (!template && props.deviceTemplates.length > 0) {
    // If still not found, use the first available template as fallback
    template = props.deviceTemplates[0]
    console.warn(`Template for type "${deviceForm.type}" not found, using fallback:`, template.manifest?.Name || template.name)
  }

  if (!template) {
    ElMessage({
      message: 'No templates available',
      type: 'error',
      center: true
    })
    return
  }

  // Emit device creation event with template
  emit('create-device', {
    template,
    customName: deviceForm.name
  })

  ElMessage({
    message: 'Device added',
    type: 'success',
    center: true
  })

  // Reset form
  deviceForm.name = ''
}

// Panel state
const isCollapsed = ref(false)

// Top-level navigation to reduce UI density
type ControlCenterSection = 'devices' | 'templates' | 'rules' | 'specs'
const activeSection = ref<ControlCenterSection>('devices')

// Toggle panel collapse
const togglePanel = () => {
  isCollapsed.value = !isCollapsed.value
}

const emit = defineEmits<{
  'create-device': [data: { template: any, customName: string }]
  'open-rule-builder': []
  'add-spec': [data: { 
    templateId: string, 
    templateType: string,
    devices: Array<{deviceId: string, deviceLabel: string, selectedApis: string[]}>, 
    formula: string,
    aConditions: SpecCondition[],
    ifConditions: SpecCondition[],
    thenConditions: SpecCondition[]
  }]
  'refresh-templates': []
  'delete-template': [templateId: string]
  'verify': []
}>()

// Component mounted


const createDevice = () => {
  handleCreateDevice()
}

const goToCreateTemplate = () => {
  router.push('/create-template')
}

const openRuleBuilder = () => {
  emit('open-rule-builder')
}

const openDeleteConfirm = (template: any) => {
  templateToDelete.value = template
  showDeleteConfirmDialog.value = true
}

const confirmDeleteTemplate = async () => {
  if (!templateToDelete.value) return

  console.log('Deleting template:', {
    id: templateToDelete.value.id,
    idType: typeof templateToDelete.value.id,
    name: templateToDelete.value.manifest.Name
  })

  try {
    const token = localStorage.getItem('iot_verify_token')
    console.log('Token exists:', !!token)

    // Ensure templateId is a valid string
    const templateId = String(templateToDelete.value.id).trim()
    console.log('Template ID to delete:', templateId)

    if (!templateId || templateId === 'undefined' || templateId === 'null') {
      throw new Error('Invalid template ID')
    }

    const response = await fetch(`/api/board/templates/${templateId}`, {
      method: 'DELETE',
      headers: {
        'Authorization': `Bearer ${token}`
      }
    })

    console.log('Delete response status:', response.status)
    console.log('Delete response ok:', response.ok)

    if (!response.ok) {
      const errorMessage = await handleApiError(response, 'Delete template')
      throw new Error(errorMessage)
    }

      ElMessage({
        message: 'Template deleted',
        type: 'success',
        center: true
      })
    emit('refresh-templates')
    showDeleteConfirmDialog.value = false
    templateToDelete.value = null
  } catch (error) {
    console.error('Failed to delete template:', error)
    const errorMessage = error instanceof Error ? error.message : 'Unknown error'
    ElMessage({
      message: `Delete failed: ${errorMessage}`,
      type: 'error',
      center: true
    })
  }
}

// Enhanced error handling utility with concise messages
const handleApiError = async (response: Response, operation: string) => {
  let errorMessage = 'Operation failed'

  try {
    const errorText = await response.text()
    console.error(`${operation} error response:`, errorText)

    // Try to parse as JSON error
    try {
      const errorData = JSON.parse(errorText)
      if (errorData.message) {
        // Shorten common error messages
        errorMessage = shortenErrorMessage(errorData.message)
      } else if (errorData.error) {
        errorMessage = shortenErrorMessage(errorData.error)
      }
    } catch {
      // Not JSON, use raw text but shorten it
      if (errorText) {
        errorMessage = errorText.length > 50 ? errorText.substring(0, 50) + '...' : errorText
      }
    }
  } catch (textError) {
    console.error('Failed to read error response:', textError)
    errorMessage = 'Server error'
  }

  return errorMessage
}

const shortenErrorMessage = (message: string): string => {
  // Shorten common error patterns
  if (message.includes('Device template already exists')) {
    return 'Template name already exists'
  }
  if (message.includes('Template not found')) {
    return 'Template not found'
  }
  if (message.includes('Invalid template ID')) {
    return 'Invalid template ID'
  }
  if (message.includes('Failed to delete template')) {
    return 'Delete failed'
  }
  if (message.includes('Failed to create template')) {
    return 'Create failed'
  }

  // For other messages, keep them short
  return message.length > 40 ? message.substring(0, 40) + '...' : message
}

const exportTemplate = (template: any) => {
  try {
    const dataStr = JSON.stringify(template.manifest, null, 2)
    const dataUri = 'data:application/json;charset=utf-8,'+ encodeURIComponent(dataStr)

    const exportFileDefaultName = `${template.manifest.Name}_template.json`

    const linkElement = document.createElement('a')
    linkElement.setAttribute('href', dataUri)
    linkElement.setAttribute('download', exportFileDefaultName)
    linkElement.click()

    ElMessage.success({
      message: 'Template exported',
      center: true
    })
  } catch (error) {
    console.error('Failed to export template:', error)
    ElMessage.error({
      message: 'Export failed',
      center: true
    })
  }
}

</script>

<template>
  <aside
    class="absolute left-0 top-0 bottom-0 modern-panel z-40 flex flex-col border-r border-white/20 shadow-xl transition-all duration-300 ease-in-out"
    :class="isCollapsed ? 'w-16' : 'w-80'"
  >
    <!-- 顶部标题区域 -->
    <div class="relative overflow-hidden p-4 bg-white border-b border-slate-200">
      <!-- 装饰性背景 -->
      <div class="absolute top-0 right-0 w-32 h-32 bg-slate-100 rounded-full -translate-y-1/2 translate-x-1/2 blur-2xl"></div>
      <div class="absolute bottom-0 left-0 w-24 h-24 bg-slate-100 rounded-full translate-y-1/2 -translate-x-1/2 blur-2xl"></div>
      
      <div v-if="!isCollapsed" class="relative flex items-center justify-between">
        <div class="flex items-center gap-3">
          <div class="w-10 h-10 bg-slate-100 rounded-xl flex items-center justify-center">
            <span class="material-symbols-outlined text-slate-600 text-xl">dashboard</span>
          </div>
          <div>
            <h2 class="text-sm font-bold text-slate-800 tracking-wide">Control Center</h2>
            <p class="text-xs text-slate-500">Device Management</p>
          </div>
        </div>
        <button
          @click="togglePanel"
          class="w-8 h-8 bg-slate-100 hover:bg-slate-200 rounded-lg flex items-center justify-center transition-all hover:scale-105"
        >
          <span class="material-symbols-outlined text-slate-600 text-base transition-transform duration-200">dock_to_left</span>
        </button>
      </div>
      <div v-else class="flex items-center justify-center">
        <button
          @click="togglePanel"
          class="w-10 h-10 bg-slate-100 hover:bg-slate-200 rounded-xl flex items-center justify-center transition-all hover:scale-105"
        >
          <span class="material-symbols-outlined text-slate-600 text-base">dock_to_right</span>
        </button>
      </div>
    </div>

    <!-- Section tabs (only when expanded) -->
    <div v-if="!isCollapsed" class="px-4 py-3 bg-white border-b border-slate-200">
      <div class="grid grid-cols-4 gap-2 p-1 bg-slate-50 rounded-xl border border-slate-200 shadow-sm">
        <button
          @click="activeSection = 'templates'"
          :class="[
            'py-2.5 rounded-lg text-xs font-semibold uppercase tracking-wider transition-all duration-200 flex flex-col items-center gap-1',
            activeSection === 'templates'
              ? 'bg-orange-500 text-white shadow-md'
              : 'text-slate-500 hover:bg-slate-200 hover:text-slate-700'
          ]"
        >
          <span class="material-symbols-outlined text-sm">inventory_2</span>
          <span class="text-[10px]">Templates</span>
        </button>
        <button
          @click="activeSection = 'devices'"
          :class="[
            'py-2.5 rounded-lg text-xs font-semibold uppercase tracking-wider transition-all duration-200 flex flex-col items-center gap-1',
            activeSection === 'devices'
              ? 'bg-purple-500 text-white shadow-md'
              : 'text-slate-500 hover:bg-slate-200 hover:text-slate-700'
          ]"
        >
          <span class="material-symbols-outlined text-sm">devices</span>
          <span class="text-[10px]">Devices</span>
        </button>
        <button
          @click="activeSection = 'rules'"
          :class="[
            'py-2.5 rounded-lg text-xs font-semibold uppercase tracking-wider transition-all duration-200 flex flex-col items-center gap-1',
            activeSection === 'rules'
              ? 'bg-blue-500 text-white shadow-md'
              : 'text-slate-500 hover:bg-slate-200 hover:text-slate-700'
          ]"
        >
          <span class="material-symbols-outlined text-sm">rule</span>
          <span class="text-[10px]">Rules</span>
        </button>
        <button
          @click="activeSection = 'specs'"
          :class="[
            'py-2.5 rounded-lg text-xs font-semibold uppercase tracking-wider transition-all duration-200 flex flex-col items-center gap-1',
            activeSection === 'specs'
              ? 'bg-red-500 text-white shadow-md'
              : 'text-slate-500 hover:bg-slate-200 hover:text-slate-700'
          ]"
        >
          <span class="material-symbols-outlined text-sm">verified</span>
          <span class="text-[10px]">Specs</span>
        </button>
      </div>
    </div>

    <div
      class="flex-1 overflow-y-auto custom-scrollbar bg-slate-50 transition-all duration-300 max-h-[calc(100vh-140px)]"
      :class="isCollapsed ? 'opacity-0 pointer-events-none p-0' : 'p-2'"
    >
      <!-- Devices -->
      <details v-if="activeSection === 'devices'" class="group mb-3 rounded-xl bg-white shadow-sm border border-slate-200 overflow-hidden" open>
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-purple-50 transition-all list-none select-none">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-purple-500 rounded-xl flex items-center justify-center">
                <span class="material-symbols-outlined text-black text-lg">add_circle</span>
            </div>
            <div>
              <span class="text-sm font-bold text-slate-800">Device Manager</span>
              <p class="text-xs text-slate-500">Add and manage devices</p>
            </div>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-lg">expand_more</span>
        </summary>

        <div class="px-3 pb-4 space-y-3 bg-slate-50/50 pt-2">
          <!-- Add Device Form -->
          <div class="space-y-3">
            <!-- Device Name -->
            <div class="relative">
              <label class="block text-[10px] font-bold text-slate-500 mb-1 uppercase tracking-wide">Device Name</label>
              <div class="relative">
                <span class="absolute left-2.5 top-1/2 -translate-y-1/2 material-symbols-outlined text-slate-400 text-xs">badge</span>
                <input
                  v-model="deviceForm.name"
                  class="w-full bg-white border-2 border-slate-200 rounded-lg px-8 py-2 text-xs text-slate-700 focus:border-purple-400 focus:ring-2 focus:ring-purple-100/50 placeholder:text-slate-400 transition-all shadow-sm"
                  placeholder="e.g. Living Room AC"
                  type="text"
                />
              </div>
            </div>

            <!-- Device Type -->
            <div class="relative">
              <label class="block text-[10px] font-bold text-slate-500 mb-1 uppercase tracking-wide">Type</label>
              <div class="relative">
                <span class="absolute left-2.5 top-1/2 -translate-y-1/2 material-symbols-outlined text-slate-400 text-xs">devices</span>
                <select
                  v-model="deviceForm.type"
                  class="w-full bg-white border-2 border-slate-200 rounded-lg px-8 py-2 text-xs text-slate-700 focus:border-purple-400 focus:ring-2 focus:ring-purple-100/50 transition-all appearance-none cursor-pointer shadow-sm"
                >
                  <option v-for="type in deviceTypes" :key="type" :value="type">{{ type }}</option>
                </select>
              </div>
            </div>

            <!-- Action Buttons -->
            <div class="space-y-2 pt-1">
              <!-- Drop Node Button for predefined types -->
              <button
                @click="createDevice()"
                class="w-full py-2.5 bg-purple-500 hover:bg-purple-600 text-white rounded-lg text-xs font-bold uppercase tracking-wider transition-all shadow-md hover:shadow-lg hover:scale-[1.02] active:scale-[0.98] flex items-center justify-center gap-1.5"
              >
                <span class="material-symbols-outlined text-sm">add_location</span>
                + Drop Node
              </button>
            </div>
          </div>
        </div>
      </details>

      <!-- Templates -->
      <details v-if="activeSection === 'templates'" class="group mb-3 rounded-xl bg-white shadow-sm border border-slate-200 overflow-hidden" open>
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-orange-50 transition-all list-none select-none">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-orange-500 rounded-xl flex items-center justify-center">
              <span class="material-symbols-outlined text-white text-lg">inventory_2</span>
            </div>
            <div>
              <span class="text-sm font-bold text-slate-800">Template Manager</span>
              <p class="text-xs text-slate-500">Design and manage templates</p>
            </div>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-lg">expand_more</span>
        </summary>

        <div class="px-3 pb-4 bg-slate-50/50 pt-2 space-y-3">
          <!-- Create New Template Button -->
          <div class="relative overflow-hidden group cursor-pointer rounded-xl bg-orange-500 hover:bg-orange-600 transition-all" @click="goToCreateTemplate">
            <div class="relative p-3 flex items-center justify-between">
              <div class="flex items-center gap-3">
                <div class="w-10 h-10 bg-orange-400 rounded-lg flex items-center justify-center">
                  <span class="material-symbols-outlined text-white text-lg">add</span>
                </div>
                <div>
                  <div class="text-sm font-bold text-white">Create New Template</div>
                </div>
              </div>
              <div class="w-8 h-8 bg-orange-400 rounded-lg flex items-center justify-center group-hover:bg-orange-300 transition-colors">
                <span class="material-symbols-outlined text-white text-sm">chevron_right</span>
              </div>
            </div>
          </div>

          <!-- Existing Templates List -->
          <div class="space-y-2">
            <div class="flex items-center gap-2 px-1">
              <span class="material-symbols-outlined text-slate-400 text-xs">folder</span>
              <h4 class="text-[10px] font-bold text-slate-500 uppercase tracking-wide">Existing Templates</h4>
              <div class="flex-1 h-px bg-slate-200"></div>
            </div>
            
            <div v-if="props.deviceTemplates.length > 0" class="grid grid-cols-1 gap-2">
              <div v-for="template in props.deviceTemplates" :key="template.id" class="group relative bg-white rounded-lg p-3 border-2 border-slate-200 hover:border-orange-300 hover:shadow-md transition-all duration-200 hover:-translate-y-0.5">
                <!-- 装饰 -->
                <div class="absolute top-0 right-0 w-16 h-16 bg-orange-100 rounded-full -translate-y-1/2 translate-x-1/2 opacity-50 group-hover:opacity-70 transition-opacity"></div>
                
                <div class="relative flex items-start justify-between mb-2">
                  <div class="flex items-center gap-2">
                    <div class="w-9 h-9 rounded-lg flex items-center justify-center bg-orange-50 group-hover:bg-orange-100 transition-all shadow-sm overflow-hidden" v-html="getTemplateIcon(template)"></div>
                    <div>
                      <h4 class="text-xs font-bold text-slate-800 group-hover:text-orange-600 transition-colors">{{ template.manifest.Name }}</h4>
                      <p v-if="template.manifest.Description" class="text-[10px] text-slate-500 mt-0.5 line-clamp-1">{{ template.manifest.Description }}</p>
                    </div>
                  </div>
                  <div class="flex gap-1">
                    <button
                      @click.stop="openDeleteConfirm(template)"
                      class="p-1.5 text-slate-400 hover:text-red-500 hover:bg-red-50 rounded-lg transition-colors opacity-0 group-hover:opacity-100"
                      title="Delete Template"
                    >
                      <span class="material-symbols-outlined text-xs">delete</span>
                    </button>
                  </div>
                </div>

                <!-- Stats Grid -->
                <div class="grid grid-cols-4 gap-1 mb-2">
                  <div class="bg-slate-50 rounded px-1.5 py-1.5 text-center border border-slate-200">
                    <div class="text-[8px] text-slate-400 uppercase font-bold">Vars</div>
                    <div class="text-xs font-bold text-slate-700">{{ template.manifest.InternalVariables?.length || 0 }}</div>
                  </div>
                  <div class="bg-slate-50 rounded px-1.5 py-1.5 text-center border border-slate-200">
                    <div class="text-[8px] text-slate-400 uppercase font-bold">APIs</div>
                    <div class="text-xs font-bold text-slate-700">{{ template.manifest.APIs?.length || 0 }}</div>
                  </div>
                  <div class="bg-slate-50 rounded px-1.5 py-1.5 text-center border border-slate-200">
                    <div class="text-[8px] text-slate-400 uppercase font-bold">States</div>
                    <div class="text-xs font-bold text-slate-700">{{ template.manifest.WorkingStates?.length || 0 }}</div>
                  </div>
                  <div class="bg-slate-50 rounded px-1.5 py-1.5 text-center border border-slate-200">
                    <div class="text-[8px] text-slate-400 uppercase font-bold">Modes</div>
                    <div class="text-xs font-bold text-slate-700">{{ template.manifest.Modes?.length || 0 }}</div>
                  </div>
                </div>

                <!-- Actions -->
                <div class="pt-2 border-t border-slate-100 flex justify-end">
                  <button
                    @click="exportTemplate(template)"
                    class="text-[10px] px-3 py-1.5 text-slate-500 hover:text-orange-600 hover:bg-orange-50 rounded-lg transition-colors flex items-center gap-1 font-medium"
                    title="Export Template"
                  >
                    <span class="material-symbols-outlined text-xs">download</span>
                    Export
                  </button>
                </div>
              </div>
            </div>

            <div v-else class="relative overflow-hidden text-center py-6 border-2 border-dashed border-slate-200 rounded-lg bg-slate-50">
              <div class="relative">
                <div class="w-12 h-12 mx-auto bg-slate-100 rounded-xl flex items-center justify-center mb-2 shadow-inner">
                  <span class="material-symbols-outlined text-slate-400 text-2xl">inventory_2</span>
                </div>
                <p class="text-xs text-slate-600 mb-0.5 font-medium">No custom templates yet</p>
                <p class="text-[10px] text-slate-400">Click "Create New Template" to get started.</p>
              </div>
            </div>
          </div>
        </div>
      </details>

      <!-- Rules -->
      <details v-if="activeSection === 'rules'" class="group mb-3 rounded-xl bg-white shadow-sm border border-slate-200 overflow-hidden" open>
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-blue-50 transition-all list-none select-none">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-blue-500 rounded-xl flex items-center justify-center">
              <span class="material-symbols-outlined text-white text-lg">function</span>
            </div>
            <div>
              <span class="text-sm font-bold text-slate-800">IFTTT Rule</span>
              <p class="text-xs text-slate-500">Create conditional logic</p>
            </div>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-lg">expand_more</span>
        </summary>

        <div class="px-3 pb-4 bg-slate-50/50 pt-2 grid grid-cols-1 gap-3">
          <!-- Rule Creation Block -->
          <div
            class="relative overflow-hidden group cursor-pointer rounded-xl bg-blue-500 hover:bg-blue-600 transition-all hover:shadow-lg hover:-translate-y-0.5"
            @click="openRuleBuilder"
          >
            <div class="relative p-3 flex items-center gap-3">
              <div class="w-10 h-10 bg-blue-400 rounded-lg flex items-center justify-center">
                <span class="material-symbols-outlined text-black text-lg">add_circle</span>
              </div>
              <div class="flex-1">
                <span class="text-sm font-bold text-white block">Create Rule</span>
                <span class="text-xs text-blue-100">IF → THEN logic</span>
              </div>
              <div class="w-7 h-7 bg-blue-400 rounded-lg flex items-center justify-center">
                <span class="material-symbols-outlined text-white text-sm">arrow_forward</span>
              </div>
            </div>
          </div>
        </div>
      </details>

      <!-- Specs -->
      <details v-if="activeSection === 'specs'" class="group mb-3 rounded-xl bg-white shadow-sm border border-slate-200 overflow-hidden" open>
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-red-50 transition-all list-none select-none">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-red-500 rounded-xl flex items-center justify-center">
              <span class="material-symbols-outlined text-white text-lg">verified</span>
            </div>
            <div>
              <span class="text-sm font-bold text-slate-800">Specifications</span>
              <p class="text-xs text-slate-500">LTL verification rules</p>
            </div>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-lg">expand_more</span>
        </summary>

        <div class="px-3 pb-4 bg-slate-50/50 pt-2 space-y-3">
          <!-- Specification Creation -->
          <div class="space-y-3">
            <!-- Step 1: Select Template -->
            <div>
              <label class="block text-[10px] font-bold text-slate-600 uppercase tracking-wide mb-2">Select Template</label>
              <select
                v-model="specForm.templateId"
                @change="handleTemplateChange"
                class="w-full bg-white border-2 border-slate-200 rounded-lg px-3 py-2 text-xs text-slate-700 focus:border-red-400 focus:ring-2 focus:ring-red-100/50 transition-all shadow-sm appearance-none cursor-pointer"
              >
                <option value="" disabled hidden>Select a specification template</option>
                <option
                  v-for="template in specTemplateDetails"
                  :key="template.id"
                  :value="template.id"
                  class="truncate"
                >
                  {{ template.label }}
                </option>
              </select>
              <p v-if="currentTemplateDetail" class="text-[10px] text-slate-500 mt-1.5 px-1">
                <span class="line-clamp-2">{{ currentTemplateDetail.description }}</span>
              </p>
            </div>

            <!-- Step 2: Add Conditions based on template requirements -->
            <div v-if="specForm.templateId" class="space-y-2">
              <label class="block text-[10px] font-bold text-slate-600 uppercase tracking-wide">Configure Conditions</label>

              <!-- A Conditions (Always/Forall) -->
              <div v-if="isSideRequired('a')" class="relative overflow-hidden rounded-lg bg-red-50 border border-red-200 p-2.5">
                <div class="relative flex items-center justify-between mb-2">
                  <div class="flex items-center gap-2">
                    <span class="w-6 h-6 bg-red-500 rounded-md flex items-center justify-center">
                      <svg class="w-4 h-4 text-white" fill="currentColor" viewBox="0 0 24 24">
                        <path d="M12 2C6.48 2 2 6.48 2 12s4.48 10 10 10 10-4.48 10-10S17.52 2 12 2zm-2 15l-5-5 1.41-1.41L10 14.17l7.59-7.59L19 8l-9 9z"/>
                      </svg>
                    </span>
                    <span class="text-[10px] font-bold text-red-700 uppercase tracking-wide">A Conditions</span>
                  </div>
                  <button
                    @click="openConditionDialog('a')"
                    class="px-2.5 py-1 bg-red-500 text-white rounded-md text-[10px] font-bold uppercase tracking-wide hover:bg-red-600 transition-all shadow-sm flex items-center gap-1"
                  >
                    <svg class="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 4v16m8-8H4"/>
                    </svg>
                    Add
                  </button>
                </div>
                <div class="space-y-1.5 max-h-36 overflow-y-auto pr-1 custom-scrollbar">
                  <div
                    v-for="(condition, index) in specForm.aConditions"
                    :key="condition.id"
                    class="flex items-center justify-between bg-white rounded-md px-2.5 py-1.5 border border-red-100 shadow-sm hover:shadow-md transition-all"
                  >
                    <div class="flex items-center gap-2 overflow-hidden flex-1">
                      <div class="w-6 h-6 bg-red-100 rounded-md flex items-center justify-center flex-shrink-0">
                        <svg class="w-3.5 h-3.5 text-red-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M9 3v2m6-2v2M9 19v2m6-2v2M5 9H3m2 6H3m18-6h-2m2 6h-2M7 19h10a2 2 0 002-2V7a2 2 0 00-2-2H7a2 2 0 00-2 2v10a2 2 0 002 2zM9 9h6v6H9V9z"/>
                        </svg>
                      </div>
                      <div class="flex items-center gap-1 overflow-hidden flex-1 min-w-0">
                        <span class="text-[10px] text-slate-700 font-medium truncate min-w-0">
                          {{ getDeviceLabel(condition.deviceId) }}
                        </span>
                        <span class="text-slate-300 flex-shrink-0">·</span>
                        <span class="text-[10px] text-red-600 font-medium truncate flex-shrink-0">{{ condition.key }}</span>
                        <span class="text-[10px] text-slate-400 bg-slate-100 px-1 py-0.5 rounded flex-shrink-0">
                          {{ getRelationLabel(condition.relation || '=') }}
                        </span>
                        <span class="text-[10px] bg-red-50 text-red-600 px-1 py-0.5 rounded truncate max-w-[60px] border border-red-200 flex-shrink-0">
                          {{ condition.value || '*' }}
                        </span>
                      </div>
                    </div>
                    <div class="flex gap-1 ml-2 flex-shrink-0">
                      <button @click="openConditionDialog('a', index)" class="p-1 text-slate-400 hover:text-slate-600 hover:bg-slate-100 rounded transition-colors" title="Edit">
                        <svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z"/>
                        </svg>
                      </button>
                      <button @click="removeCondition('a', index)" class="p-1 text-slate-400 hover:text-red-500 hover:bg-red-50 rounded transition-colors" title="Delete">
                        <svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M19 7l-.867 12.142A2 2 0 0116.138 21H7.862a2 2 0 01-1.995-1.858L5 7m5 4v6m4-6v6m1-10V4a1 1 0 00-1-1h-4a1 1 0 00-1 1v3M4 7h16"/>
                        </svg>
                      </button>
                    </div>
                  </div>
                  <div v-if="specForm.aConditions.length === 0" class="text-center py-2 text-[10px] text-slate-400 italic bg-white/50 rounded border border-dashed border-red-200">
                    No conditions added yet
                  </div>
                </div>
              </div>

              <!-- IF Conditions (Antecedent) -->
              <div v-if="isSideRequired('if')" class="relative overflow-hidden rounded-lg bg-red-50 border border-red-200 p-2.5">
                <div class="relative flex items-center justify-between mb-2">
                  <div class="flex items-center gap-2">
                    <span class="w-6 h-6 bg-red-500 rounded-md flex items-center justify-center">
                      <svg class="w-4 h-4 text-white" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M13 10V3L4 14h7v7l9-11h-7z"/>
                      </svg>
                    </span>
                    <span class="text-[10px] font-bold text-red-700 uppercase tracking-wide">IF Conditions</span>
                  </div>
                  <button
                    @click="openConditionDialog('if')"
                    class="px-2.5 py-1 bg-red-500 text-white rounded-md text-[10px] font-bold uppercase tracking-wide hover:bg-red-600 transition-all shadow-sm flex items-center gap-1"
                  >
                    <svg class="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 4v16m8-8H4"/>
                    </svg>
                    Add
                  </button>
                </div>
                <div class="space-y-1.5 max-h-36 overflow-y-auto pr-1 custom-scrollbar">
                  <div
                    v-for="(condition, index) in specForm.ifConditions"
                    :key="condition.id"
                    class="flex items-center justify-between bg-white rounded-md px-2.5 py-1.5 border border-red-100 shadow-sm hover:shadow-md transition-all"
                  >
                    <div class="flex items-center gap-2 overflow-hidden flex-1">
                      <div class="w-6 h-6 bg-red-100 rounded-md flex items-center justify-center flex-shrink-0">
                        <svg class="w-3.5 h-3.5 text-red-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M9 3v2m6-2v2M9 19v2m6-2v2M5 9H3m2 6H3m18-6h-2m2 6h-2M7 19h10a2 2 0 002-2V7a2 2 0 00-2-2H7a2 2 0 00-2 2v10a2 2 0 002 2zM9 9h6v6H9V9z"/>
                        </svg>
                      </div>
                      <div class="flex items-center gap-1 overflow-hidden flex-1 min-w-0">
                        <span class="text-[10px] text-slate-700 font-medium truncate min-w-0">
                          {{ getDeviceLabel(condition.deviceId) }}
                        </span>
                        <span class="text-slate-300 flex-shrink-0">·</span>
                        <span class="text-[10px] text-red-600 font-medium truncate flex-shrink-0">{{ condition.key }}</span>
                        <span class="text-[10px] text-slate-400 bg-slate-100 px-1 py-0.5 rounded flex-shrink-0">
                          {{ getRelationLabel(condition.relation || '=') }}
                        </span>
                        <span class="text-[10px] bg-red-50 text-red-600 px-1 py-0.5 rounded truncate max-w-[60px] border border-red-200 flex-shrink-0">
                          {{ condition.value || '*' }}
                        </span>
                      </div>
                    </div>
                    <div class="flex gap-1 ml-2 flex-shrink-0">
                      <button @click="openConditionDialog('if', index)" class="p-1 text-slate-400 hover:text-slate-600 hover:bg-slate-100 rounded transition-colors" title="Edit">
                        <svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z"/>
                        </svg>
                      </button>
                      <button @click="removeCondition('if', index)" class="p-1 text-slate-400 hover:text-red-500 hover:bg-red-50 rounded transition-colors" title="Delete">
                        <svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M19 7l-.867 12.142A2 2 0 0116.138 21H7.862a2 2 0 01-1.995-1.858L5 7m5 4v6m4-6v6m1-10V4a1 1 0 00-1-1h-4a1 1 0 00-1 1v3M4 7h16"/>
                        </svg>
                      </button>
                    </div>
                  </div>
                  <div v-if="specForm.ifConditions.length === 0" class="text-center py-2 text-[10px] text-slate-400 italic bg-white/50 rounded border border-dashed border-red-200">
                    No conditions added yet
                  </div>
                </div>
              </div>

              <!-- THEN Conditions (Consequent) -->
              <div v-if="isSideRequired('then')" class="relative overflow-hidden rounded-lg bg-yellow-50 border border-yellow-200 p-2.5">
                <div class="relative flex items-center justify-between mb-2">
                  <div class="flex items-center gap-2">
                    <span class="w-6 h-6 bg-yellow-500 rounded-md flex items-center justify-center">
                      <svg class="w-4 h-4 text-white" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M17 8l4 4m0 0l-4 4m4-4H3"/>
                      </svg>
                    </span>
                    <span class="text-[10px] font-bold text-yellow-700 uppercase tracking-wide">THEN Conditions</span>
                  </div>
                  <button
                    @click="openConditionDialog('then')"
                    class="px-2.5 py-1 bg-yellow-500 text-white rounded-md text-[10px] font-bold uppercase tracking-wide hover:bg-yellow-600 transition-all shadow-sm flex items-center gap-1"
                  >
                    <svg class="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 4v16m8-8H4"/>
                    </svg>
                    Add
                  </button>
                </div>
                <div class="space-y-1.5 max-h-36 overflow-y-auto pr-1 custom-scrollbar">
                  <div
                    v-for="(condition, index) in specForm.thenConditions"
                    :key="condition.id"
                    class="flex items-center justify-between bg-white rounded-md px-2.5 py-1.5 border border-yellow-100 shadow-sm hover:shadow-md transition-all"
                  >
                    <div class="flex items-center gap-2 overflow-hidden flex-1">
                      <div class="w-6 h-6 bg-yellow-100 rounded-md flex items-center justify-center flex-shrink-0">
                        <svg class="w-3.5 h-3.5 text-yellow-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M9 3v2m6-2v2M9 19v2m6-2v2M5 9H3m2 6H3m18-6h-2m2 6h-2M7 19h10a2 2 0 002-2V7a2 2 0 00-2-2H7a2 2 0 00-2 2v10a2 2 0 002 2zM9 9h6v6H9V9z"/>
                        </svg>
                      </div>
                      <div class="flex items-center gap-1 overflow-hidden flex-1 min-w-0">
                        <span class="text-[10px] text-slate-700 font-medium truncate min-w-0">
                          {{ getDeviceLabel(condition.deviceId) }}
                        </span>
                        <span class="text-slate-300 flex-shrink-0">·</span>
                        <span class="text-[10px] text-yellow-600 font-medium truncate flex-shrink-0">{{ condition.key }}</span>
                        <span class="text-[10px] text-slate-400 bg-slate-100 px-1 py-0.5 rounded flex-shrink-0">
                          {{ getRelationLabel(condition.relation || '=') }}
                        </span>
                        <span class="text-[10px] bg-yellow-50 text-yellow-600 px-1 py-0.5 rounded truncate max-w-[60px] border border-yellow-200 flex-shrink-0">
                          {{ condition.value || '*' }}
                        </span>
                      </div>
                    </div>
                    <div class="flex gap-1 ml-2 flex-shrink-0">
                      <button @click="openConditionDialog('then', index)" class="p-1 text-slate-400 hover:text-slate-600 hover:bg-slate-100 rounded transition-colors" title="Edit">
                        <svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z"/>
                        </svg>
                      </button>
                      <button @click="removeCondition('then', index)" class="p-1 text-slate-400 hover:text-yellow-500 hover:bg-yellow-50 rounded transition-colors" title="Delete">
                        <svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M19 7l-.867 12.142A2 2 0 0116.138 21H7.862a2 2 0 01-1.995-1.858L5 7m5 4v6m4-6v6m1-10V4a1 1 0 00-1-1h-4a1 1 0 00-1 1v3M4 7h16"/>
                        </svg>
                      </button>
                    </div>
                  </div>
                  <div v-if="specForm.thenConditions.length === 0" class="text-center py-2 text-[10px] text-slate-400 italic bg-white/50 rounded border border-dashed border-yellow-200">
                    No conditions added yet
                  </div>
                </div>
              </div>
            </div>

            <!-- Step 3: Generated Rule Description -->
            <div v-if="specForm.templateId" class="relative overflow-hidden rounded-lg bg-white border border-red-200 p-3 shadow-sm">
              <div class="relative">
                <div class="flex items-center gap-2 mb-2">
                  <span class="w-6 h-6 bg-red-100 rounded-md flex items-center justify-center">
                    <svg class="w-4 h-4 text-red-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M3 5h12M9 3v2m1.048 9.5A18.022 18.022 0 016.412 9m6.088 9h7M11 21l5-10 5 10M12.751 5C11.783 10.77 8.07 15.61 3 18.129"/>
                    </svg>
                  </span>
                  <span class="text-[10px] font-bold text-red-600 uppercase tracking-wide">Rule Description</span>
                </div>
                <div class="text-xs text-slate-700 leading-relaxed pl-8">
                  {{ naturalLanguageRule }}
                </div>
                <div class="mt-2 pt-2 border-t border-slate-200 flex items-center gap-2">
                  <span class="px-1.5 py-0.5 bg-slate-100 rounded text-[10px] font-bold text-slate-600 uppercase">LTL</span>
                  <code class="flex-1 text-[10px] bg-slate-100 text-slate-700 px-2 py-1 rounded font-mono overflow-x-auto">
                    {{ specForm.formula }}
                  </code>
                </div>
              </div>
            </div>

            <!-- Create Button -->
            <button
              @click="createSpecification"
              :disabled="!specForm.templateId"
              class="w-full py-2.5 bg-red-500 hover:bg-red-600 disabled:bg-slate-300 text-white rounded-lg text-xs font-bold uppercase tracking-wider transition-all shadow-md hover:shadow-lg hover:scale-[1.02] active:scale-[0.98] disabled:hover:scale-100 flex items-center justify-center gap-1.5 disabled:cursor-not-allowed"
            >
              <svg class="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z"/>
              </svg>
              Create Specification
            </button>
          </div>
        </div>
      </details>

      <!-- Verification Action -->
      <div class="p-4 border-t border-slate-200 bg-white">
        <button
          @click="emit('verify')"
          class="w-full py-3 bg-green-600 hover:bg-green-700 text-white rounded-lg text-sm font-bold uppercase tracking-wider transition-all shadow-md hover:shadow-lg hover:scale-[1.02] active:scale-[0.98] flex items-center justify-center gap-2"
        >
          <span class="material-symbols-outlined text-lg">verified_user</span>
          Start Verification
        </button>
      </div>

    </div>

  </aside>

  <!-- Specification Condition Dialog -->
  <div v-if="showSpecDialog" class="fixed inset-0 bg-slate-900/60 backdrop-blur-sm flex items-center justify-center z-50" @click="showSpecDialog = false">
    <div class="bg-white rounded-2xl w-full max-w-md shadow-2xl transform transition-all overflow-hidden" @click.stop>
      <!-- Header with light background -->
      <div class="relative bg-slate-100 border-b border-slate-200 p-6">
        <div class="absolute top-0 right-0 w-32 h-32 bg-slate-200/50 rounded-full -translate-y-1/2 translate-x-1/2"></div>
        <div class="absolute bottom-0 left-0 w-24 h-24 bg-slate-200/50 rounded-full translate-y-1/2 -translate-x-1/2"></div>
        
        <div class="relative flex items-center justify-between">
          <div class="flex items-center gap-4">
            <div class="w-12 h-12 bg-white shadow-sm rounded-xl flex items-center justify-center">
              <svg class="w-6 h-6 text-black" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z"/>
              </svg>
            </div>
            <div>
              <h3 class="text-xl font-bold text-black">
                {{ editingConditionIndex >= 0 ? 'Edit Condition' : 'Add Condition' }}
              </h3>
              <p class="text-sm text-slate-600">Configure your specification</p>
            </div>
          </div>
          <button 
            @click="showSpecDialog = false" 
            class="w-10 h-10 bg-white hover:bg-slate-50 rounded-lg flex items-center justify-center transition-all hover:rotate-90 shadow-sm"
          >
            <svg class="w-5 h-5 text-black" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M6 18L18 6M6 6l12 12"/>
            </svg>
          </button>
        </div>
      </div>

      <!-- Content Body -->
      <div class="p-6 space-y-6">
        <!-- Device Selection -->
        <div class="space-y-2">
          <div class="flex items-center gap-2">
            <span class="text-sm font-bold text-black">Device Selection</span>
          </div>
          <div class="relative w-full">
            <select
              v-model="editingConditionData.deviceId"
              @change="editingConditionData.key = ''"
              class="w-full bg-white border-2 border-slate-300 rounded-lg px-3 py-2.5 text-sm text-black focus:border-red-400 focus:outline-none appearance-none cursor-pointer"
            >
              <option value="" hidden>Select a device</option>
              <option
                v-for="device in props.nodes"
                :key="device.id"
                :value="device.label"
              >
                {{ device.label }}
              </option>
            </select>
          </div>
        </div>

        <!-- Type -->
        <div class="space-y-2" v-if="editingConditionData.deviceId">
          <div class="flex items-center gap-2">
            <svg class="w-5 h-5 text-black" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M7 7h.01M7 3h5c.512 0 1.024.195 1.414.586l7 7a2 2 0 010 2.828l-7 7a2 2 0 01-2.828 0l-7-7A2 2 0 013 12V7a4 4 0 014-4z"/>
            </svg>
            <span class="text-sm font-bold text-black">Type</span>
          </div>
          <div class="relative w-full">
            <select
              v-model="editingConditionData.targetType"
              @change="handleTargetTypeChange"
              class="w-full bg-white border-2 border-slate-300 rounded-lg px-3 py-2.5 text-sm text-black focus:border-red-400 focus:outline-none appearance-none cursor-pointer"
            >
              <option value="" hidden>Type</option>
              <option v-for="type in targetTypes" :key="type.value" :value="type.value">
                {{ type.label }}
              </option>
            </select>
          </div>
        </div>

        <!-- Property -->
        <div class="space-y-2" v-if="editingConditionData.targetType !== 'state' && editingConditionData.deviceId">
          <div class="flex items-center gap-2">
            <svg class="w-5 h-5 text-black" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M15 7a2 2 0 012 2m4 0a6 6 0 01-7.743 5.743L11 17H9v2H7v2H4a1 1 0 01-1-1v-2.586a1 1 0 01.293-.707l5.964-5.964A6 6 0 1121 9z"/>
            </svg>
            <span class="text-sm font-bold text-black">Property</span>
          </div>
          <div class="relative w-full">
            <select
              v-model="editingConditionData.key"
              class="w-full bg-white border-2 border-slate-300 rounded-lg px-3 py-2.5 text-sm text-black focus:border-red-400 focus:outline-none appearance-none cursor-pointer"
            >
              <option value="" hidden>Property</option>
              <option
                v-for="key in availableKeys"
                :key="key.value"
                :value="key.value"
              >
                {{ key.label }}
              </option>
            </select>
          </div>
        </div>

        <!-- Condition Details -->
        <div class="space-y-2" v-if="showRelationAndValue">
          <div class="flex items-center gap-2">
            <svg class="w-5 h-5 text-black" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 6V4m0 2a2 2 0 100 4m0-4a2 2 0 110 4m-6 8a2 2 0 100-4m0 4a2 2 0 110-4m0 4v2m0-6V4m6 6v10m6-2a2 2 0 100-4m0 4a2 2 0 110-4m0 4v2m0-6V4"/>
            </svg>
            <span class="text-sm font-bold text-black">Condition Details</span>
          </div>
          <div class="flex gap-2 w-full">
            <!-- Operator -->
            <div class="relative w-1/4">
              <select
                v-model="editingConditionData.relation"
                class="w-full bg-white border-2 border-slate-300 rounded-lg px-2 py-2.5 text-sm text-center font-bold text-black focus:border-red-400 focus:outline-none appearance-none cursor-pointer"
              >
                <option v-for="op in filteredRelationOperators" :key="op.value" :value="op.value">
                  {{ op.label }}
                </option>
              </select>
            </div>
            <!-- Value -->
            <div class="relative w-3/4">
              <select
                v-if="editingConditionData.targetType === 'state' && ['in', 'not_in'].includes(currentRelation)"
                v-model="editingConditionData.value"
                class="w-full bg-white border-2 border-slate-300 rounded-lg px-3 py-2.5 text-sm text-black focus:border-red-400 focus:outline-none appearance-none cursor-pointer"
              >
                <option value="" hidden>State</option>
                <option v-for="state in availableStates" :key="state" :value="state">
                  {{ state }}
                </option>
              </select>
              <input
                v-else
                v-model="editingConditionData.value"
                class="w-full bg-white border-2 border-slate-300 rounded-lg px-3 py-2.5 text-sm text-black placeholder:text-slate-400 focus:border-red-400 focus:outline-none"
                placeholder="Enter value"
              />
            </div>
          </div>
        </div>

        <!-- Preview -->
        <div class="space-y-2">
          <div class="flex items-center gap-2">
            <svg class="w-5 h-5 text-black" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M15 12a3 3 0 11-6 0 3 3 0 016 0z"/>
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M2.458 12C3.732 7.943 7.523 5 12 5c4.478 0 8.268 2.943 9.542 7-1.274 4.057-5.064 7-9.542 7-4.477 0-8.268-2.943-9.542-7z"/>
            </svg>
            <span class="text-xs font-bold uppercase text-black tracking-wider">Preview</span>
          </div>
          <div class="font-mono text-xs bg-slate-100 rounded-lg px-3 py-2.5 border border-slate-300 text-black break-all w-full">
            <span class="text-red-600 font-bold">{{ getDeviceLabel(editingConditionData.deviceId || 'Device') }}</span>
            <template v-if="editingConditionData.targetType !== 'state' && editingConditionData.key">
              <span class="text-slate-400">.</span>
              <span class="text-red-600 font-bold">{{ editingConditionData.key }}</span>
            </template>
            <template v-if="showRelationAndValue">
              <span class="text-slate-500 mx-1">{{ getRelationLabel(editingConditionData.relation || '=') }}</span>
              <span class="text-black">"{{ editingConditionData.value || 'value' }}"</span>
            </template>
          </div>
        </div>
      </div>

      <!-- Footer Actions -->
      <div class="bg-slate-100 px-6 py-4 flex justify-end gap-3 border-t border-slate-200">
        <button
          @click="showSpecDialog = false"
          class="px-5 py-2.5 text-sm font-bold text-black bg-white border-2 border-slate-300 rounded-lg hover:bg-slate-50 hover:border-slate-400 transition-all"
        >
          Cancel
        </button>
        <button
          @click="saveCondition"
          class="px-5 py-2.5 text-sm font-bold text-black bg-gradient-to-r from-red-500 to-red-600 rounded-lg hover:from-red-600 hover:to-red-700 transition-all shadow-md flex items-center gap-2 disabled:opacity-50 disabled:cursor-not-allowed"
          :disabled="!editingConditionData.deviceId || !editingConditionData.targetType || (editingConditionData.targetType !== 'state' && !editingConditionData.key)"
        >
          <svg class="w-4 h-4" :fill="editingConditionIndex >= 0 ? 'currentColor' : 'none'" stroke="currentColor" viewBox="0 0 24 24">
            <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" :d="editingConditionIndex >= 0 ? 'M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z' : 'M12 4v16m8-8H4'"/>
          </svg>
          {{ editingConditionIndex >= 0 ? 'Update' : 'Add' }}
        </button>
      </div>
    </div>
  </div>

  <!-- Delete Confirmation Dialog -->
  <div v-if="showDeleteConfirmDialog" class="fixed inset-0 bg-slate-900/50 backdrop-blur-sm flex items-center justify-center z-50" @click="showDeleteConfirmDialog = false">
    <div class="bg-white rounded-2xl p-6 w-full max-w-md shadow-2xl border border-slate-200 transform transition-all" @click.stop>
      <!-- 警告头部 -->
      <div class="relative -mx-6 -top-6 mb-6 bg-red-600 rounded-t-2xl p-6 text-center">
        <div class="relative">
          <div class="w-16 h-16 mx-auto bg-white/20 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-white text-3xl">warning</span>
          </div>
          <p class="text-base text-white/90">You are about to delete</p>
        </div>
      </div>

      <div v-if="templateToDelete" class="text-center mb-6">
        <div class="inline-flex items-center gap-3 px-6 py-3 bg-red-50 rounded-xl border-2 border-red-200">
          <span class="material-symbols-outlined text-red-500 text-xl">inventory_2</span>
          <p class="text-lg font-bold text-red-600">{{ templateToDelete.manifest.Name }}</p>
        </div>
        <p class="text-xs text-slate-400 mt-3">This action cannot be undone</p>
      </div>

      <div class="flex justify-center gap-3">
        <button
          @click="showDeleteConfirmDialog = false"
          class="px-6 py-2.5 text-sm font-semibold text-slate-600 bg-white border-2 border-slate-200 rounded-xl hover:bg-slate-50 hover:border-slate-300 transition-all"
        >
          Cancel
        </button>
        <button
          @click="confirmDeleteTemplate"
          class="px-6 py-2.5 text-sm font-semibold text-white bg-red-600 rounded-xl hover:bg-red-500 transition-all shadow-md flex items-center gap-2"
        >
          <span class="material-symbols-outlined text-sm">delete</span>
          Delete Template
        </button>
      </div>
    </div>
  </div>
</template>

<style scoped>
/* Modern panel effect */
.modern-panel {
  background: linear-gradient(180deg, rgba(255, 255, 255, 0.95) 0%, rgba(248, 250, 252, 0.95) 100%);
  backdrop-filter: blur(20px);
  border: 1px solid rgba(255, 255, 255, 0.3);
}

/* Glass panel effect (legacy support) */
.glass-panel {
  background: rgba(255, 255, 255, 0.7);
  backdrop-filter: blur(16px);
  border: 1px solid rgba(226, 232, 240, 0.8);
}

/* Custom scrollbar */
.custom-scrollbar::-webkit-scrollbar {
  width: 6px;
}

.custom-scrollbar::-webkit-scrollbar-track {
  background: rgba(0, 0, 0, 0.02);
  border-radius: 10px;
}

.custom-scrollbar::-webkit-scrollbar-thumb {
  background: #cbd5e1;
  border-radius: 10px;
}

.custom-scrollbar::-webkit-scrollbar-thumb:hover {
  background: #94a3b8;
}

/* Utility classes */
.text-primary {
  color: #8B5CF6;
}

.text-secondary {
  color: #C026D3;
}

.bg-online {
  background-color: #10B981;
}

.bg-offline {
  background-color: #EF4444;
}

/* Material Symbols font */
.material-symbols-outlined {
  font-family: 'Material Symbols Outlined';
  font-variation-settings: 'FILL' 0, 'wght' 400, 'GRAD' 0, 'opsz' 24;
}

/* Details/Summary styling */
details > summary {
  list-style: none;
}

details > summary::-webkit-details-marker {
  display: none;
}

/* Animation utilities */
@keyframes pulse-glow {
  0%, 100% {
    box-shadow: 0 0 0 0 rgba(100, 116, 139, 0.4);
  }
  50% {
    box-shadow: 0 0 0 8px rgba(100, 116, 139, 0);
  }
}

.animate-pulse-glow {
  animation: pulse-glow 2s infinite;
}

/* Text color */
.text-primary {
  color: #334155;
}

.text-secondary {
  color: #475569;
}

/* Input focus animation */
input:focus,
select:focus {
  animation: focus-ring 0.3s ease-out;
}

@keyframes focus-ring {
  0% {
    box-shadow: 0 0 0 0 rgba(100, 116, 139, 0.4);
  }
  100% {
    box-shadow: 0 0 0 4px rgba(100, 116, 139, 0.1);
  }
}

/* Button hover effects */
button:not(:disabled):hover {
  transform: translateY(-1px);
}

button:not(:disabled):active {
  transform: translateY(0);
}

/* Card hover effects */
.group:hover .group-hover\:scale-105 {
  transform: scale(1.05);
}

/* Fade in animation */
@keyframes fadeIn {
  from {
    opacity: 0;
    transform: translateY(10px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

.fade-in {
  animation: fadeIn 0.3s ease-out;
}

/* Backdrop blur support */
@supports (-webkit-backdrop-filter: blur(20px)) {
  .backdrop-blur-sm {
    -webkit-backdrop-filter: blur(20px);
    backdrop-filter: blur(20px);
  }
}
</style>


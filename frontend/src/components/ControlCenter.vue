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
  type: 'Sensor',
  id: 'AUTO'
})

// Device types - hard-coded options plus dynamically loaded custom templates
const deviceTypes = computed(() => {
  const hardCodedTypes = ['Sensor', 'Switch', 'Light']
  const templateNames = props.deviceTemplates.map((tpl: any) => tpl.manifest.Name)
  // Filter out hard-coded types to avoid duplicates, keep only custom templates
  const customTemplates = templateNames.filter(name =>
    !hardCodedTypes.includes(name) && name !== 'Custom'
  )
  return [...hardCodedTypes, ...customTemplates]
})

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
  if (!editingConditionData.key) {
    ElMessage.warning({
      message: 'Please select a property',
      center: true
    })
    return
  }
  
  const device = props.nodes.find(n => n.id === editingConditionData.deviceId)
  const condition: SpecCondition = {
    id: editingConditionData.id || generateConditionId(),
    side: editingConditionSide.value,
    deviceId: editingConditionData.deviceId,
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
const getDeviceLabel = (deviceId: string) => {
  const device = props.nodes.find(n => n.id === deviceId)
  return device?.label || deviceId
}

// Get device template
const getDeviceTemplate = (deviceId: string) => {
  const device = props.nodes.find(n => n.id === deviceId)
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

  if (targetType === 'variable' && template.manifest.InternalVariables) {
    template.manifest.InternalVariables.forEach((v: any) => {
      keys.push({ label: v.Name, value: v.Name })
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
  const manifest = getCachedManifestForNode(editingConditionData.deviceId)
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

  let template

  // If using a predefined type, find existing template
  if (deviceTypes.value.includes(deviceForm.type)) {
    template = props.deviceTemplates.find((tpl: any) => tpl.manifest.Name === deviceForm.type)
    if (!template) {
      // Try to find by lowercase name
      template = props.deviceTemplates.find((tpl: any) =>
        tpl.manifest.Name.toLowerCase() === deviceForm.type.toLowerCase()
      )
    }
    if (!template && props.deviceTemplates.length > 0) {
      // If still not found, use the first available template as fallback
      template = props.deviceTemplates[0]
      console.warn(`Template for type "${deviceForm.type}" not found, using fallback:`, template.manifest.Name)
    }
  } else {
    // If custom type, we should navigate to templates or show error?
    // The "Custom" option in dropdown was triggering this path.
    // But we removed the "Custom Template" form from here.
    // So if user selects "Custom" (which is not in deviceTypes), we should probably warn them to use the Templates tab.
    
    // Actually, "Custom" is filtered out in deviceTypes computed.
    // deviceTypes = hardCoded + customTemplates.filter(!hardCoded)
    // So if user selects "Custom", it's because it's in the list?
    // Wait, in the old code:
    // if (deviceForm.type === 'Custom') -> ...
    // So if user selects "Custom", we should probably just show a message or do nothing.
    // Or better, remove "Custom" from the list if we want to force them to use the new Tab.
    // But for now, let's just warn.
    
    ElMessage({
      message: 'Please use the Templates tab to create custom devices',
      type: 'info',
      center: true
    })
    return
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
    class="absolute left-0 top-0 bottom-0 glass-panel z-40 flex flex-col border-r border-slate-200 transition-all duration-300 ease-in-out"
    :class="isCollapsed ? 'w-12' : 'w-72'"
  >
    <div class="p-3 border-b border-slate-100 bg-white/50 flex items-center justify-center">
      <div v-if="!isCollapsed" class="flex items-center justify-between w-full">
        <h2 class="text-xs font-bold uppercase tracking-[0.2em] text-slate-500">Control Center</h2>
        <button
          @click="togglePanel"
          class="text-slate-400 hover:text-slate-700 transition-colors"
        >
          <span class="material-symbols-outlined text-lg transition-transform duration-200">dock_to_left</span>
        </button>
      </div>
      <div v-else class="flex items-center justify-center p-1">
        <button
          @click="togglePanel"
          class="text-slate-400 hover:text-slate-700 transition-colors p-1 rounded hover:bg-white/20"
        >
          <span class="material-symbols-outlined text-base">dock_to_right</span>
        </button>
      </div>
    </div>

    <!-- Section tabs (only when expanded) -->
    <div v-if="!isCollapsed" class="px-3 py-2 border-b border-slate-100 bg-white/60">
      <div class="grid grid-cols-4 gap-1">
        <button
          @click="activeSection = 'templates'"
          :class="[
            'py-1.5 rounded-md text-[10px] font-bold uppercase tracking-wider transition-colors border',
            activeSection === 'templates'
              ? 'bg-slate-200 text-slate-900 border-slate-300'
              : 'bg-white text-slate-500 border-slate-200 hover:bg-slate-50'
          ]"
        >
          Templates
        </button>
        <button
          @click="activeSection = 'devices'"
          :class="[
            'py-1.5 rounded-md text-[10px] font-bold uppercase tracking-wider transition-colors border',
            activeSection === 'devices'
              ? 'bg-slate-200 text-slate-900 border-slate-300'
              : 'bg-white text-slate-500 border-slate-200 hover:bg-slate-50'
          ]"
        >
          Devices
        </button>
        <button
          @click="activeSection = 'rules'"
          :class="[
            'py-1.5 rounded-md text-[10px] font-bold uppercase tracking-wider transition-colors border',
            activeSection === 'rules'
              ? 'bg-slate-200 text-slate-900 border-slate-300'
              : 'bg-white text-slate-500 border-slate-200 hover:bg-slate-50'
          ]"
        >
          Rules
        </button>
        <button
          @click="activeSection = 'specs'"
          :class="[
            'py-1.5 rounded-md text-[10px] font-bold uppercase tracking-wider transition-colors border',
            activeSection === 'specs'
              ? 'bg-slate-200 text-slate-900 border-slate-300'
              : 'bg-white text-slate-500 border-slate-200 hover:bg-slate-50'
          ]"
        >
          Specs
        </button>
      </div>
    </div>

    <div
      class="flex-1 overflow-y-auto custom-scrollbar bg-white transition-all duration-300 max-h-[calc(100vh-120px)]"
      :class="isCollapsed ? 'opacity-0 pointer-events-none p-0' : 'p-0'"
    >
      <!-- Devices -->
      <details v-if="activeSection === 'devices'" class="group border-b border-slate-100" open>
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-slate-50 transition-colors list-none select-none">
          <div class="flex items-center gap-3">
            <span class="material-symbols-outlined text-lg text-secondary">add_circle</span>
            <span class="text-sm font-semibold text-slate-700">Device Manager</span>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-sm">expand_more</span>
        </summary>

        <div class="px-4 pb-5 space-y-3 bg-slate-50/50 pt-2">
          <!-- Add Device Form -->
          <div class="space-y-3">
            <!-- Device Name -->
            <div>
              <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Device Name</label>
              <input
                v-model="deviceForm.name"
                class="w-full bg-white border border-slate-200 rounded-md px-3 py-2 text-xs text-slate-700 focus:border-secondary focus:ring-secondary/20 placeholder:text-slate-400 transition-all shadow-sm"
                placeholder="e.g. Kitchen Sensor"
                type="text"
              />
            </div>

            <!-- Device Type -->
            <div>
              <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Type</label>
              <select
                v-model="deviceForm.type"
                class="w-full bg-white border border-slate-200 rounded-md px-2 py-2 text-xs text-slate-700 focus:border-secondary focus:ring-secondary/20 shadow-sm"
              >
                <option v-for="type in deviceTypes" :key="type" :value="type">{{ type }}</option>
              </select>
            </div>

            <!-- Action Buttons -->
            <div class="space-y-2">
              <!-- Drop Node Button for predefined types -->
              <button
                @click="createDevice()"
                class="w-full py-2 bg-white hover:bg-secondary/[0.03] text-secondary border border-secondary/20 hover:border-secondary/40 rounded-md text-xs font-bold uppercase tracking-wider transition-all shadow-sm"
              >
                + Drop Node
              </button>
            </div>

          </div>

        </div>
      </details>

      <!-- Templates -->
      <details v-if="activeSection === 'templates'" class="group border-b border-slate-100" open>
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-slate-50 transition-colors list-none select-none">
          <div class="flex items-center gap-3">
            <span class="material-symbols-outlined text-lg text-orange-500">inventory_2</span>
            <span class="text-sm font-semibold text-slate-700">Template Manager</span>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-sm">expand_more</span>
        </summary>

        <div class="px-4 pb-5 bg-slate-50/50 pt-2 space-y-4">
          <!-- Create New Template Button -->
          <div class="border border-orange-200 rounded-lg p-4 bg-orange-50/30 hover:bg-orange-50/50 transition-colors cursor-pointer" @click="goToCreateTemplate">
            <div class="flex items-center justify-between">
              <div class="flex items-center gap-3">
                <div class="w-10 h-10 rounded-full bg-orange-100 flex items-center justify-center text-orange-600">
                  <span class="material-symbols-outlined">add</span>
                </div>
                <div>
                  <div class="text-sm font-semibold text-orange-800">Create New Template</div>
                  <div class="text-xs text-orange-600/70">Design a new device template</div>
                </div>
              </div>
              <span class="material-symbols-outlined text-orange-400">chevron_right</span>
            </div>
          </div>

          <!-- Existing Templates List -->
          <div class="space-y-2">
            <h4 class="text-xs font-bold text-slate-500 uppercase tracking-wide px-1">Existing Templates</h4>
            
            <div v-if="props.deviceTemplates.filter(t => !['Sensor', 'Switch', 'Light'].includes(t.manifest.Name)).length > 0" class="grid grid-cols-1 gap-3">
              <div v-for="template in props.deviceTemplates.filter(t => !['Sensor', 'Switch', 'Light'].includes(t.manifest.Name))" :key="template.id" class="bg-white border border-slate-200 rounded-lg p-3 hover:shadow-md transition-shadow group">
                <div class="flex items-start justify-between mb-3">
                  <div class="flex items-center gap-3">
                    <div class="w-10 h-10 rounded-lg bg-orange-50 flex items-center justify-center text-orange-600 group-hover:bg-orange-100 transition-colors">
                      <span class="material-symbols-outlined">devices</span>
                    </div>
                    <div>
                      <h4 class="text-sm font-bold text-slate-800">{{ template.manifest.Name }}</h4>
                      <p v-if="template.manifest.Description" class="text-xs text-slate-500 mt-0.5 line-clamp-1">{{ template.manifest.Description }}</p>
                    </div>
                  </div>
                  <div class="flex gap-1">
                    <button
                      @click.stop="openDeleteConfirm(template)"
                      class="p-1.5 text-slate-400 hover:text-red-500 hover:bg-red-50 rounded-lg transition-colors"
                      title="Delete Template"
                    >
                      <span class="material-symbols-outlined text-sm">delete</span>
                    </button>
                  </div>
                </div>

                <!-- Stats Grid -->
                <div class="grid grid-cols-4 gap-2 mb-3">
                  <div class="bg-slate-50 rounded px-2 py-1.5 text-center border border-slate-100">
                    <div class="text-[10px] text-slate-400 uppercase font-bold">Vars</div>
                    <div class="text-xs font-bold text-slate-700">{{ template.manifest.InternalVariables?.length || 0 }}</div>
                  </div>
                  <div class="bg-slate-50 rounded px-2 py-1.5 text-center border border-slate-100">
                    <div class="text-[10px] text-slate-400 uppercase font-bold">APIs</div>
                    <div class="text-xs font-bold text-slate-700">{{ template.manifest.APIs?.length || 0 }}</div>
                  </div>
                  <div class="bg-slate-50 rounded px-2 py-1.5 text-center border border-slate-100">
                    <div class="text-[10px] text-slate-400 uppercase font-bold">States</div>
                    <div class="text-xs font-bold text-slate-700">{{ template.manifest.WorkingStates?.length || 0 }}</div>
                  </div>
                  <div class="bg-slate-50 rounded px-2 py-1.5 text-center border border-slate-100">
                    <div class="text-[10px] text-slate-400 uppercase font-bold">Modes</div>
                    <div class="text-xs font-bold text-slate-700">{{ template.manifest.Modes?.length || 0 }}</div>
                  </div>
                </div>

                <!-- Actions -->
                <div class="pt-2 border-t border-slate-100 flex justify-end">
                  <button
                    @click="exportTemplate(template)"
                    class="text-xs px-3 py-1.5 text-slate-500 hover:text-orange-600 hover:bg-orange-50 rounded transition-colors flex items-center gap-1"
                    title="Export Template"
                  >
                    <span class="material-symbols-outlined text-sm">download</span>
                    Export
                  </button>
                </div>
              </div>
            </div>

            <div v-else class="text-center py-8 border border-dashed border-slate-200 rounded-lg bg-slate-50/50">
              <div class="material-symbols-outlined text-slate-300 text-3xl mb-2">inventory_2</div>
              <p class="text-sm text-slate-500 mb-2">No custom templates yet</p>
              <p class="text-xs text-slate-400">Click "Create New Template" to get started.</p>
            </div>
          </div>
        </div>
      </details>

      <!-- Rules -->
      <details v-if="activeSection === 'rules'" class="group border-b border-slate-100" open>
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-slate-50 transition-colors list-none select-none">
          <div class="flex items-center gap-3">
            <span class="material-symbols-outlined text-lg text-primary">function</span>
            <span class="text-sm font-semibold text-slate-700">IFTTT Rule</span>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-sm">expand_more</span>
        </summary>

        <div class="px-4 pb-5 bg-slate-50/50 pt-2 grid grid-cols-1 gap-2">
          <!-- Rule Creation Block -->
          <div
            class="flex items-center gap-2 p-3 rounded bg-white border border-blue-200 cursor-pointer hover:bg-blue-50 transition-colors shadow-sm"
            @click="openRuleBuilder"
          >
            <div class="flex flex-col">
              <span class="text-xs font-bold text-blue-700">Create Rule</span>
              <span class="text-[10px] text-slate-500">IF → THEN logic</span>
            </div>
          </div>
        </div>
      </details>

      <!-- Specs -->
      <details v-if="activeSection === 'specs'" class="group border-b border-slate-100" open>
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-slate-50 transition-colors list-none select-none">
          <div class="flex items-center gap-3">
            <span class="material-symbols-outlined text-lg text-red-500">verified</span>
            <span class="text-sm font-semibold text-slate-700">Specifications</span>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-sm">expand_more</span>
        </summary>

        <div class="px-4 pb-5 bg-slate-50/50 pt-2 space-y-2">
          <!-- Specification Creation -->
          <div class="space-y-4">
            <!-- Step 1: Select Template -->
            <div>
              <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">1. Select Template</label>
              <select
                v-model="specForm.templateId"
                @change="handleTemplateChange"
                class="w-full bg-white border border-slate-200 rounded-lg px-3 py-2.5 text-xs text-slate-700 focus:border-red-400 focus:ring-2 focus:ring-red-100 transition-all"
              >
                <option value="" disabled hidden>Select a specification template</option>
                <option
                  v-for="template in specTemplateDetails"
                  :key="template.id"
                  :value="template.id"
                >
                  {{ template.label }}
                </option>
              </select>
              <p v-if="currentTemplateDetail" class="text-xs text-slate-500 mt-1.5 px-1">
                {{ currentTemplateDetail.description }}
              </p>
            </div>

            <!-- Step 2: Add Conditions based on template requirements -->
            <div v-if="specForm.templateId" class="space-y-2">
              <label class="block text-[10px] uppercase font-bold text-slate-500">2. Configure Conditions</label>

              <!-- A Conditions (Always/Forall) -->
              <div v-if="isSideRequired('a')" class="border border-red-200 rounded-lg p-2 bg-red-50/50">
                <div class="flex items-center justify-between mb-2">
                  <span class="text-xs font-bold text-red-600 uppercase tracking-wide">A Conditions</span>
                  <button
                    @click="openConditionDialog('a')"
                    class="text-xs px-2 py-0.5 bg-red-500 text-white rounded hover:bg-red-600 transition-colors"
                  >
                    + Add
                  </button>
                </div>
                <div class="space-y-1 max-h-28 overflow-y-auto">
                  <div
                    v-for="(condition, index) in specForm.aConditions"
                    :key="condition.id"
                    class="flex items-center justify-between bg-white rounded px-2 py-1 border border-red-100"
                  >
                    <div class="flex items-center gap-1.5 overflow-hidden">
                      <span class="text-xs text-slate-700 font-medium truncate">
                        {{ getDeviceLabel(condition.deviceId) }}
                      </span>
                      <span class="text-slate-300">·</span>
                      <span class="text-xs text-red-600 truncate">
                        {{ condition.key }}
                      </span>
                      <span class="text-xs text-slate-400">{{ getRelationLabel(condition.relation || '=') }}</span>
                      <span class="text-xs bg-slate-100 text-slate-600 px-1.5 py-0.5 rounded truncate max-w-[50px]">
                        {{ condition.value || '*' }}
                      </span>
                    </div>
                    <div class="flex gap-0.5 ml-1">
                      <button @click="openConditionDialog('a', index)" class="p-0.5 text-slate-400 hover:text-slate-600 hover:bg-slate-100 rounded">
                        <span class="material-symbols-outlined text-xs">edit</span>
                      </button>
                      <button @click="removeCondition('a', index)" class="p-0.5 text-slate-400 hover:text-red-500 hover:bg-red-50 rounded">
                        <span class="material-symbols-outlined text-xs">close</span>
                      </button>
                    </div>
                  </div>
                  <div v-if="specForm.aConditions.length === 0" class="text-[10px] text-slate-400 italic text-center py-1">
                    No conditions
                  </div>
                </div>
              </div>

              <!-- IF Conditions (Antecedent) -->
              <div v-if="isSideRequired('if')" class="border border-orange-200 rounded-lg p-2 bg-orange-50/50">
                <div class="flex items-center justify-between mb-2">
                  <span class="text-xs font-bold text-orange-600 uppercase tracking-wide">A Conditions</span>
                  <button
                    @click="openConditionDialog('if')"
                    class="text-xs px-2 py-0.5 bg-orange-500 text-white rounded hover:bg-orange-600 transition-colors"
                  >
                    + Add
                  </button>
                </div>
                <div class="space-y-1 max-h-28 overflow-y-auto">
                  <div
                    v-for="(condition, index) in specForm.ifConditions"
                    :key="condition.id"
                    class="flex items-center justify-between bg-white rounded px-2 py-1 border border-orange-100"
                  >
                    <div class="flex items-center gap-1.5 overflow-hidden">
                      <span class="text-xs text-slate-700 font-medium truncate">
                        {{ getDeviceLabel(condition.deviceId) }}
                      </span>
                      <span class="text-slate-300">·</span>
                      <span class="text-xs text-orange-600 truncate">
                        {{ condition.key }}
                      </span>
                      <span class="text-xs text-slate-400">{{ getRelationLabel(condition.relation || '=') }}</span>
                      <span class="text-xs bg-slate-100 text-slate-600 px-1.5 py-0.5 rounded truncate max-w-[50px]">
                        {{ condition.value || '*' }}
                      </span>
                    </div>
                    <div class="flex gap-0.5 ml-1">
                      <button @click="openConditionDialog('if', index)" class="p-0.5 text-slate-400 hover:text-slate-600 hover:bg-slate-100 rounded">
                        <span class="material-symbols-outlined text-xs">edit</span>
                      </button>
                      <button @click="removeCondition('if', index)" class="p-0.5 text-slate-400 hover:text-red-500 hover:bg-red-50 rounded">
                        <span class="material-symbols-outlined text-xs">close</span>
                      </button>
                    </div>
                  </div>
                  <div v-if="specForm.ifConditions.length === 0" class="text-[10px] text-slate-400 italic text-center py-1">
                    No conditions
                  </div>
                </div>
              </div>

              <!-- THEN Conditions (Consequent) -->
              <div v-if="isSideRequired('then')" class="border border-rose-200 rounded-lg p-2 bg-rose-50/50">
                <div class="flex items-center justify-between mb-2">
                  <span class="text-xs font-bold text-rose-600 uppercase tracking-wide">B Conditions</span>
                  <button
                    @click="openConditionDialog('then')"
                    class="text-xs px-2 py-0.5 bg-rose-500 text-white rounded hover:bg-rose-600 transition-colors"
                  >
                    + Add
                  </button>
                </div>
                <div class="space-y-1 max-h-28 overflow-y-auto">
                  <div
                    v-for="(condition, index) in specForm.thenConditions"
                    :key="condition.id"
                    class="flex items-center justify-between bg-white rounded px-2 py-1 border border-rose-100"
                  >
                    <div class="flex items-center gap-1.5 overflow-hidden">
                      <text class="text-xs text-slate-700 font-medium truncate">
                        {{ getDeviceLabel(condition.deviceId) }}
                      </text>
                      <span class="text-slate-300">·</span>
                      <span class="text-xs text-rose-600 truncate">
                        {{ condition.key }}
                      </span>
                      <span class="text-xs text-slate-400">{{ getRelationLabel(condition.relation || '=') }}</span>
                      <span class="text-xs bg-slate-100 text-slate-600 px-1.5 py-0.5 rounded truncate max-w-[50px]">
                        {{ condition.value || '*' }}
                      </span>
                    </div>
                    <div class="flex gap-0.5 ml-1">
                      <button @click="openConditionDialog('then', index)" class="p-0.5 text-slate-400 hover:text-slate-600 hover:bg-slate-100 rounded">
                        <span class="material-symbols-outlined text-xs">edit</span>
                      </button>
                      <button @click="removeCondition('then', index)" class="p-0.5 text-slate-400 hover:text-red-500 hover:bg-red-50 rounded">
                        <span class="material-symbols-outlined text-xs">close</span>
                      </button>
                    </div>
                  </div>
                  <div v-if="specForm.thenConditions.length === 0" class="text-[10px] text-slate-400 italic text-center py-1">
                    No conditions
                  </div>
                </div>
              </div>
            </div>

            <!-- Step 3: Generated Rule Description -->
            <div v-if="specForm.templateId" class="bg-red-50 rounded-lg p-3 border border-red-100">
              <div class="flex items-center gap-2 mb-1">
                <span class="material-symbols-outlined text-red-400 text-sm">translate</span>
                <span class="text-[10px] uppercase font-bold text-red-600">Rule Description</span>
              </div>
              <div class="text-xs text-slate-700 leading-relaxed pl-7">
                {{ naturalLanguageRule }}
              </div>
              <div class="mt-2 pt-2 border-t border-red-200 flex items-center gap-2">
                <span class="text-[10px] uppercase font-bold text-slate-400">LTL:</span>
                <code class="text-xs bg-white text-slate-600 px-2 py-0.5 rounded border border-slate-200 font-mono">
                  {{ specForm.formula }}
                </code>
              </div>
            </div>

            <!-- Create Button -->
            <button
              @click="createSpecification"
              :disabled="!specForm.templateId"
              class="w-full py-2 bg-red-500 hover:bg-red-600 disabled:bg-slate-300 text-white rounded-lg text-xs font-bold uppercase tracking-wider transition-all"
            >
              Create Specification
            </button>
          </div>
        </div>
      </details>
    </div>

  </aside>

  <!-- Specification Condition Dialog -->
  <div v-if="showSpecDialog" class="fixed inset-0 bg-black/40 backdrop-blur-sm flex items-center justify-center z-50" @click="showSpecDialog = false">
    <div class="bg-white rounded-xl p-5 w-full max-w-sm shadow-xl" @click.stop>
      <div class="flex justify-between items-center mb-4">
        <h3 class="text-base font-semibold text-slate-800">
          {{ editingConditionIndex >= 0 ? 'Edit' : 'Add' }} Condition
        </h3>
        <button @click="showSpecDialog = false" class="p-1.5 text-slate-400 hover:text-red-500 hover:bg-red-50 rounded-lg transition-colors">
          <span class="material-symbols-outlined text-sm">close</span>
        </button>
      </div>

      <div class="space-y-3">
        <!-- Device Selection -->
        <div>
          <label class="block text-xs font-medium text-slate-600 mb-1">Device</label>
          <select
            v-model="editingConditionData.deviceId"
            @change="editingConditionData.key = ''"
            class="w-full px-3 py-2 border border-slate-200 rounded-lg focus:ring-2 focus:ring-red-100 focus:border-red-400 transition-all text-sm"
          >
            <option value="" hidden>Select device</option>
            <option
              v-for="device in props.nodes"
              :key="device.id"
              :value="device.id"
            >
              {{ device.label }}
            </option>
          </select>
        </div>

        <!-- Target Type & Property Key in one row -->
        <div class="grid grid-cols-2 gap-2">
          <div>
            <label class="block text-xs font-medium text-slate-600 mb-1">Type</label>
            <select
              v-model="editingConditionData.targetType"
              @change="handleTargetTypeChange"
              class="w-full px-2 py-2 border border-slate-200 rounded-lg focus:ring-2 focus:ring-red-100 focus:border-red-400 transition-all text-sm"
              :disabled="!editingConditionData.deviceId"
            >
              <option value="" hidden>Select type</option>
              <option v-for="type in targetTypes" :key="type.value" :value="type.value">
                {{ type.label }}
              </option>
            </select>
          </div>
          <!-- Property: Only show for Variable or API types -->
          <div v-if="editingConditionData.targetType !== 'state'">
            <label class="block text-xs font-medium text-slate-600 mb-1">Property</label>
            <select
              v-model="editingConditionData.key"
              class="w-full px-2 py-2 border border-slate-200 rounded-lg focus:ring-2 focus:ring-red-100 focus:border-red-400 transition-all text-sm"
              :disabled="!editingConditionData.deviceId || !editingConditionData.targetType"
            >
              <option value="" hidden>Select property</option>
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

        <!-- Relation and Value (hidden for API type) -->
        <div v-if="showRelationAndValue" class="grid grid-cols-3 gap-2">
          <div class="col-span-1">
            <label class="block text-xs font-medium text-slate-600 mb-1">Relation</label>
            <select
              v-model="editingConditionData.relation"
              class="w-full px-2 py-2 border border-slate-200 rounded-lg focus:ring-2 focus:ring-red-100 focus:border-red-400 transition-all text-sm text-center"
            >
              <option v-for="op in filteredRelationOperators" :key="op.value" :value="op.value">
                {{ op.label }}
              </option>
            </select>
          </div>
          <div class="col-span-2">
            <label class="block text-xs font-medium text-slate-600 mb-1">Value</label>
            <select
              v-if="editingConditionData.targetType === 'state' && ['in', 'not_in'].includes(currentRelation)"
              v-model="editingConditionData.value"
              class="w-full px-3 py-2 border border-slate-200 rounded-lg focus:ring-2 focus:ring-red-100 focus:border-red-400 transition-all text-sm bg-white"
            >
              <option value="" hidden>Select State</option>
              <option v-for="state in availableStates" :key="state" :value="state">
                {{ state }}
              </option>
            </select>
            <input
              v-else
              v-model="editingConditionData.value"
              class="w-full px-3 py-2 border border-slate-200 rounded-lg focus:ring-2 focus:ring-red-100 focus:border-red-400 transition-all text-sm"
              placeholder="Value"
            />
          </div>
        </div>

        <!-- Preview -->
        <div class="bg-slate-50 rounded-lg p-2 border border-slate-200">
          <div class="text-[10px] uppercase font-bold text-slate-400 mb-1">Preview</div>
          <div class="font-mono text-xs text-slate-700 break-all">
            <span class="text-red-600">{{ getDeviceLabel(editingConditionData.deviceId || '-') }}</span>
            <!-- Only show .key for Variable and API types -->
            <template v-if="editingConditionData.targetType !== 'state'">
              <span class="text-slate-400">.</span>
              <span class="text-orange-600">{{ editingConditionData.key || '-' }}</span>
            </template>
            <template v-if="showRelationAndValue">
              <span class="text-slate-500 mx-1">{{ getRelationLabel(editingConditionData.relation || '=') }}</span>
              <span class="text-red-600">"{{ editingConditionData.value || '-' }}"</span>
            </template>
          </div>
        </div>
      </div>

      <div class="flex justify-end gap-2 mt-4">
        <button
          @click="showSpecDialog = false"
          class="px-4 py-1.5 text-xs font-medium text-slate-600 bg-slate-100 border border-slate-200 rounded-lg hover:bg-slate-200"
        >
          Cancel
        </button>
        <button
          @click="saveCondition"
          class="px-4 py-1.5 text-xs font-medium text-white bg-red-500 rounded-lg hover:bg-red-600 transition-colors"
        >
          {{ editingConditionIndex >= 0 ? 'Update' : 'Add' }}
        </button>
      </div>
    </div>
  </div>

  <!-- Delete Confirmation Dialog -->
  <div v-if="showDeleteConfirmDialog" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="showDeleteConfirmDialog = false">
    <div class="bg-white rounded-lg p-6 w-80 max-w-[90vw]" @click.stop>
      <div v-if="templateToDelete" class="text-center">
        <div class="mb-4">
          <p class="text-base text-slate-700 mb-2">You are about to delete:</p>
          <p class="text-xl font-bold text-red-600">{{ templateToDelete.manifest.Name }}</p>
        </div>
      </div>

      <div class="flex justify-end space-x-3">
        <button
          @click="showDeleteConfirmDialog = false"
          class="px-4 py-2 text-sm font-medium text-slate-700 bg-white border border-slate-300 rounded-md hover:bg-slate-50 transition-colors"
        >
          Cancel
        </button>
        <button
          @click="confirmDeleteTemplate"
          class="px-4 py-2 text-sm font-medium text-white bg-red-600 border border-transparent rounded-md hover:bg-red-700 transition-colors"
        >
          Delete Template
        </button>
      </div>
    </div>
    </div>
</template>

<style scoped>
/* Glass panel effect */
.glass-panel {
  background: rgba(255, 255, 255, 0.7);
  backdrop-filter: blur(16px);
  border: 1px solid rgba(226, 232, 240, 0.8);
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

.text-secondary {
  color: #C026D3;
}

.bg-online {
  background-color: #059669;
}

.bg-offline {
  background-color: #dc2626;
}

/* Material Symbols font */
.material-symbols-outlined {
  font-family: 'Material Symbols Outlined';
}
</style>

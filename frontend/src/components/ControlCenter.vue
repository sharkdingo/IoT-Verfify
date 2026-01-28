<script setup lang="ts">
import { ref, reactive, computed } from 'vue'
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

// Custom template form data
const customTemplateForm = reactive({
  name: '',
  description: '',
  initState: '',
  modes: [] as Array<string>,
  apis: [] as Array<{
    id: string,
    name: string,
    description: string,
    signal: boolean,
    startState: string,
    endState: string,
    trigger: string,
    assignments: Array<{variableName: string, changeRate: string}>
  }>,
  variables: [] as Array<{
    name: string,
    description: string,
    isInside: boolean,
    publicVisible: boolean,
    trust: string,
    privacy: string,
    lowerBound: number,
    upperBound: number,
    values: string[]
  }>,
  impactedVariables: [] as Array<string>,
  workingStates: [] as Array<{
    name: string,
    description: string,
    trust: string,
    privacy: string,
    invariant: string
  }>
})

// Template creation mode
const isCreatingCustomTemplate = ref(false)

// JSON upload functionality
const fileInput = ref<HTMLInputElement>()

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

// Dialog states
const showVariableDialog = ref(false)
const showWorkingStateDialog = ref(false)
const showApiDialog = ref(false)
const showDeleteConfirmDialog = ref(false)
const editingVariableIndex = ref(-1)
const editingWorkingStateIndex = ref(-1)
const editingApiIndex = ref(-1)
const templateToDelete = ref<any>(null)

// Dialog data
const editingVariableData = reactive({
  name: '',
  description: '',
  isInside: true,
  publicVisible: true,
  trust: 'high',
  privacy: 'low',
  lowerBound: 0,
  upperBound: 100,
  values: []
})

const editingWorkingStateData = reactive({
  name: '',
  description: '',
  trust: 'high',
  privacy: 'low',
  invariant: 'true'
})

const editingApiData = reactive({
  name: '',
  description: '',
  signal: false,
  startState: '',
  endState: '',
  trigger: 'user',
  assignments: [] as Array<{variableName: string, changeRate: string}>
})

// (removed unused `jsonExample`; UI provides direct JSON upload)

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

// Check if relation and value fields should be shown (hidden for API type)
const showRelationAndValue = computed(() => {
  return editingConditionData.targetType !== 'api'
})

// (removed unused helpers getKeyLabel/getTargetTypeLabel)

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
      const relationText = getRelationLabel(c.relation)
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

// (removed unused helper getConditionsCount)



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
    // If custom type, create a new template first
    template = await createCustomTemplate()
    if (!template) {
      return // Template creation failed
    }
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

const switchToCustomTemplate = () => {
  if (!deviceForm.name.trim()) {
    ElMessage({
      message: 'Enter device name first',
      type: 'warning',
      center: true
    })
    return
  }

  // Pre-fill the custom template form with device name
  customTemplateForm.name = deviceForm.name
  customTemplateForm.description = `${deviceForm.name} device`

  // Switch to custom template mode
  isCreatingCustomTemplate.value = true

  ElMessage({
    message: 'Switched to template mode',
    type: 'info',
    center: true
  })
}



const addApiToTemplate = () => {
  editingApiIndex.value = -1
  Object.assign(editingApiData, {
    name: '',
    description: '',
    signal: false,
    startState: customTemplateForm.initState || '',
    endState: customTemplateForm.initState || '',
    trigger: 'user',
    assignments: []
  })
  showApiDialog.value = true
}

const saveApi = (apiData: any) => {
  if (editingApiIndex.value >= 0) {
    customTemplateForm.apis[editingApiIndex.value] = { ...apiData, id: customTemplateForm.apis[editingApiIndex.value].id }
  } else {
    customTemplateForm.apis.push({ ...apiData, id: `api-${Date.now()}` })
  }
  showApiDialog.value = false
}

const editApi = (index: number) => {
  editingApiIndex.value = index
  const api = customTemplateForm.apis[index]
  Object.assign(editingApiData, api)
  showApiDialog.value = true
}

const confirmSaveApi = () => {
  if (!editingApiData.name.trim()) {
    ElMessage({
      message: 'Enter API name',
      type: 'warning',
      center: true
    })
    return
  }
  saveApi({ ...editingApiData })
}

const removeApiFromTemplate = (index: number) => {
  customTemplateForm.apis.splice(index, 1)
}

const addVariableToTemplate = () => {
  editingVariableIndex.value = -1
  // Reset to default values
  Object.assign(editingVariableData, {
    name: '',
    description: '',
    isInside: true,
    publicVisible: true,
    trust: 'high',
    privacy: 'low',
    lowerBound: 0,
    upperBound: 100,
    values: []
  })
  showVariableDialog.value = true
}

const saveVariable = (variableData: any) => {
  if (editingVariableIndex.value >= 0) {
    // Edit existing variable
    customTemplateForm.variables[editingVariableIndex.value] = variableData
  } else {
    // Add new variable
    customTemplateForm.variables.push(variableData)
  }
  showVariableDialog.value = false
}

const editVariable = (index: number) => {
  editingVariableIndex.value = index
  // Load existing data
  const variable = customTemplateForm.variables[index]
  Object.assign(editingVariableData, variable)
  showVariableDialog.value = true
}

const confirmSaveVariable = () => {
  if (!editingVariableData.name.trim()) {
    ElMessage({
      message: 'Enter variable name',
      type: 'warning',
      center: true
    })
    return
  }
  saveVariable({ ...editingVariableData })
}

const removeVariableFromTemplate = (index: number) => {
  const variableName = customTemplateForm.variables[index].name
  customTemplateForm.variables.splice(index, 1)

  // Also remove from impacted variables if it was selected
  const impactedIndex = customTemplateForm.impactedVariables.indexOf(variableName)
  if (impactedIndex > -1) {
    customTemplateForm.impactedVariables.splice(impactedIndex, 1)
  }
}

const toggleImpactedVariable = (variableName: string) => {
  if (!variableName.trim()) return // Don't allow empty variable names

  const index = customTemplateForm.impactedVariables.indexOf(variableName)
  if (index > -1) {
    customTemplateForm.impactedVariables.splice(index, 1)
  } else {
    customTemplateForm.impactedVariables.push(variableName)
  }
}

const addWorkingStateToTemplate = () => {
  editingWorkingStateIndex.value = -1
  // Reset to default values
  Object.assign(editingWorkingStateData, {
    name: '',
    description: '',
    trust: 'high',
    privacy: 'low',
    invariant: 'true'
  })
  showWorkingStateDialog.value = true
}

const saveWorkingState = (stateData: any) => {
  if (editingWorkingStateIndex.value >= 0) {
    // Edit existing state
    customTemplateForm.workingStates[editingWorkingStateIndex.value] = stateData
  } else {
    // Add new state
    customTemplateForm.workingStates.push(stateData)
  }
  showWorkingStateDialog.value = false
}

const editWorkingState = (index: number) => {
  editingWorkingStateIndex.value = index
  // Load existing data
  const state = customTemplateForm.workingStates[index]
  Object.assign(editingWorkingStateData, state)
  showWorkingStateDialog.value = true
}

const confirmSaveWorkingState = () => {
  if (!editingWorkingStateData.name.trim()) {
    ElMessage({
      message: 'Enter state name',
      type: 'warning',
      center: true
    })
    return
  }
  saveWorkingState({ ...editingWorkingStateData })
}

const removeWorkingStateFromTemplate = (index: number) => {
  customTemplateForm.workingStates.splice(index, 1)
}

const addModeToTemplate = () => {
  customTemplateForm.modes.push('')
}

const removeModeFromTemplate = (index: number) => {
  customTemplateForm.modes.splice(index, 1)
}

// JSON file upload handling
const handleJsonFileUpload = (event: Event) => {
  const file = (event.target as HTMLInputElement).files?.[0]
  if (!file) return

  if (file.type !== 'application/json' && !file.name.endsWith('.json')) {
      ElMessage({
        message: 'Invalid file format',
        type: 'error',
        center: true
      })
    return
  }

  const reader = new FileReader()
  reader.onload = (e) => {
    try {
      const jsonData = JSON.parse(e.target?.result as string)
      console.log('Parsed JSON data:', jsonData)

      // Validate JSON structure
      if (!jsonData.Name || !jsonData.Description) {
        ElMessage({
          message: 'Missing required fields in JSON',
          type: 'error',
          center: true
        })
        return
      }

      // Directly create template from JSON data
      createTemplateFromJson(jsonData)
    } catch (error) {
      ElMessage({
        message: 'Invalid JSON format',
        type: 'error',
        center: true
      })
      console.error('JSON parse error:', error)
    }
  }
  reader.readAsText(file)
}



const createCustomTemplate = async () => {
  if (!customTemplateForm.name.trim()) {
    ElMessage({
      message: 'Enter template name',
      type: 'warning',
      center: true
    })
    return
  }

  try {
    // Create manifest object
    const manifest = {
      Name: customTemplateForm.name,
      Description: customTemplateForm.description || `${customTemplateForm.name} device`,
      Modes: customTemplateForm.modes.filter(m => m.trim() !== ''),
      InternalVariables: customTemplateForm.variables
        .filter(v => v.name.trim() !== '')
        .map(v => ({
          Name: v.name,
          Description: v.description,
          IsInside: v.isInside,
          PublicVisible: v.publicVisible,
          Trust: v.trust,
          Privacy: v.privacy,
          LowerBound: v.lowerBound,
          UpperBound: v.upperBound,
          Values: v.values.filter(val => val.trim() !== '')
        })),
      ImpactedVariables: customTemplateForm.impactedVariables.filter(v => v.trim() !== ''),
      InitState: customTemplateForm.initState,
      WorkingStates: customTemplateForm.workingStates
        .filter(s => s.name.trim() !== '')
        .map(s => ({
          Name: s.name,
          Description: s.description,
          Trust: s.trust,
          Privacy: s.privacy,
          Invariant: s.invariant,
          Dynamics: []
        })),
      Transitions: [],
      APIs: customTemplateForm.apis
        .filter(api => api.name.trim() !== '')
        .map(api => ({
          Name: api.name,
          Description: api.description,
          Signal: api.signal,
          StartState: api.startState,
          EndState: api.endState,
          Trigger: api.trigger,
          Assignments: api.assignments.filter(a => a.variableName.trim() !== '').map(a => ({
            VariableName: a.variableName,
            ChangeRate: a.changeRate
          }))
        }))
    }

    // Call API to create template
    console.log('Creating custom template:', { name: customTemplateForm.name, manifest })

    const token = localStorage.getItem('iot_verify_token')
    console.log('Token exists:', !!token)
    console.log('Token value:', token ? token.substring(0, 20) + '...' : 'null')

    if (!token) {
      ElMessage({
      message: 'Please login first',
      type: 'error',
      center: true
    })
      return
    }

    const response = await fetch('/api/board/templates', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Authorization': `Bearer ${token}`
      },
      body: JSON.stringify({
        name: customTemplateForm.name,
        manifest
      })
    })

    console.log('API response status:', response.status)
    console.log('API response ok:', response.ok)

    if (!response.ok) {
      const errorMessage = await handleApiError(response, 'Create custom template')
      throw new Error(errorMessage)
    }

    const newTemplate = await response.json()

    ElMessage({
      message: 'Template created',
      type: 'success',
      center: true
    })

    // Reset form
    customTemplateForm.name = ''
    customTemplateForm.description = ''
    customTemplateForm.initState = ''
    customTemplateForm.modes = []
    customTemplateForm.apis = []
    customTemplateForm.variables = []
    customTemplateForm.impactedVariables = []
    customTemplateForm.workingStates = []

    // Switch back to device creation mode
    isCreatingCustomTemplate.value = false

    // Emit event to refresh templates
    emit('refresh-templates')

    return newTemplate.data
  } catch (error) {
    console.error('Failed to create custom template:', error)
    const errorMessage = error instanceof Error ? error.message : 'Unknown error occurred'
    ElMessage({
      message: `Create failed: ${errorMessage}`,
      type: 'error',
      center: true
    })
    return null
  }
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


const createTemplateFromJson = async (jsonData: any) => {
  try {
    console.log('Creating template from JSON:', jsonData)

    // Build manifest from JSON data
    const manifest = {
      Name: jsonData.Name,
      Description: jsonData.Description,
      Modes: jsonData.Modes || [],
      InternalVariables: (jsonData.InternalVariables || jsonData.variables || []).map((v: any) => ({
        Name: v.Name || v.name || '',
        Description: v.Description || v.description || '',
        IsInside: v.IsInside !== undefined ? v.IsInside : (v.isInside !== undefined ? v.isInside : true),
        PublicVisible: v.PublicVisible !== undefined ? v.PublicVisible : (v.publicVisible !== undefined ? v.publicVisible : true),
        Trust: v.Trust || v.trust || 'high',
        Privacy: v.Privacy || v.privacy || 'low',
        LowerBound: v.LowerBound !== undefined ? v.LowerBound : (v.lowerBound !== undefined ? v.lowerBound : 0),
        UpperBound: v.UpperBound !== undefined ? v.UpperBound : (v.upperBound !== undefined ? v.upperBound : 100),
        Values: v.Values || v.values || [],
        NaturalChangeRate: v.NaturalChangeRate || v.naturalChangeRate
      })),
      ImpactedVariables: jsonData.ImpactedVariables || jsonData.impactedVariables || [],
      InitState: jsonData.InitState || jsonData.initState || '',
      WorkingStates: (jsonData.WorkingStates || jsonData.workingStates || []).map((s: any) => ({
        Name: s.Name || s.name || '',
        Description: s.Description || s.description || '',
        Trust: s.Trust || s.trust || 'high',
        Privacy: s.Privacy || s.privacy || 'low',
        Invariant: s.Invariant || s.invariant || 'true',
        Dynamics: s.Dynamics || s.dynamics || []
      })),
      Transitions: jsonData.Transitions || jsonData.transitions || [],
      APIs: (jsonData.APIs || jsonData.apis || []).map((api: any) => ({
        Name: api.Name || api.name || '',
        Description: api.Description || api.description || '',
        Signal: api.Signal !== undefined ? api.Signal : (api.signal !== undefined ? api.signal : false),
        StartState: api.StartState || api.startState || jsonData.InitState || jsonData.initState || '',
        EndState: api.EndState || api.endState || jsonData.InitState || jsonData.initState || '',
        Trigger: api.Trigger || api.trigger || 'user',
        Assignments: api.Assignments || api.assignments || []
      }))
    }

    console.log('Built manifest:', manifest)

    // Send to backend
    const token = localStorage.getItem('iot_verify_token')
    if (!token) {
      ElMessage({
      message: 'Please login first',
      type: 'error',
      center: true
    })
      return
    }

    const response = await fetch('/api/board/templates', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Authorization': `Bearer ${token}`
      },
      body: JSON.stringify({
        name: jsonData.Name,
        manifest: manifest
      })
    })

    if (!response.ok) {
      const errorMessage = await handleApiError(response, 'Create template from JSON')
      throw new Error(errorMessage)
    }

    const result = await response.json()
    console.log('Template created successfully:', result)

    ElMessage({
      message: `Template "${jsonData.Name}" created`,
      type: 'success',
      center: true,
      duration: 2000
    })
    emit('refresh-templates')

    // Switch to Add Device mode
    isCreatingCustomTemplate.value = false

    // Clear file input
    if (fileInput.value) {
      fileInput.value.value = ''
    }

  } catch (error) {
    console.error('Failed to create template from JSON:', error)
    const errorMessage = error instanceof Error ? error.message : 'Unknown error'
    ElMessage({
      message: errorMessage,
      type: 'error',
      center: true,
      duration: 4000
    })
  }
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

// (removed unused spec device helper functions; spec creation uses condition dialog + template-based keys)

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
          <!-- Mode Toggle -->
          <div class="flex gap-2">
            <button
              @click="isCreatingCustomTemplate = false"
              :class="[
                'flex-1 py-1.5 px-2 rounded text-xs font-medium transition-all',
                !isCreatingCustomTemplate
                  ? 'bg-slate-200 text-slate-900 border border-slate-300'
                  : 'bg-white text-secondary border border-secondary/20'
              ]"
            >
              Add Device
            </button>
            <button
              @click="isCreatingCustomTemplate = true"
              :class="[
                'flex-1 py-1.5 px-2 rounded text-xs font-medium transition-all',
                isCreatingCustomTemplate
                  ? 'bg-slate-200 text-slate-900 border border-slate-300'
                  : 'bg-white text-secondary border border-secondary/20'
              ]"
            >
              Custom Template
            </button>
          </div>

          <!-- Add Device Form -->
          <div v-if="!isCreatingCustomTemplate" class="space-y-3">
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
                v-if="deviceForm.type !== 'Custom'"
                @click="createDevice()"
                class="w-full py-2 bg-white hover:bg-secondary/[0.03] text-secondary border border-secondary/20 hover:border-secondary/40 rounded-md text-xs font-bold uppercase tracking-wider transition-all shadow-sm"
              >
                + Drop Node
              </button>

              <!-- Custom Device Options -->
              <div v-if="deviceForm.type === 'Custom'" class="space-y-2">
                <button
                  @click="switchToCustomTemplate()"
                  class="w-full py-2 bg-slate-200 hover:bg-slate-300 text-slate-900 border border-slate-300 rounded-md text-xs font-bold uppercase tracking-wider transition-all shadow-sm"
                  :disabled="!deviceForm.name.trim()"
                >
                  + Create Custom Template
                </button>
              </div>
            </div>

          </div>

          <!-- Custom Template Form -->
          <div v-if="isCreatingCustomTemplate" class="space-y-4">
            <!-- JSON Import -->
            <div class="border border-slate-200 rounded-lg p-4 hover:border-secondary/40 transition-colors cursor-pointer" @click="fileInput?.click()">
              <input
                ref="fileInput"
                type="file"
                accept=".json"
                @change="handleJsonFileUpload"
                class="hidden"
              />
              <div class="text-center">
                <div class="material-symbols-outlined text-secondary text-2xl mb-2">upload_file</div>
                <div class="text-sm font-medium text-slate-600 mb-1">Import JSON Template</div>
                <div class="text-xs text-slate-500">Upload a JSON file to create template</div>
              </div>
            </div>

            <!-- Basic Info -->
            <div class="space-y-3">
              <input
                v-model="customTemplateForm.name"
                class="w-full bg-white border border-slate-200 rounded-md px-3 py-2 text-xs text-slate-700 focus:border-secondary focus:ring-secondary/20 placeholder:text-slate-400 transition-all shadow-sm"
                placeholder="Template name"
              />
              <input
                v-model="customTemplateForm.description"
                class="w-full bg-white border border-slate-200 rounded-md px-3 py-2 text-xs text-slate-700 focus:border-secondary focus:ring-secondary/20 placeholder:text-slate-400 transition-all shadow-sm"
                placeholder="Description (optional)"
              />
              <input
                v-model="customTemplateForm.initState"
                class="w-full bg-white border border-slate-200 rounded-md px-3 py-2 text-xs text-slate-700 focus:border-secondary focus:ring-secondary/20 placeholder:text-slate-400 transition-all shadow-sm"
                placeholder="Initial state"
              />
            </div>

            <!-- Compact Sections -->
            <div class="grid grid-cols-1 gap-3">
              <!-- Modes -->
              <div class="border border-slate-100 rounded-lg p-3 bg-slate-50/30">
                <div class="flex items-center justify-between mb-2">
                  <span class="text-xs font-semibold text-slate-600 uppercase tracking-wide">Modes</span>
                  <button @click="addModeToTemplate" class="text-secondary text-xs font-medium hover:text-secondary/80">
                    + Add
                  </button>
                </div>
                <div class="space-y-1.5 max-h-20 overflow-y-auto">
                  <div v-for="(_, index) in customTemplateForm.modes" :key="`mode-${index}`" class="flex items-center gap-2">
                    <input
                      v-model="customTemplateForm.modes[index]"
                      class="flex-1 bg-white border border-slate-200 rounded px-2 py-1 text-xs focus:border-secondary"
                      placeholder="Mode name"
                    />
                    <button @click="removeModeFromTemplate(index)" class="text-red-400 hover:text-red-600 text-xs">
                      ✕
                    </button>
                  </div>
                </div>
              </div>

              <!-- States -->
              <div class="border border-slate-100 rounded-lg p-3 bg-slate-50/30">
                <div class="flex items-center justify-between mb-2">
                  <span class="text-xs font-semibold text-slate-600 uppercase tracking-wide">States</span>
                  <button @click="addWorkingStateToTemplate" class="text-secondary text-xs font-medium hover:text-secondary/80">
                    + Add
                  </button>
                </div>
                <div class="space-y-1.5 max-h-20 overflow-y-auto">
                  <div v-for="(state, index) in customTemplateForm.workingStates" :key="`state-${index}`" class="flex items-center justify-between bg-white rounded px-2 py-1.5 border border-slate-100">
                    <span class="text-xs text-slate-700 font-medium">{{ state.name || `State ${index + 1}` }}</span>
                    <div class="flex gap-1">
                      <button @click="editWorkingState(index)" class="text-blue-500 hover:text-blue-700 text-xs">✏️</button>
                      <button @click="removeWorkingStateFromTemplate(index)" class="text-red-400 hover:text-red-600 text-xs">✕</button>
                    </div>
                  </div>
                </div>
              </div>

              <!-- Variables -->
              <div class="border border-slate-100 rounded-lg p-3 bg-slate-50/30">
                <div class="flex items-center justify-between mb-2">
                  <span class="text-xs font-semibold text-slate-600 uppercase tracking-wide">Variables</span>
                  <button @click="addVariableToTemplate" class="text-secondary text-xs font-medium hover:text-secondary/80">
                    + Add
                  </button>
                </div>
                <div class="space-y-1.5 max-h-24 overflow-y-auto">
                  <div v-for="(variable, index) in customTemplateForm.variables" :key="index" class="flex items-center justify-between bg-white rounded px-2 py-1.5 border border-slate-100">
                    <span class="text-xs text-slate-700 font-medium">{{ variable.name || `Variable ${index + 1}` }}</span>
                    <div class="flex gap-1">
                      <button @click="editVariable(index)" class="text-blue-500 hover:text-blue-700 text-xs">✏️</button>
                      <button @click="removeVariableFromTemplate(index)" class="text-red-400 hover:text-red-600 text-xs">✕</button>
                    </div>
                  </div>
                </div>
              </div>

              <!-- Impacted Variables -->
              <div class="border border-slate-100 rounded-lg p-3 bg-slate-50/30">
                <div class="mb-2">
                  <span class="text-xs font-semibold text-slate-600 uppercase tracking-wide">Impacted Variables</span>
                </div>
                <div class="space-y-1.5 max-h-24 overflow-y-auto">
                  <div v-for="variable in customTemplateForm.variables.filter(v => v.name.trim())" :key="`impacted-${variable.name}`" class="flex items-center gap-2">
                    <input
                      :id="`impacted-${variable.name}`"
                      type="checkbox"
                      :checked="customTemplateForm.impactedVariables.includes(variable.name)"
                      @change="toggleImpactedVariable(variable.name)"
                      class="w-3 h-3 text-secondary bg-white border-slate-300 rounded focus:ring-0 focus:outline-none"
                    />
                    <label :for="`impacted-${variable.name}`" class="text-xs text-slate-700 cursor-pointer flex-1">
                      {{ variable.name }}
                      <span v-if="variable.description" class="text-slate-400 text-[10px] ml-1">
                        - {{ variable.description }}
                      </span>
                    </label>
                  </div>
                  <div v-if="customTemplateForm.variables.length === 0" class="text-[10px] text-slate-400 italic">
                    No variables defined yet
                  </div>
                </div>
              </div>

              <!-- APIs -->
              <div class="border border-slate-100 rounded-lg p-3 bg-slate-50/30">
                <div class="flex items-center justify-between mb-2">
                  <span class="text-xs font-semibold text-slate-600 uppercase tracking-wide">APIs</span>
                  <button @click="addApiToTemplate" class="text-secondary text-xs font-medium hover:text-secondary/80">
                    + Add
                  </button>
                </div>
                <div class="space-y-1 max-h-32 overflow-y-auto">
                  <div v-for="(api, index) in customTemplateForm.apis" :key="api.id" class="flex items-center justify-between bg-white rounded px-2 py-1.5 border border-slate-200">
                    <span class="text-xs text-slate-700 font-medium">{{ api.name || `API ${index + 1}` }}</span>
                    <div class="flex gap-1">
                      <button @click="editApi(index)" class="text-blue-500 hover:text-blue-700 text-xs">✏️</button>
                      <button @click="removeApiFromTemplate(index)" class="text-red-400 hover:text-red-600 text-xs">✕</button>
                    </div>
                  </div>
                </div>
              </div>


            </div>

            <!-- Create Button -->
            <button
              @click="createCustomTemplate"
              class="w-full py-2 bg-white hover:bg-secondary/[0.03] text-secondary border border-secondary/20 hover:border-secondary/40 rounded-md text-xs font-bold uppercase tracking-wider transition-all shadow-sm"
            >
              Create Template
            </button>
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

        <div class="px-4 pb-5 bg-slate-50/50 pt-2 space-y-3">
          <div class="space-y-2 max-h-64 overflow-y-auto">
            <div v-for="template in props.deviceTemplates.filter(t => !['Sensor', 'Switch', 'Light'].includes(t.manifest.Name))" :key="template.id" class="bg-white border border-slate-200 rounded-lg p-3">
              <div class="flex items-start justify-between mb-2">
                <div class="flex-1">
                  <h4 class="text-sm font-semibold text-slate-800">{{ template.manifest.Name }}</h4>
                  <p v-if="template.manifest.Description" class="text-xs text-slate-600 mt-1">{{ template.manifest.Description }}</p>
                </div>
                <button
                  @click="openDeleteConfirm(template)"
                  class="text-red-500 hover:text-red-700 p-1 rounded hover:bg-red-50 transition-colors"
                  title="Delete Template"
                >
                  <span class="material-symbols-outlined text-base">delete</span>
                </button>
              </div>

              <div class="grid grid-cols-2 gap-2 text-xs">
                <div class="bg-slate-50 rounded px-2 py-1">
                  <span class="text-slate-500">Variables:</span>
                  <span class="font-medium text-slate-700">{{ template.manifest.InternalVariables?.length || 0 }}</span>
                </div>
                <div class="bg-slate-50 rounded px-2 py-1">
                  <span class="text-slate-500">APIs:</span>
                  <span class="font-medium text-slate-700">{{ template.manifest.APIs?.length || 0 }}</span>
                </div>
                <div class="bg-slate-50 rounded px-2 py-1">
                  <span class="text-slate-500">States:</span>
                  <span class="font-medium text-slate-700">{{ template.manifest.WorkingStates?.length || 0 }}</span>
                </div>
                <div class="bg-slate-50 rounded px-2 py-1">
                  <span class="text-slate-500">Modes:</span>
                  <span class="font-medium text-slate-700">{{ template.manifest.Modes?.length || 0 }}</span>
                </div>
              </div>

              <div class="mt-3 pt-2 border-t border-slate-100">
                <button
                  @click="exportTemplate(template)"
                  class="text-xs px-3 py-2 bg-green-50 text-green-700 rounded hover:bg-green-100 transition-colors flex items-center gap-1"
                  title="Export Template"
                >
                  <span class="material-symbols-outlined text-sm">download</span>
                  Export
                </button>
              </div>
            </div>

            <div v-if="props.deviceTemplates.filter(t => !['Sensor', 'Switch', 'Light'].includes(t.manifest.Name)).length === 0" class="text-center py-8">
              <div class="material-symbols-outlined text-slate-300 text-3xl mb-2">inventory_2</div>
              <p class="text-sm text-slate-500 mb-2">No custom templates yet</p>
              <p class="text-xs text-slate-400">Switch to "Custom Template" mode in Add Device to create your first template.</p>
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
                      <span class="text-xs text-slate-400">{{ getRelationLabel(condition.relation) }}</span>
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
                  <span class="text-xs font-bold text-orange-600 uppercase tracking-wide">IF Conditions</span>
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
                      <span class="text-xs text-slate-400">{{ getRelationLabel(condition.relation) }}</span>
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
                  <span class="text-xs font-bold text-rose-600 uppercase tracking-wide">THEN Conditions</span>
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
                      <span class="text-xs text-slate-400">{{ getRelationLabel(condition.relation) }}</span>
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
              @change="editingConditionData.key = ''"
              class="w-full px-2 py-2 border border-slate-200 rounded-lg focus:ring-2 focus:ring-red-100 focus:border-red-400 transition-all text-sm"
              :disabled="!editingConditionData.deviceId"
            >
              <option value="" hidden>Select type</option>
              <option v-for="type in targetTypes" :key="type.value" :value="type.value">
                {{ type.label }}
              </option>
            </select>
          </div>
          <div>
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
              <option v-for="op in relationOperators" :key="op.value" :value="op.value">
                {{ op.label }}
              </option>
            </select>
          </div>
          <div class="col-span-2">
            <label class="block text-xs font-medium text-slate-600 mb-1">Value</label>
            <input
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
            <span class="text-slate-400">.</span>
            <span class="text-orange-600">{{ editingConditionData.key || '-' }}</span>
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

  <!-- Variable Dialog -->
  <div v-if="showVariableDialog" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="showVariableDialog = false">
    <div class="bg-white rounded-xl p-6 w-full max-w-2xl max-h-[90vh] overflow-y-auto shadow-2xl" @click.stop>
      <div class="flex justify-between items-center mb-6">
        <h3 class="text-lg font-semibold text-secondary">
          {{ editingVariableIndex >= 0 ? 'Edit Variable' : 'Add Variable' }}
        </h3>
        <button @click="showVariableDialog = false" class="text-slate-400 hover:text-secondary transition-colors">
          <span class="material-symbols-outlined">close</span>
        </button>
      </div>

      <div class="space-y-4">
        <div class="grid grid-cols-2 gap-4">
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Name</label>
            <input
              v-model="editingVariableData.name"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
              placeholder="Variable name"
            />
          </div>
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Description</label>
            <input
              v-model="editingVariableData.description"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
              placeholder="Description"
            />
          </div>
        </div>

        <div class="grid grid-cols-2 gap-4">
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Trust</label>
            <select
              v-model="editingVariableData.trust"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
            >
              <option value="high">High</option>
              <option value="medium">Medium</option>
              <option value="low">Low</option>
            </select>
          </div>
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Privacy</label>
            <select
              v-model="editingVariableData.privacy"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
            >
              <option value="public">Public</option>
              <option value="private">Private</option>
              <option value="low">Low</option>
            </select>
          </div>
        </div>

        <div class="grid grid-cols-2 gap-4">
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Lower Bound</label>
            <input
              v-model.number="editingVariableData.lowerBound"
              type="number"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
              placeholder="0"
            />
          </div>
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Upper Bound</label>
            <input
              v-model.number="editingVariableData.upperBound"
              type="number"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
              placeholder="100"
            />
          </div>
        </div>

        <div class="flex items-center space-x-4">
          <label class="flex items-center">
            <input
              v-model="editingVariableData.isInside"
              type="checkbox"
              class="w-4 h-4 text-secondary bg-gray-100 border-gray-300 rounded focus:ring-secondary"
            />
            <span class="ml-2 text-sm text-slate-700">Internal Variable</span>
          </label>
          <label class="flex items-center">
            <input
              v-model="editingVariableData.publicVisible"
              type="checkbox"
              class="w-4 h-4 text-secondary bg-gray-100 border-gray-300 rounded focus:ring-secondary"
            />
            <span class="ml-2 text-sm text-slate-700">Public Visible</span>
          </label>
        </div>
      </div>

      <div class="flex justify-end space-x-3 mt-6">
        <button
          @click="showVariableDialog = false"
          class="px-4 py-2 text-sm font-medium text-slate-700 bg-slate-100 border border-slate-300 rounded-md hover:bg-slate-200"
        >
          Cancel
        </button>
        <button
          @click="confirmSaveVariable"
          class="px-4 py-2 text-sm font-medium text-white bg-purple-600 border border-transparent rounded-lg hover:bg-purple-700 transition-all"
        >
          {{ editingVariableIndex >= 0 ? 'Update' : 'Add' }} Variable
        </button>
      </div>
    </div>
  </div>

  <!-- Working State Dialog -->
  <div v-if="showWorkingStateDialog" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="showWorkingStateDialog = false">
    <div class="bg-white rounded-xl p-6 w-full max-w-2xl max-h-[90vh] overflow-y-auto shadow-2xl" @click.stop>
      <div class="flex justify-between items-center mb-6">
        <h3 class="text-lg font-semibold text-secondary">
          {{ editingWorkingStateIndex >= 0 ? 'Edit Working State' : 'Add Working State' }}
        </h3>
        <button @click="showWorkingStateDialog = false" class="text-slate-400 hover:text-secondary transition-colors">
          <span class="material-symbols-outlined">close</span>
        </button>
      </div>

      <div class="space-y-4">
        <div class="grid grid-cols-2 gap-4">
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Name</label>
            <input
              v-model="editingWorkingStateData.name"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
              placeholder="State name"
            />
          </div>
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Description</label>
            <input
              v-model="editingWorkingStateData.description"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
              placeholder="Description"
            />
          </div>
        </div>

        <div class="grid grid-cols-2 gap-4">
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Trust</label>
            <select
              v-model="editingWorkingStateData.trust"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
            >
              <option value="high">High</option>
              <option value="medium">Medium</option>
              <option value="low">Low</option>
            </select>
          </div>
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Privacy</label>
            <select
              v-model="editingWorkingStateData.privacy"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
            >
              <option value="public">Public</option>
              <option value="private">Private</option>
              <option value="low">Low</option>
            </select>
          </div>
        </div>

        <div>
          <label class="block text-sm font-medium text-slate-700 mb-1">Invariant</label>
          <input
            v-model="editingWorkingStateData.invariant"
            class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
            placeholder="true"
          />
        </div>
      </div>

      <div class="flex justify-end space-x-3 mt-6">
        <button
          @click="showWorkingStateDialog = false"
          class="px-4 py-2 text-sm font-medium text-slate-700 bg-slate-100 border border-slate-300 rounded-md hover:bg-slate-200"
        >
          Cancel
        </button>
        <button
          @click="confirmSaveWorkingState"
          class="px-4 py-2 text-sm font-medium text-white bg-purple-600 border border-transparent rounded-lg hover:bg-purple-700 transition-all"
        >
          {{ editingWorkingStateIndex >= 0 ? 'Update' : 'Add' }} State
        </button>
      </div>
    </div>
  </div>

  <!-- API Dialog -->
  <div v-if="showApiDialog" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="showApiDialog = false">
    <div class="bg-white rounded-xl p-6 w-full max-w-lg shadow-2xl" @click.stop>
      <div class="flex justify-between items-center mb-6">
        <h3 class="text-lg font-semibold text-secondary">
          {{ editingApiIndex >= 0 ? 'Edit API' : 'Add API' }}
        </h3>
        <button @click="showApiDialog = false" class="text-slate-400 hover:text-secondary transition-colors">
          <span class="material-symbols-outlined">close</span>
        </button>
      </div>

      <div class="space-y-4">
        <div class="grid grid-cols-2 gap-4">
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Name</label>
            <input
              v-model="editingApiData.name"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
              placeholder="API name"
            />
          </div>
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Description</label>
            <input
              v-model="editingApiData.description"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
              placeholder="Description"
            />
          </div>
        </div>

        <div class="grid grid-cols-2 gap-4">
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Start State</label>
            <select
              v-model="editingApiData.startState"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
            >
              <option value="" hidden>Select state</option>
              <option v-for="state in customTemplateForm.workingStates" :key="state.name" :value="state.name">
                {{ state.name }}
              </option>
            </select>
          </div>
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">End State</label>
            <select
              v-model="editingApiData.endState"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
            >
              <option value="" hidden>Select state</option>
              <option v-for="state in customTemplateForm.workingStates" :key="state.name" :value="state.name">
                {{ state.name }}
              </option>
            </select>
          </div>
        </div>

        <div class="grid grid-cols-2 gap-4">
          <div>
            <label class="block text-sm font-medium text-slate-700 mb-1">Trigger</label>
            <select
              v-model="editingApiData.trigger"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-secondary focus:border-secondary transition-all"
            >
              <option value="user">User Trigger</option>
              <option value="auto">Auto Trigger</option>
              <option value="event">Event Trigger</option>
            </select>
          </div>
          <div class="flex items-center">
            <label class="flex items-center gap-2 text-sm text-slate-700">
              <input
                type="checkbox"
                v-model="editingApiData.signal"
                class="w-4 h-4 text-secondary rounded"
              />
              Is Signal API
            </label>
          </div>
        </div>

        <!-- Assignments -->
        <div>
          <div class="flex items-center justify-between mb-2">
            <label class="text-sm font-medium text-slate-700">Assignments</label>
            <button
              @click="editingApiData.assignments.push({variableName: '', changeRate: ''})"
              class="text-xs text-secondary hover:text-secondary/80"
            >
              + Add Assignment
            </button>
          </div>
          <div class="space-y-2 max-h-32 overflow-y-auto">
            <div v-for="(assignment, index) in editingApiData.assignments" :key="index" class="flex items-center gap-2">
              <select
                v-model="assignment.variableName"
                class="flex-1 px-2 py-1.5 border border-slate-200 rounded text-xs"
              >
                <option value="">Select variable</option>
                <option v-for="v in customTemplateForm.variables.filter(v => v.name.trim())" :key="v.name" :value="v.name">
                  {{ v.name }}
                </option>
              </select>
              <input
                v-model="assignment.changeRate"
                class="w-20 px-2 py-1.5 border border-slate-200 rounded text-xs"
                placeholder="Change rate"
              />
              <button
                @click="editingApiData.assignments.splice(index, 1)"
                class="p-1 text-red-400 hover:text-red-600"
              >
                <span class="material-symbols-outlined text-sm">close</span>
              </button>
            </div>
          </div>
        </div>
      </div>

      <div class="flex justify-end space-x-3 mt-6">
        <button
          @click="showApiDialog = false"
          class="px-4 py-2 text-sm font-medium text-slate-700 bg-slate-100 border border-slate-300 rounded-md hover:bg-slate-200"
        >
          Cancel
        </button>
        <button
          @click="confirmSaveApi"
          class="px-4 py-2 text-sm font-medium text-white bg-purple-600 border border-transparent rounded-lg hover:bg-purple-700 transition-all"
        >
          {{ editingApiIndex >= 0 ? 'Update' : 'Add' }} API
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

<script setup lang="ts">
import { ref, reactive, computed } from 'vue'
import { ElMessage } from 'element-plus'

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
  apis: [] as Array<{name: string, description: string}>,
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
const showDeleteConfirmDialog = ref(false)
const editingVariableIndex = ref(-1)
const editingWorkingStateIndex = ref(-1)
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

// JSON format example for template creation
const jsonExample = `{
  "Name": "SmartThermostat",
  "Description": "A smart thermostat device",
  "InitState": "idle",
  "Modes": ["heating", "cooling"],
  "InternalVariables": [
    {
      "Name": "temperature",
      "Description": "Current temperature",
      "IsInside": true,
      "PublicVisible": true,
      "Trust": "high",
      "Privacy": "low",
      "LowerBound": -10,
      "UpperBound": 50
    }
  ],
  "ImpactedVariables": ["temperature"],
  "APIs": [
    {
      "Name": "setTemperature",
      "Description": "Set target temperature"
    }
  ],
  "WorkingStates": [
    {
      "Name": "heating",
      "Description": "Device is heating",
      "Trust": "high",
      "Privacy": "low",
      "Invariant": "temperature < targetTemp"
    }
  ]
}`

// Specification form data
  const specForm = reactive({
    templateId: '',
    selectedDevices: [] as Array<{deviceId: string, deviceLabel: string, selectedApis: string[]}>,
    formula: ''
  })



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

// Toggle panel collapse
const togglePanel = () => {
  isCollapsed.value = !isCollapsed.value
}

const emit = defineEmits<{
  'create-device': [data: { template: any, customName: string }]
  'open-rule-builder': []
  'add-spec': [data: { templateId: string, devices: Array<{deviceId: string, deviceLabel: string, selectedApis: string[]}>, formula: string }]
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
  customTemplateForm.apis.push({ name: '', description: '' })
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
          Signal: false,
          StartState: customTemplateForm.initState,
          EndState: customTemplateForm.initState,
          Trigger: "user",
          Assignments: []
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


  const selectLTLOperator = (operator: string) => {
    specForm.formula += operator + ' '
  }

  const addDeviceToSpec = (deviceId: string) => {
    const device = props.nodes.find(d => d.id === deviceId)
    if (!device) return

    // 检查是否已添加
    if (specForm.selectedDevices.some(d => d.deviceId === deviceId)) {
      ElMessage({
        message: 'Device already added',
        type: 'warning',
        center: true
      })
      return
    }

    specForm.selectedDevices.push({
      deviceId,
      deviceLabel: device.label,
      selectedApis: []
    })
  }

  const removeDeviceFromSpec = (deviceId: string) => {
    specForm.selectedDevices = specForm.selectedDevices.filter(d => d.deviceId !== deviceId)
  }

  const toggleDeviceApi = (deviceId: string, apiName: string) => {
    const device = specForm.selectedDevices.find(d => d.deviceId === deviceId)
    if (!device) return

    const index = device.selectedApis.indexOf(apiName)
    if (index > -1) {
      device.selectedApis.splice(index, 1)
    } else {
      device.selectedApis.push(apiName)
    }
  }

  const insertVariableIntoFormula = (deviceId: string, apiName: string) => {
    const device = props.nodes.find(d => d.id === deviceId)
    if (!device) return

    // 创建变量引用，如: sensor_temp, light_status 等
    const variableName = `${device.label.toLowerCase().replace(/\s+/g, '_')}_${apiName}`
    specForm.formula += variableName + ' '
  }

  // 获取设备可用API列表
  const getDeviceApis = (deviceId: string) => {
    const device = props.nodes.find(d => d.id === deviceId)
    if (!device) return []

    // 这里可以根据设备模板返回不同的API
    // 暂时返回一些常见的API
    return ['status', 'value', 'active', 'temperature', 'humidity', 'motion']
  }

const createSpecification = () => {
  if (!specForm.templateId) {
    ElMessage.warning({
      message: 'Select a template',
      center: true
    })
    return
  }

  if (specForm.selectedDevices.length === 0) {
    ElMessage.warning({
      message: 'Add at least one device',
      center: true
    })
    return
  }

  if (!specForm.formula.trim()) {
    ElMessage.warning({
      message: 'Enter LTL formula',
      center: true
    })
    return
  }

  emit('add-spec', {
    templateId: specForm.templateId,
    devices: specForm.selectedDevices,
    formula: specForm.formula
  })

  // Reset form
  specForm.templateId = ''
  specForm.selectedDevices = []
  specForm.formula = ''
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

    <div
      class="flex-1 overflow-y-auto custom-scrollbar bg-white transition-all duration-300"
      :class="isCollapsed ? 'opacity-0 pointer-events-none p-0' : 'p-0'"
    >
      <!-- Add Device Section -->
      <details class="group border-b border-slate-100" open>
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
              <!-- APIs -->
              <div class="border border-slate-100 rounded-lg p-3 bg-slate-50/30">
                <div class="flex items-center justify-between mb-2">
                  <span class="text-xs font-semibold text-slate-600 uppercase tracking-wide">APIs</span>
                  <button @click="addApiToTemplate" class="text-secondary text-xs font-medium hover:text-secondary/80">
                    + Add
                  </button>
                </div>
                <div class="space-y-1.5 max-h-20 overflow-y-auto">
                  <div v-for="(api, index) in customTemplateForm.apis" :key="index" class="flex items-center gap-2">
                    <input
                      v-model="api.name"
                      class="flex-1 bg-white border border-slate-200 rounded px-2 py-1 text-xs focus:border-secondary"
                      placeholder="API name"
                    />
                    <button @click="removeApiFromTemplate(index)" class="text-red-400 hover:text-red-600 text-xs">
                      ✕
                    </button>
                  </div>
                </div>
              </div>

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

      <!-- Template Manager Section -->
      <details class="group border-b border-slate-100">
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

      <!-- Rule Lab Section -->
      <details class="group border-b border-slate-100">
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

      <!-- Protocol Hub Section -->
      <details class="group border-b border-slate-100">
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-slate-50 transition-colors list-none select-none">
          <div class="flex items-center gap-3">
            <span class="material-symbols-outlined text-lg text-purple-500">schema</span>
            <span class="text-sm font-semibold text-slate-700">Specifications</span>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-sm">expand_more</span>
        </summary>

        <div class="px-4 pb-5 bg-slate-50/50 pt-2 space-y-2">
          <p class="text-[10px] text-slate-400 mb-2 font-medium">Linear Temporal Logic (LTL) - Global Specifications</p>

          <div class="flex gap-2 mb-3">
            <!-- Global Operator -->
            <div
              class="flex-1 p-2 bg-white border border-slate-200 rounded text-center hover:border-purple-300 hover:shadow-sm cursor-pointer transition-all"
              @click="selectLTLOperator('G')"
            >
              <span class="block text-lg font-bold text-purple-600">G</span>
              <span class="text-[9px] uppercase text-slate-400 font-medium">Global</span>
            </div>

            <!-- Future Operator -->
            <div
              class="flex-1 p-2 bg-white border border-slate-200 rounded text-center hover:border-purple-300 hover:shadow-sm cursor-pointer transition-all"
              @click="selectLTLOperator('F')"
            >
              <span class="block text-lg font-bold text-purple-600">F</span>
              <span class="text-[9px] uppercase text-slate-400 font-medium">Future</span>
            </div>

            <!-- Next Operator -->
            <div
              class="flex-1 p-2 bg-white border border-slate-200 rounded text-center hover:border-purple-300 hover:shadow-sm cursor-pointer transition-all"
              @click="selectLTLOperator('X')"
            >
              <span class="block text-lg font-bold text-purple-600">X</span>
              <span class="text-[9px] uppercase text-slate-400 font-medium">Next</span>
            </div>
          </div>

            <!-- Specification Creation -->
            <div class="space-y-3">
              <!-- Device Selection -->
              <div>
                <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Add Devices</label>
                <select
                  @change="addDeviceToSpec(($event.target as HTMLSelectElement).value); ($event.target as HTMLSelectElement).value = ''"
                  class="w-full bg-white border border-slate-200 rounded-md px-2 py-2 text-xs text-slate-700 focus:border-purple-300 focus:ring-purple-200"
                >
                  <option value="" disabled hidden>Select Device to Add</option>
                  <option
                    v-for="device in props.nodes"
                    :key="device.id"
                    :value="device.id"
                  >
                    {{ device.label }} ({{ device.id }})
                  </option>
                </select>
              </div>

              <!-- Selected Devices with Variables -->
              <div v-if="specForm.selectedDevices.length > 0">
                <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Selected Devices & Variables</label>
                <div class="space-y-2 max-h-32 overflow-y-auto">
                  <div
                    v-for="device in specForm.selectedDevices"
                    :key="device.deviceId"
                    class="bg-purple-50/50 border border-purple-200 rounded p-2"
                  >
                    <div class="flex items-center justify-between mb-1">
                      <span class="text-xs font-medium text-purple-700">{{ device.deviceLabel }}</span>
                      <button
                        @click="removeDeviceFromSpec(device.deviceId)"
                        class="text-purple-400 hover:text-red-500 text-xs"
                      >
                        ✕
                      </button>
                    </div>
                    <div class="flex flex-wrap gap-1">
                      <button
                        v-for="api in getDeviceApis(device.deviceId)"
                        :key="api"
                        @click="toggleDeviceApi(device.deviceId, api)"
                        :class="[
                          'px-1.5 py-0.5 text-[9px] rounded border transition-colors',
                          device.selectedApis.includes(api)
                            ? 'bg-slate-200 text-slate-900 border-slate-300'
                            : 'bg-white text-purple-600 border-purple-300 hover:bg-purple-50'
                        ]"
                      >
                        {{ api }}
                      </button>
                    </div>
                  </div>
                </div>
              </div>

              <!-- Variable Insertion Buttons -->
              <div v-if="specForm.selectedDevices.length > 0">
                <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Insert Variables</label>
                <div class="flex flex-wrap gap-1">
                  <template v-for="device in specForm.selectedDevices" :key="device.deviceId">
                    <button
                      v-for="api in device.selectedApis"
                      :key="`${device.deviceId}-${api}`"
                      @click="insertVariableIntoFormula(device.deviceId, api)"
                      class="px-2 py-1 text-[9px] bg-blue-50 text-blue-700 border border-blue-200 rounded hover:bg-blue-100 transition-colors"
                    >
                      {{ device.deviceLabel.toLowerCase().replace(/\s+/g, '_') }}_{{ api }}
                    </button>
                  </template>
                </div>
              </div>

            <div>
              <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Template</label>
              <select
                v-model="specForm.templateId"
                class="w-full bg-white border border-slate-200 rounded-md px-2 py-2 text-xs text-slate-700 focus:border-purple-300 focus:ring-purple-200"
              >
                <option value="" disabled hidden>Select Template</option>
                <option value="safety">Safety Property</option>
                <option value="liveness">Liveness Property</option>
                <option value="fairness">Fairness Property</option>
              </select>
            </div>

            <div>
              <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Formula</label>
              <input
                v-model="specForm.formula"
                class="w-full bg-white border border-slate-200 rounded-md px-3 py-2 text-xs text-slate-700 focus:border-purple-300 focus:ring-purple-200 placeholder:text-slate-400"
                placeholder="e.g. G (sensor_temp > 25)"
                type="text"
              />
            </div>

            <button
              @click="createSpecification"
              class="w-full py-2 bg-slate-200 hover:bg-slate-300 text-slate-900 border border-slate-300 rounded-md text-xs font-bold uppercase tracking-wider transition-all"
            >
              Create Specification
            </button>
          </div>
        </div>
      </details>
    </div>

  </aside>

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

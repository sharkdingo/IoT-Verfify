<script setup lang="ts">
import { ref, reactive } from 'vue'
import { useRouter } from 'vue-router'
import { ElMessage as ElMessageRaw } from 'element-plus'

// Element-Plus typings vary by version; we use an `any` alias to keep runtime behavior (e.g. `center`) without TS errors.
const ElMessage = ElMessageRaw as any
const router = useRouter()

// Props
interface Props {
  // We don't strictly need templates to create, but useful if we wanted to check duplicates or similar
}

const props = withDefaults(defineProps<Props>(), {
})

const emit = defineEmits<{
  'refresh-templates': []
}>()

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

// Dialog states
const showVariableDialog = ref(false)
const showWorkingStateDialog = ref(false)
const showApiDialog = ref(false)
const editingVariableIndex = ref(-1)
const editingWorkingStateIndex = ref(-1)
const editingApiIndex = ref(-1)

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

// JSON file upload handling
const fileInput = ref<HTMLInputElement>()

const triggerFileInput = () => {
  fileInput.value?.click()
}

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

    // Navigate to board
    router.push('/board')

    // Reset form
    customTemplateForm.name = ''
    customTemplateForm.description = ''
    customTemplateForm.initState = ''
    customTemplateForm.modes = []
    customTemplateForm.apis = []
    customTemplateForm.variables = []
    customTemplateForm.impactedVariables = []
    customTemplateForm.workingStates = []

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

  return message.length > 40 ? message.substring(0, 40) + '...' : message
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

    // Navigate to board
    router.push('/board')
    emit('refresh-templates')

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

// Helper functions for the form
const addModeToTemplate = () => {
  customTemplateForm.modes.push('')
}

const removeModeFromTemplate = (index: number) => {
  customTemplateForm.modes.splice(index, 1)
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

const toggleImpactedVariable = (variableName: string) => {
  if (!variableName.trim()) return // Don't allow empty variable names

  const index = customTemplateForm.impactedVariables.indexOf(variableName)
  if (index > -1) {
    customTemplateForm.impactedVariables.splice(index, 1)
  } else {
    customTemplateForm.impactedVariables.push(variableName)
  }
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

const saveApi = (apiData: any) => {
  if (editingApiIndex.value >= 0) {
    customTemplateForm.apis[editingApiIndex.value] = { ...apiData, id: customTemplateForm.apis[editingApiIndex.value].id }
  } else {
    customTemplateForm.apis.push({ ...apiData, id: `api-${Date.now()}` })
  }
  showApiDialog.value = false
}

</script>

<template>
  <div class="custom-template-creator space-y-4 w-full max-w-4xl mx-auto p-4 sm:p-4 lg:p-4">

    <!-- JSON Import -->
    <div
      class="mb-6 group cursor-pointer relative overflow-hidden rounded-lg border-2 border-dashed border-orange-300 dark:border-orange-700 hover:border-orange-500 bg-orange-50 dark:bg-slate-800/50 transition-all duration-300 p-4 text-center"
      @click="triggerFileInput"
    >
      <input
        ref="fileInput"
        type="file"
        accept=".json"
        @change="handleJsonFileUpload"
        class="hidden"
      />
      <div class="flex flex-row items-center justify-center gap-3">
        <div class="w-8 h-8 rounded-full bg-orange-100 text-orange-500 flex items-center justify-center shadow-sm group-hover:scale-110 transition-transform duration-300 dark:bg-orange-900/30 dark:text-orange-400">
            <span class="material-icons-round text-lg">upload_file</span>
        </div>
        <div class="text-left">
          <h3 class="font-semibold text-orange-600 dark:text-orange-400 text-sm">Import JSON Template</h3>
          <p class="text-xs text-slate-500 dark:text-slate-400 mt-0.5">Upload a JSON file to create template automatically</p>
        </div>
      </div>
    </div>

    <!-- Basic Info -->
    <div class="space-y-3">
      <div class="grid grid-cols-1 sm:grid-cols-2 gap-3">
        <div class="group">
          <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1 ml-1">Template Name</label>
          <input
            v-model="customTemplateForm.name"
            class="w-full px-3 py-2 rounded-lg border border-slate-300 dark:border-slate-700 bg-white dark:bg-slate-900/50 text-slate-800 dark:text-slate-100 focus:ring-2 focus:ring-orange-500/20 focus:border-orange-500 dark:focus:border-orange-500 transition-all placeholder:text-slate-400 dark:placeholder:text-slate-600 outline-none text-sm"
            placeholder="e.g. Smart Thermostat"
            type="text"
          />
        </div>
        <div class="group">
          <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1 ml-1">Description <span class="text-slate-400 font-normal">(optional)</span></label>
          <input
            v-model="customTemplateForm.description"
            class="w-full px-3 py-2 rounded-lg border border-slate-300 dark:border-slate-700 bg-white dark:bg-slate-900/50 text-slate-800 dark:text-slate-100 focus:ring-2 focus:ring-orange-500/20 focus:border-orange-500 dark:focus:border-orange-500 transition-all placeholder:text-slate-400 dark:placeholder:text-slate-600 outline-none text-sm"
            placeholder="Brief description"
            type="text"
          />
        </div>
      </div>
    </div>

    <hr class="border-slate-200 dark:border-slate-800 my-4"/>

    <!-- Compact Sections -->
    <div class="space-y-3">
      <!-- Modes -->
      <div class="bg-white dark:bg-slate-800/50 border border-slate-200 dark:border-slate-700 rounded-lg p-3">
        <div class="flex items-center justify-between mb-2">
          <div class="flex items-center gap-2">
            <span class="material-icons-round text-slate-400 dark:text-slate-500 text-sm">tune</span>
            <div class="flex flex-col">
              <span class="font-semibold text-slate-700 dark:text-slate-200 text-xs uppercase tracking-wide">Modes</span>
              <span class="text-[10px] text-slate-500">{{ customTemplateForm.modes.length }} defined</span>
            </div>
          </div>
          <button @click="addModeToTemplate" class="text-orange-500 hover:text-orange-600 hover:bg-orange-50 dark:hover:bg-orange-900/20 px-2 py-1 rounded text-xs font-medium transition-colors flex items-center gap-0.5">
            <span class="material-icons-round text-base">add</span> Add
          </button>
        </div>
        <div class="flex flex-wrap gap-1.5">
          <div v-for="(mode, idx) in customTemplateForm.modes" :key="idx" class="flex items-center gap-1 bg-slate-100 dark:bg-slate-700 px-2 py-1 rounded border border-slate-200 dark:border-slate-600">
            <input
              v-model="customTemplateForm.modes[idx]"
              class="bg-transparent border-none focus:ring-0 text-xs text-slate-700 dark:text-slate-300 w-20 outline-none"
              placeholder="Mode name"
            />
            <button @click="removeModeFromTemplate(idx)" class="text-slate-400 hover:text-red-500 p-0.5">×</button>
          </div>
          <div v-if="customTemplateForm.modes.length === 0" class="text-[10px] text-slate-400 italic py-1">No modes</div>
        </div>
      </div>

      <!-- Variables -->
      <div class="bg-white dark:bg-slate-800/50 border border-slate-200 dark:border-slate-700 rounded-lg p-3">
        <div class="flex items-center justify-between mb-2">
          <div class="flex items-center gap-2">
            <span class="material-icons-round text-slate-400 dark:text-slate-500 text-sm">data_object</span>
            <div class="flex flex-col">
              <span class="font-semibold text-slate-700 dark:text-slate-200 text-xs uppercase tracking-wide">Variables</span>
              <span class="text-[10px] text-slate-500">{{ customTemplateForm.variables.length }} defined</span>
            </div>
          </div>
          <button @click="addVariableToTemplate" class="text-orange-500 hover:text-orange-600 hover:bg-orange-50 dark:hover:bg-orange-900/20 px-2 py-1 rounded text-xs font-medium transition-colors flex items-center gap-0.5">
            <span class="material-icons-round text-base">add</span> Add
          </button>
        </div>

        <div v-if="customTemplateForm.variables.length > 0" class="mt-2 space-y-1.5">
          <div v-for="(variable, idx) in customTemplateForm.variables" :key="idx" class="flex items-center justify-between bg-slate-50 dark:bg-slate-900/50 border border-slate-200 dark:border-slate-700 rounded px-2 py-1.5">
            <div class="flex items-center gap-2 overflow-hidden">
              <span class="material-icons-round text-slate-400 text-xs">tag</span>
              <div class="flex flex-col min-w-0">
                <span class="text-xs font-medium text-slate-700 dark:text-slate-300 truncate">{{ variable.name || '(Unnamed)' }}</span>
              </div>
            </div>
            <div class="flex items-center gap-1.5 ml-2">
               <button @click="editVariable(idx)" class="text-slate-400 hover:text-orange-500 p-0.5">
                 <span class="material-symbols-outlined text-xs">edit</span>
               </button>
               <button @click="removeVariableFromTemplate(idx)" class="text-slate-400 hover:text-red-500 p-0.5">
                 <span class="material-symbols-outlined text-xs">close</span>
               </button>
            </div>
          </div>
        </div>
      </div>

      <!-- States -->
      <div class="bg-white dark:bg-slate-800/50 border border-slate-200 dark:border-slate-700 rounded-lg p-3">
        <div class="flex items-center justify-between mb-2">
          <div class="flex items-center gap-2">
            <span class="material-icons-round text-slate-400 dark:text-slate-500 text-sm">toggle_on</span>
            <div class="flex flex-col">
              <span class="font-semibold text-slate-700 dark:text-slate-200 text-xs uppercase tracking-wide">States</span>
              <span class="text-[10px] text-slate-500">{{ customTemplateForm.workingStates.length }} defined</span>
            </div>
          </div>
          <button @click="addWorkingStateToTemplate" class="text-orange-500 hover:text-orange-600 hover:bg-orange-50 dark:hover:bg-orange-900/20 px-2 py-1 rounded text-xs font-medium transition-colors flex items-center gap-0.5">
            <span class="material-icons-round text-base">add</span> Add
          </button>
        </div>

        <div v-if="customTemplateForm.workingStates.length > 0" class="mt-2 space-y-1.5">
           <div v-for="(state, idx) in customTemplateForm.workingStates" :key="idx" class="flex items-center justify-between bg-slate-50 dark:bg-slate-900/50 border border-slate-200 dark:border-slate-700 rounded px-2 py-1.5">
            <div class="flex items-center gap-2 overflow-hidden">
              <span class="material-icons-round text-slate-400 text-xs">settings</span>
              <div class="flex flex-col min-w-0">
                <span class="text-xs font-medium text-slate-700 dark:text-slate-300 truncate">{{ state.name || '(Unnamed)' }}</span>
              </div>
            </div>
            <div class="flex items-center gap-1.5 ml-2">
               <button @click="editWorkingState(idx)" class="text-slate-400 hover:text-orange-500 p-0.5">
                 <span class="material-symbols-outlined text-xs">edit</span>
               </button>
               <button @click="removeWorkingStateFromTemplate(idx)" class="text-slate-400 hover:text-red-500 p-0.5">
                 <span class="material-symbols-outlined text-xs">close</span>
               </button>
            </div>
          </div>
        </div>
      </div>

      <!-- Initial State (Moved here) -->
      <div class="bg-white dark:bg-slate-800/50 border border-slate-200 dark:border-slate-700 rounded-lg p-3">
        <div class="group">
          <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1 ml-1">Initial State</label>
          <select
            v-model="customTemplateForm.initState"
            class="w-full px-3 py-2 rounded-lg border border-slate-300 dark:border-slate-700 bg-white dark:bg-slate-900/50 text-slate-800 dark:text-slate-100 focus:ring-2 focus:ring-orange-500/20 focus:border-orange-500 dark:focus:border-orange-500 transition-all outline-none text-sm"
          >
            <option value="" disabled>Select state</option>
            <option v-for="state in customTemplateForm.workingStates" :key="state.name" :value="state.name">
              {{ state.name }}
            </option>
          </select>
        </div>
      </div>

      <!-- APIs -->
      <div class="bg-white dark:bg-slate-800/50 border border-slate-200 dark:border-slate-700 rounded-lg p-3">
        <div class="flex items-center justify-between mb-2">
          <div class="flex items-center gap-2">
            <span class="material-icons-round text-slate-400 dark:text-slate-500 text-sm">api</span>
            <div class="flex flex-col">
              <span class="font-semibold text-slate-700 dark:text-slate-200 text-xs uppercase tracking-wide">APIs</span>
              <span class="text-[10px] text-slate-500">{{ customTemplateForm.apis.length }} defined</span>
            </div>
          </div>
          <button @click="addApiToTemplate" class="text-orange-500 hover:text-orange-600 hover:bg-orange-50 dark:hover:bg-orange-900/20 px-2 py-1 rounded text-xs font-medium transition-colors flex items-center gap-0.5">
            <span class="material-icons-round text-base">add</span> Add
          </button>
        </div>

        <div v-if="customTemplateForm.apis.length > 0" class="mt-2 space-y-1.5">
           <div v-for="(api, idx) in customTemplateForm.apis" :key="idx" class="flex items-center justify-between bg-slate-50 dark:bg-slate-900/50 border border-slate-200 dark:border-slate-700 rounded px-2 py-1.5">
            <div class="flex items-center gap-2 overflow-hidden">
              <span class="material-symbols-outlined text-slate-400 text-xs">link</span>
              <div class="flex flex-col min-w-0">
                <span class="text-xs font-medium text-slate-700 dark:text-slate-300 truncate">{{ api.name || '(Unnamed)' }}</span>
              </div>
            </div>
            <div class="flex items-center gap-1.5 ml-2">
               <button @click="editApi(idx)" class="text-slate-400 hover:text-orange-500 p-0.5">
                 <span class="material-symbols-outlined text-xs">edit</span>
               </button>
               <button @click="removeApiFromTemplate(idx)" class="text-slate-400 hover:text-red-500 p-0.5">
                 <span class="material-symbols-outlined text-xs">close</span>
               </button>
            </div>
          </div>
        </div>
      </div>

      <!-- Impacted Variables -->
      <div class="bg-white dark:bg-slate-800/50 border border-slate-200 dark:border-slate-700 rounded-lg p-3">
        <div class="flex items-center justify-between mb-2">
          <div class="flex items-center gap-2">
            <span class="material-icons-round text-slate-400 dark:text-slate-500 text-sm">bolt</span>
            <span class="font-semibold text-slate-700 dark:text-slate-200 text-xs uppercase tracking-wide">Impacted Vars</span>
          </div>
          <span class="text-[10px] text-slate-500">{{ customTemplateForm.impactedVariables.length }} selected</span>
        </div>
        <div class="min-h-[40px] rounded border border-dashed border-slate-300 dark:border-slate-700 bg-slate-50 dark:bg-slate-900/30 flex flex-wrap items-center p-1.5 gap-1.5">
          
          <div v-if="customTemplateForm.variables.length === 0" class="w-full text-center py-1">
            <span class="text-[10px] text-slate-400 italic">Add variables first</span>
          </div>

          <div v-for="variable in customTemplateForm.variables.filter(v => v.name.trim())" :key="`impacted-${variable.name}`" class="flex items-center gap-1.5 bg-white dark:bg-slate-800 border border-slate-200 dark:border-slate-700 px-2 py-1 rounded shadow-sm">
            <input
              :id="`impacted-${variable.name}`"
              type="checkbox"
              :checked="customTemplateForm.impactedVariables.includes(variable.name)"
              @change="toggleImpactedVariable(variable.name)"
              class="w-3 h-3 text-orange-500 bg-slate-100 border-slate-300 rounded focus:ring-orange-500 dark:focus:ring-offset-slate-900 dark:bg-slate-700 dark:border-slate-600"
            />
            <label :for="`impacted-${variable.name}`" class="text-[10px] text-slate-700 dark:text-slate-300 cursor-pointer">
              {{ variable.name }}
            </label>
          </div>

        </div>
      </div>
    </div>

    <!-- Create Button -->
    <div class="pt-4">
      <button
        @click="createCustomTemplate"
        class="w-full bg-orange-500 hover:bg-orange-600 text-white font-bold py-3 px-4 rounded-lg shadow-lg shadow-orange-500/25 hover:shadow-orange-500/40 transform hover:-translate-y-0.5 transition-all duration-200 text-sm uppercase tracking-wider flex items-center justify-center gap-2 dark:bg-orange-600 dark:hover:bg-orange-700"
      >
        <span class="material-icons-round text-lg">check_circle</span>
        Create Template
      </button>
    </div>

  </div>

  <!-- Variable Dialog -->
  <div v-if="showVariableDialog" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="showVariableDialog = false">
    <div class="bg-white dark:bg-slate-800 rounded-xl p-4 w-full max-w-lg max-h-[90vh] overflow-y-auto shadow-2xl dark:text-slate-100" @click.stop>
      <div class="flex justify-between items-center mb-4">
        <h3 class="text-sm font-semibold text-orange-500 dark:text-orange-400">
          {{ editingVariableIndex >= 0 ? 'Edit Variable' : 'Add Variable' }}
        </h3>
        <button @click="showVariableDialog = false" class="text-slate-400 hover:text-orange-500 transition-colors dark:hover:text-slate-300">
          <span class="material-symbols-outlined">close</span>
        </button>
      </div>

      <div class="space-y-3">
        <div class="grid grid-cols-2 gap-3">
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Name</label>
            <input
              v-model="editingVariableData.name"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
              placeholder="Var name"
            />
          </div>
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Description</label>
            <input
              v-model="editingVariableData.description"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
              placeholder="Desc"
            />
          </div>
        </div>

        <div class="grid grid-cols-2 gap-3">
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Trust</label>
            <select
              v-model="editingVariableData.trust"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
            >
              <option value="high">High</option>
              <option value="medium">Medium</option>
              <option value="low">Low</option>
            </select>
          </div>
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Privacy</label>
            <select
              v-model="editingVariableData.privacy"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
            >
              <option value="public">Public</option>
              <option value="private">Private</option>
              <option value="low">Low</option>
            </select>
          </div>
        </div>

        <div class="grid grid-cols-2 gap-3">
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Lower Bound</label>
            <input
              v-model.number="editingVariableData.lowerBound"
              type="number"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
              placeholder="0"
            />
          </div>
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Upper Bound</label>
            <input
              v-model.number="editingVariableData.upperBound"
              type="number"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
              placeholder="100"
            />
          </div>
        </div>

        <div class="flex items-center space-x-4 mt-1">
          <label class="flex items-center">
            <input
              v-model="editingVariableData.isInside"
              type="checkbox"
              class="w-3.5 h-3.5 text-orange-500 bg-slate-100 border-slate-300 rounded focus:ring-orange-500 dark:focus:ring-offset-slate-900 dark:bg-slate-700 dark:border-slate-600"
            />
            <span class="ml-2 text-xs text-slate-700 dark:text-slate-300">Internal</span>
          </label>
          <label class="flex items-center">
            <input
              v-model="editingVariableData.publicVisible"
              type="checkbox"
              class="w-3.5 h-3.5 text-orange-500 bg-slate-100 border-slate-300 rounded focus:ring-orange-500 dark:focus:ring-offset-slate-900 dark:bg-slate-700 dark:border-slate-600"
            />
            <span class="ml-2 text-xs text-slate-700 dark:text-slate-300">Public</span>
          </label>
        </div>
      </div>

      <div class="flex justify-end space-x-2 mt-4">
        <button
          @click="showVariableDialog = false"
          class="px-3 py-1.5 text-xs font-medium text-slate-700 bg-slate-100 border border-slate-200 rounded-lg hover:bg-slate-200 dark:bg-slate-700 dark:text-slate-300 dark:border-slate-600 dark:hover:bg-slate-600"
        >
          Cancel
        </button>
        <button
          @click="confirmSaveVariable"
          class="px-3 py-1.5 text-xs font-medium text-white bg-orange-500 rounded-lg hover:bg-orange-600 transition-colors dark:bg-orange-600 dark:hover:bg-orange-700"
        >
          {{ editingVariableIndex >= 0 ? 'Update' : 'Add' }}
        </button>
      </div>
    </div>
  </div>

  <!-- Working State Dialog -->
  <div v-if="showWorkingStateDialog" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="showWorkingStateDialog = false">
    <div class="bg-white dark:bg-slate-800 rounded-xl p-4 w-full max-w-lg max-h-[90vh] overflow-y-auto shadow-2xl dark:text-slate-100" @click.stop>
      <div class="flex justify-between items-center mb-4">
        <h3 class="text-sm font-semibold text-orange-500 dark:text-orange-400">
          {{ editingWorkingStateIndex >= 0 ? 'Edit Working State' : 'Add Working State' }}
        </h3>
        <button @click="showWorkingStateDialog = false" class="text-slate-400 hover:text-orange-500 transition-colors dark:hover:text-slate-300">
          <span class="material-symbols-outlined">close</span>
        </button>
      </div>

      <div class="space-y-3">
        <div class="grid grid-cols-2 gap-3">
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Name</label>
            <input
              v-model="editingWorkingStateData.name"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
              placeholder="State name"
            />
          </div>
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Description</label>
            <input
              v-model="editingWorkingStateData.description"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
              placeholder="Desc"
            />
          </div>
        </div>

        <div class="grid grid-cols-2 gap-3">
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Trust</label>
            <select
              v-model="editingWorkingStateData.trust"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
            >
              <option value="high">High</option>
              <option value="medium">Medium</option>
              <option value="low">Low</option>
            </select>
          </div>
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Privacy</label>
            <select
              v-model="editingWorkingStateData.privacy"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
            >
              <option value="public">Public</option>
              <option value="private">Private</option>
              <option value="low">Low</option>
            </select>
          </div>
        </div>

        <div>
          <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Invariant</label>
          <input
            v-model="editingWorkingStateData.invariant"
            class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
            placeholder="true"
          />
        </div>
      </div>

      <div class="flex justify-end space-x-2 mt-4">
        <button
          @click="showWorkingStateDialog = false"
          class="px-3 py-1.5 text-xs font-medium text-slate-700 bg-slate-100 border border-slate-200 rounded-lg hover:bg-slate-200 dark:bg-slate-700 dark:text-slate-300 dark:border-slate-600 dark:hover:bg-slate-600"
        >
          Cancel
        </button>
        <button
          @click="confirmSaveWorkingState"
          class="px-3 py-1.5 text-xs font-medium text-white bg-orange-500 rounded-lg hover:bg-orange-600 transition-colors dark:bg-orange-600 dark:hover:bg-orange-700"
        >
          {{ editingWorkingStateIndex >= 0 ? 'Update' : 'Add' }}
        </button>
      </div>
    </div>
  </div>

  <!-- API Dialog -->
  <div v-if="showApiDialog" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="showApiDialog = false">
    <div class="bg-white dark:bg-slate-800 rounded-xl p-4 w-full max-w-md shadow-2xl dark:text-slate-100" @click.stop>
      <div class="flex justify-between items-center mb-4">
        <h3 class="text-sm font-semibold text-orange-500 dark:text-orange-400">
          {{ editingApiIndex >= 0 ? 'Edit API' : 'Add API' }}
        </h3>
        <button @click="showApiDialog = false" class="text-slate-400 hover:text-orange-500 transition-colors dark:hover:text-slate-300">
          <span class="material-symbols-outlined">close</span>
        </button>
      </div>

      <div class="space-y-3">
        <div class="grid grid-cols-2 gap-3">
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Name</label>
            <input
              v-model="editingApiData.name"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
              placeholder="API name"
            />
          </div>
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Description</label>
            <input
              v-model="editingApiData.description"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
              placeholder="Desc"
            />
          </div>
        </div>

        <div class="grid grid-cols-2 gap-3">
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Start State</label>
            <select
              v-model="editingApiData.startState"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
            >
              <option value="" hidden>Select</option>
              <option v-for="state in customTemplateForm.workingStates" :key="state.name" :value="state.name">
                {{ state.name }}
              </option>
            </select>
          </div>
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">End State</label>
            <select
              v-model="editingApiData.endState"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
            >
              <option value="" hidden>Select</option>
              <option v-for="state in customTemplateForm.workingStates" :key="state.name" :value="state.name">
                {{ state.name }}
              </option>
            </select>
          </div>
        </div>

        <div class="grid grid-cols-2 gap-3">
          <div>
            <label class="block text-xs font-medium text-slate-700 dark:text-slate-300 mb-1">Trigger</label>
            <select
              v-model="editingApiData.trigger"
              class="w-full px-3 py-2 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded-lg focus:ring-2 focus:ring-orange-500 focus:border-orange-500 transition-all dark:text-white text-sm"
            >
              <option value="user">User</option>
              <option value="auto">Auto</option>
              <option value="event">Event</option>
            </select>
          </div>
          <div class="flex items-center h-full pt-4">
            <label class="flex items-center gap-1.5 text-xs text-slate-700 dark:text-slate-300">
              <input
                type="checkbox"
                v-model="editingApiData.signal"
                class="w-3.5 h-3.5 text-orange-500 bg-slate-100 border-slate-300 rounded focus:ring-orange-500 dark:focus:ring-offset-slate-900 dark:bg-slate-700 dark:border-slate-600"
              />
               Signal
            </label>
          </div>
        </div>

        <!-- Assignments -->
        <div>
          <div class="flex items-center justify-between mb-1.5">
            <label class="text-xs font-medium text-slate-700 dark:text-slate-300">Assignments</label>
            <button
              @click="editingApiData.assignments.push({variableName: '', changeRate: ''})"
              class="text-[10px] text-orange-500 hover:text-orange-600 dark:text-orange-400 dark:hover:text-orange-300"
            >
              + Add
            </button>
          </div>
          <div class="space-y-1.5 max-h-24 overflow-y-auto">
            <div v-for="(assignment, index) in editingApiData.assignments" :key="index" class="flex items-center gap-2">
              <select
                v-model="assignment.variableName"
                class="flex-1 px-2 py-1.5 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded text-xs dark:text-white"
              >
                <option value="">Select</option>
                <option v-for="v in customTemplateForm.variables.filter(v => v.name.trim())" :key="v.name" :value="v.name">
                  {{ v.name }}
                </option>
              </select>
              <input
                v-model="assignment.changeRate"
                class="w-16 px-2 py-1.5 border border-slate-300 dark:border-slate-600 bg-white dark:bg-slate-900 rounded text-xs dark:text-white"
                placeholder="Rate"
              />
              <button
                @click="editingApiData.assignments.splice(index, 1)"
                class="p-1 text-red-400 hover:text-red-600 dark:text-red-500 dark:hover:text-red-400"
              >
                <span class="material-symbols-outlined text-xs">close</span>
              </button>
            </div>
          </div>
        </div>
      </div>

      <div class="flex justify-end space-x-2 mt-4">
        <button
          @click="showApiDialog = false"
          class="px-3 py-1.5 text-xs font-medium text-slate-700 bg-slate-100 border border-slate-200 rounded-lg hover:bg-slate-200 dark:bg-slate-700 dark:text-slate-300 dark:border-slate-600 dark:hover:bg-slate-600"
        >
          Cancel
        </button>
        <button
          @click="confirmSaveApi"
          class="px-3 py-1.5 text-xs font-medium text-white bg-orange-500 rounded-lg hover:bg-orange-600 transition-colors dark:bg-orange-600 dark:hover:bg-orange-700"
        >
          {{ editingApiIndex >= 0 ? 'Update' : 'Add' }}
        </button>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import {ref, reactive, watch, computed} from 'vue'
import {useI18n} from 'vue-i18n'
import {ElMessage} from 'element-plus'
import {Delete, ArrowRight, Connection, Coin, Setting, Platform} from '@element-plus/icons-vue'
import type {DeviceTemplate, DeviceManifest, InternalVariable} from '../types/device'
import {validateManifest} from '../utils/device'

const props = defineProps<{
  visible: boolean
}>()

const emit = defineEmits<{
  (e: 'update:visible', val: boolean): void
  (e: 'save', tpl: DeviceTemplate): void
}>()

const {t} = useI18n()

// === 模式切换 ===
const mode = ref<'form' | 'json'>('form')
const jsonStr = ref('')

// === 表单数据 (完全对应 DeviceManifest 结构) ===
const form = reactive<DeviceManifest>({
  Name: '',
  Description: '',
  Modes: [],
  ImpactedVariables: [],
  InternalVariables: [],
  InitState: '',
  WorkingStates: [],
  APIs: [],
  Transitions: []
})

// === 临时状态 ===
const tempMode = ref('')
const tempImpactedVar = ref('')

// === Internal Variable 弹窗状态 ===
const ivDialogVisible = ref(false)
const editingIvIndex = ref(-1) // -1 表示新增
// 临时编辑对象
const ivForm = reactive<InternalVariable>({
  Name: '', Description: '', IsInside: false, PublicVisible: true,
  Trust: 'trusted', Privacy: 'public', Values: [], LowerBound: undefined, UpperBound: undefined, NaturalChangeRate: ''
})
const tempIvValue = ref('') // 枚举值输入框

// === 计算属性 (用于下拉框选项) ===
const availableVariables = computed(() => {
  const impacted = form.ImpactedVariables || []
  const internal = form.InternalVariables.map(v => v.Name).filter(n => n)
  return [...impacted, ...internal]
})

const availableStates = computed(() => {
  return form.WorkingStates.map(s => s.Name).filter(n => n)
})

// === 监听与同步 ===
watch(() => props.visible, (val) => {
  if (val) {
    resetForm()
    syncFormToJson()
    mode.value = 'form'
  }
})

watch(mode, (newMode) => {
  if (newMode === 'json') syncFormToJson()
  else {
    try {
      const parsed = JSON.parse(jsonStr.value)
      // 简单合并，防止字段丢失
      Object.assign(form, {
        Name: '', Description: '', Modes: [], ImpactedVariables: [], InternalVariables: [],
        InitState: '', WorkingStates: [], APIs: [], Transitions: [],
        ...parsed
      })
    } catch (e) {
      ElMessage.warning(t('app.jsonParseError') || 'JSON 格式错误，无法切换回表单')
      mode.value = 'json'
    }
  }
})

const resetForm = () => {
  Object.assign(form, {
    Name: '', Description: '', Modes: [], ImpactedVariables: ['temperature'], InternalVariables: [],
    InitState: 'Off',
    WorkingStates: [
      {Name: 'Off', Description: 'Closed', Trust: 'trusted', Privacy: 'public', Invariant: 'true', Dynamics: []}
    ],
    APIs: [],
    Transitions: []
  })
}

const syncFormToJson = () => {
  jsonStr.value = JSON.stringify(form, null, 2)
}

// === 操作逻辑 ===

// Modes
const addMode = () => {
  if (tempMode.value) {
    form.Modes?.push(tempMode.value);
    tempMode.value = ''
  }
}
const removeMode = (i: number) => form.Modes?.splice(i, 1)

// Impacted Vars
const addImpactedVar = () => {
  if (tempImpactedVar.value) {
    form.ImpactedVariables.push(tempImpactedVar.value);
    tempImpactedVar.value = ''
  }
}
const removeImpactedVar = (i: number) => form.ImpactedVariables.splice(i, 1)

// Internal Vars
const openIvDialog = (index = -1) => {
  editingIvIndex.value = index
  if (index >= 0) {
    Object.assign(ivForm, JSON.parse(JSON.stringify(form.InternalVariables[index])))
  } else {
    // 重置默认值
    Object.assign(ivForm, {
      Name: '', Description: '', IsInside: false, PublicVisible: true,
      Trust: 'trusted', Privacy: 'public', Values: [], LowerBound: undefined, UpperBound: undefined
    })
  }
  ivDialogVisible.value = true
}
const saveInternalVar = () => {
  if (!ivForm.Name) return ElMessage.warning(t('app.inputVarName') || 'Variable Name is required')
  const newVar = JSON.parse(JSON.stringify(ivForm))
  if (editingIvIndex.value >= 0) form.InternalVariables[editingIvIndex.value] = newVar
  else form.InternalVariables.push(newVar)
  ivDialogVisible.value = false
}
const removeInternalVar = (i: number) => form.InternalVariables.splice(i, 1)
const addIvValue = () => {
  if (tempIvValue.value) {
    ivForm.Values = ivForm.Values || [];
    ivForm.Values.push(tempIvValue.value);
    tempIvValue.value = ''
  }
}
const removeIvValue = (i: number) => ivForm.Values?.splice(i, 1)

// States & Dynamics
const addState = () => form.WorkingStates.push({
  Name: 'NewState', Description: '', Trust: 'trusted', Privacy: 'public', Invariant: 'true', Dynamics: []
})
const removeState = (i: number) => form.WorkingStates.splice(i, 1)

const addDynamic = (stateIndex: number) => {
  const defaultVar = availableVariables.value[0] || ''
  form.WorkingStates[stateIndex].Dynamics.push({VariableName: defaultVar, ChangeRate: '0'})
}
const removeDynamic = (sIdx: number, dIdx: number) => form.WorkingStates[sIdx].Dynamics.splice(dIdx, 1)

// APIs
const addApi = () => form.APIs.push({
  Name: 'NewAPI', Description: '', Signal: true, StartState: '', EndState: '', Trigger: null, Assignments: []
})
const removeApi = (i: number) => form.APIs.splice(i, 1)

// Submit
const handleConfirm = () => {
  let finalManifest: DeviceManifest
  if (mode.value === 'form') {
    if (!form.Name.trim()) return ElMessage.warning(t('app.inputDeviceName') || 'Device Name is required')
    finalManifest = JSON.parse(JSON.stringify(form))
  } else {
    try {
      finalManifest = JSON.parse(jsonStr.value)
    } catch (e) {
      return ElMessage.error(t('app.jsonParseError') || 'JSON Syntax Error')
    }
  }

  const check = validateManifest(finalManifest)
  if (!check.valid) return ElMessage.error(check.msg)

  emit('save', {id: '', name: finalManifest.Name.replace(/ /g, '_'), manifest: finalManifest})
}
</script>

<template>
  <el-dialog
      :model-value="visible"
      @update:model-value="emit('update:visible', $event)"
      :title="t('app.addDeviceTemplate') || 'Add Device Template'"
      width="960px"
      class="iot-dialog"
      destroy-on-close
      append-to-body
      top="4vh"
  >
    <!-- Tabs -->
    <div class="dialog-tabs">
      <div class="tab-item" :class="{active: mode === 'form'}" @click="mode = 'form'">
        {{ t('app.basicMode') || 'Guided Mode' }}
      </div>
      <div class="tab-item" :class="{active: mode === 'json'}" @click="mode = 'json'">
        {{ t('app.jsonMode') || 'JSON Mode' }}
      </div>
    </div>

    <!-- Main Content -->
    <div class="dialog-scroll-content">
      <!-- FORM MODE -->
      <div v-show="mode === 'form'" class="form-layout">

        <!-- 1. Basic Info -->
        <div class="form-block">
          <div class="block-title">
            <el-icon>
              <Setting/>
            </el-icon>
            {{ t('app.basicInfo') || 'Basic Info' }}
          </div>
          <div class="grid-2">
            <el-form-item :label="t('app.deviceName') || 'Name'" required>
              <el-input v-model="form.Name"/>
            </el-form-item>
            <el-form-item :label="t('app.initState') || 'Init State'" required>
              <el-select v-model="form.InitState" placeholder="Select from States" style="width: 100%" filterable
                         allow-create>
                <el-option v-for="s in availableStates" :key="s" :label="s" :value="s"/>
              </el-select>
            </el-form-item>
          </div>
          <el-form-item :label="t('app.modes') || 'Modes'">
            <div class="tags-row">
              <el-tag v-for="(m, i) in form.Modes" :key="i" closable @close="removeMode(i)">{{ m }}</el-tag>
              <el-input v-model="tempMode" size="small" class="tag-input" placeholder="+ Mode" @keyup.enter="addMode"
                        @blur="addMode"/>
            </div>
          </el-form-item>
          <el-form-item :label="t('app.description') || 'Description'">
            <el-input v-model="form.Description" type="textarea" :rows="1"/>
          </el-form-item>
        </div>

        <!-- 2. Variables -->
        <div class="form-block">
          <div class="block-title">
            <el-icon>
              <Coin/>
            </el-icon>
            {{ t('app.variables') || 'Variables' }}
          </div>

          <el-form-item :label="t('app.impactedVariables') || 'Impacted (External)'">
            <div class="tags-row">
              <el-tag v-for="(v, i) in form.ImpactedVariables" :key="i" closable type="info"
                      @close="removeImpactedVar(i)">{{ v }}
              </el-tag>
              <el-input v-model="tempImpactedVar" size="small" class="tag-input" placeholder="+ Var"
                        @keyup.enter="addImpactedVar" @blur="addImpactedVar"/>
            </div>
          </el-form-item>

          <div class="sub-header">
            <span>{{ t('app.internalVariables') || 'Internal Variables' }}</span>
            <el-button link type="primary" size="small" @click="openIvDialog()">+ {{
                t('app.add') || 'Add'
              }}
            </el-button>
          </div>
          <div class="internal-vars-list">
            <div v-for="(iv, i) in form.InternalVariables" :key="i" class="iv-row">
              <span class="iv-name">{{ iv.Name }}</span>
              <el-tag size="small" :type="iv.Trust === 'trusted' ? 'success' : 'warning'">{{ iv.Trust }}</el-tag>
              <el-tag size="small" :type="iv.Privacy === 'private' ? 'danger' : 'info'">{{ iv.Privacy }}</el-tag>
              <span class="iv-extra" v-if="iv.Values && iv.Values.length">Enum: {{ iv.Values.length }}</span>
              <span class="iv-extra" v-else>[{{ iv.LowerBound ?? '?' }}, {{ iv.UpperBound ?? '?' }}]</span>
              <div class="spacer"></div>
              <el-button link type="primary" @click="openIvDialog(i)">
                <el-icon>
                  <Setting/>
                </el-icon>
              </el-button>
              <el-button link type="danger" @click="removeInternalVar(i)">
                <el-icon>
                  <Delete/>
                </el-icon>
              </el-button>
            </div>
            <div v-if="form.InternalVariables.length === 0" class="empty-hint">
              {{ t('app.noInternalVars') || 'No internal variables defined' }}
            </div>
          </div>
        </div>

        <!-- 3. Working States -->
        <div class="form-block">
          <div class="sub-header-lg">
            <div class="block-title mb-0">
              <el-icon>
                <Platform/>
              </el-icon>
              {{ t('app.workingStates') || 'Working States' }}
            </div>
            <el-button link type="primary" @click="addState">+ {{ t('app.addState') || 'Add State' }}</el-button>
          </div>

          <div class="cards-grid">
            <div v-for="(s, i) in form.WorkingStates" :key="i" class="state-card">
              <div class="state-head">
                <el-input v-model="s.Name" size="small" placeholder="State Name" class="state-name-input"/>
                <el-button link type="danger" @click="removeState(i)">
                  <el-icon>
                    <Delete/>
                  </el-icon>
                </el-button>
              </div>
              <div class="state-props">
                <el-select v-model="s.Trust" size="small" style="width: 90px">
                  <el-option value="trusted"/>
                  <el-option value="untrusted"/>
                </el-select>
                <el-select v-model="s.Privacy" size="small" style="width: 90px">
                  <el-option value="public"/>
                  <el-option value="private"/>
                </el-select>
              </div>
              <el-input v-model="s.Description" size="small" :placeholder="t('app.description') || 'Description'"
                        class="my-1"/>
              <div class="mini-label">Invariant:
                <el-input v-model="s.Invariant" size="small" style="width: 140px"/>
              </div>

              <div class="dynamics-section">
                <div class="dyn-head">
                  <span>Dynamics</span>
                  <el-button link type="primary" size="small" @click="addDynamic(i)">+</el-button>
                </div>
                <div v-for="(dyn, di) in s.Dynamics" :key="di" class="dyn-row">
                  <!-- Variable Select -->
                  <el-select v-model="dyn.VariableName" size="small" placeholder="Var" style="flex: 1">
                    <el-option v-for="v in availableVariables" :key="v" :label="v" :value="v"/>
                  </el-select>
                  <span>=</span>
                  <el-input v-model="dyn.ChangeRate" size="small" placeholder="Rate" style="width: 60px"/>
                  <el-button link type="danger" size="small" @click="removeDynamic(i, di)">×</el-button>
                </div>
              </div>
            </div>
          </div>
        </div>

        <!-- 4. APIs -->
        <div class="form-block">
          <div class="sub-header-lg">
            <div class="block-title mb-0">
              <el-icon>
                <Connection/>
              </el-icon>
              {{ t('app.deviceApis') || 'APIs' }}
            </div>
            <el-button link type="primary" @click="addApi">+ {{ t('app.addApi') || 'Add API' }}</el-button>
          </div>
          <div class="api-list">
            <div v-for="(api, i) in form.APIs" :key="i" class="api-item">
              <div class="api-main">
                <div class="api-row-1">
                  <el-input v-model="api.Name" placeholder="API Name" style="width: 180px; font-weight: 600"/>
                  <el-checkbox v-model="api.Signal" :label="t('app.signal') || 'Signal'" size="small"/>
                  <el-input v-model="api.Description" :placeholder="t('app.description') || 'Description'"
                            style="flex: 1"/>
                </div>
                <div class="api-row-2">
                  <span class="flow-lbl">Transition:</span>
                  <el-select v-model="api.StartState" size="small" placeholder="Any" style="width: 130px" clearable>
                    <el-option v-for="s in availableStates" :key="s" :label="s" :value="s"/>
                  </el-select>
                  <el-icon class="arrow">
                    <ArrowRight/>
                  </el-icon>
                  <el-select v-model="api.EndState" size="small" placeholder="End" style="width: 130px">
                    <el-option v-for="s in availableStates" :key="s" :label="s" :value="s"/>
                  </el-select>
                </div>
              </div>
              <el-button link type="danger" @click="removeApi(i)" class="del-btn">
                <el-icon>
                  <Delete/>
                </el-icon>
              </el-button>
            </div>
          </div>
        </div>

      </div>

      <!-- JSON MODE -->
      <div v-show="mode === 'json'" class="json-layout">
        <el-input v-model="jsonStr" type="textarea" :rows="25" class="json-editor" spellcheck="false"/>
      </div>
    </div>

    <template #footer>
      <el-button @click="emit('update:visible', false)">{{ t('app.cancel') }}</el-button>
      <el-button type="primary" @click="handleConfirm">{{ t('app.save') }}</el-button>
    </template>

    <!-- Internal Variable Dialog -->
    <el-dialog v-model="ivDialogVisible" :title="t('app.editInternalVar') || 'Edit Internal Variable'" width="400px"
               append-to-body>
      <el-form :model="ivForm" label-position="top">
        <el-form-item :label="t('app.varName') || 'Name'" required>
          <el-input v-model="ivForm.Name"/>
        </el-form-item>
        <div class="grid-2">
          <el-form-item :label="t('app.trust') || 'Trust'">
            <el-select v-model="ivForm.Trust">
              <el-option value="trusted"/>
              <el-option value="untrusted"/>
            </el-select>
          </el-form-item>
          <el-form-item :label="t('app.privacy') || 'Privacy'">
            <el-select v-model="ivForm.Privacy">
              <el-option value="public"/>
              <el-option value="private"/>
            </el-select>
          </el-form-item>
        </div>
        <div class="grid-2">
          <el-form-item :label="t('app.isInside') || 'Is Inside'">
            <el-switch v-model="ivForm.IsInside"/>
          </el-form-item>
          <el-form-item :label="t('app.publicVisible') || 'Public Visible'">
            <el-switch v-model="ivForm.PublicVisible"/>
          </el-form-item>
        </div>
        <el-divider content-position="left">Type Constraints</el-divider>
        <el-tabs type="border-card" class="mini-tabs">
          <el-tab-pane label="Numeric">
            <div class="grid-2">
              <el-form-item label="Min">
                <el-input-number v-model="ivForm.LowerBound"/>
              </el-form-item>
              <el-form-item label="Max">
                <el-input-number v-model="ivForm.UpperBound"/>
              </el-form-item>
            </div>
            <el-form-item label="Rate">
              <el-input v-model="ivForm.NaturalChangeRate" placeholder="[-1, 1]"/>
            </el-form-item>
          </el-tab-pane>
          <el-tab-pane label="Enum">
            <div class="tags-row">
              <el-tag v-for="(v, i) in ivForm.Values" :key="i" closable @close="removeIvValue(i)">{{ v }}</el-tag>
              <el-input v-model="tempIvValue" size="small" class="tag-input" placeholder="+ Val"
                        @keyup.enter="addIvValue" @blur="addIvValue"/>
            </div>
          </el-tab-pane>
        </el-tabs>
      </el-form>
      <template #footer>
        <el-button @click="ivDialogVisible = false">{{ t('app.cancel') }}</el-button>
        <el-button type="primary" @click="saveInternalVar">{{ t('app.save') }}</el-button>
      </template>
    </el-dialog>
  </el-dialog>
</template>

<style scoped>
/* Scoped vars for consistent light theme */
.iot-dialog {
  --el-dialog-bg-color: #fff;
  --el-text-color-primary: #333;
  --el-border-color-lighter: #ebeef5;
}

.dialog-tabs {
  display: flex;
  border-bottom: 1px solid #eee;
  margin: -10px 0 16px;
}

.tab-item {
  padding: 8px 16px;
  cursor: pointer;
  color: #666;
  border-bottom: 2px solid transparent;
  transition: all 0.2s;
}

.tab-item.active {
  color: var(--iot-color-edge);
  border-bottom-color: var(--iot-color-edge);
  font-weight: 600;
}

.dialog-scroll-content {
  height: 65vh;
  overflow-y: auto;
  padding-right: 8px;
}

.form-layout {
  display: flex;
  flex-direction: column;
  gap: 16px;
}

.form-block {
  background: #fcfcfc;
  border: 1px solid #ebeef5;
  border-radius: 8px;
  padding: 16px;
}

.block-title {
  font-size: 14px;
  font-weight: 600;
  color: #303133;
  margin-bottom: 12px;
  display: flex;
  align-items: center;
  gap: 6px;
}

.mb-0 {
  margin-bottom: 0;
}

.sub-header-lg {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: 12px;
}

.grid-2 {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 16px;
}

.tags-row {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
  padding: 4px;
  border: 1px solid #dcdfe6;
  border-radius: 4px;
  background: #fff;
  min-height: 32px;
}

.tag-input {
  width: 80px;
  border: none;
}

:deep(.tag-input .el-input__wrapper) {
  box-shadow: none !important;
  padding: 0 4px;
}

.sub-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin: 12px 0 8px;
  font-size: 13px;
  font-weight: 500;
  color: #606266;
}

.internal-vars-list {
  display: flex;
  flex-direction: column;
  gap: 6px;
}

.iv-row {
  display: flex;
  align-items: center;
  gap: 8px;
  background: #fff;
  padding: 6px 10px;
  border: 1px solid #ebeef5;
  border-radius: 4px;
  font-size: 13px;
}

.iv-name {
  font-weight: 600;
  width: 120px;
  overflow: hidden;
  text-overflow: ellipsis;
}

.iv-extra {
  color: #909399;
  font-size: 12px;
  margin-left: 8px;
}

.spacer {
  flex: 1;
}

.empty-hint {
  text-align: center;
  color: #c0c4cc;
  font-size: 12px;
  padding: 4px;
}

.cards-grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(260px, 1fr));
  gap: 12px;
}

.state-card {
  background: #fff;
  border: 1px solid #e4e7ed;
  border-radius: 6px;
  padding: 10px;
  display: flex;
  flex-direction: column;
  gap: 8px;
  box-shadow: 0 1px 3px rgba(0, 0, 0, 0.04);
}

.state-head {
  display: flex;
  justify-content: space-between;
  align-items: center;
}

.state-name-input {
  width: 120px;
  font-weight: 600;
}

.state-props {
  display: flex;
  gap: 6px;
}

.my-1 {
  margin: 4px 0;
}

.mini-label {
  font-size: 12px;
  color: #909399;
  display: flex;
  align-items: center;
  gap: 4px;
}

.dynamics-section {
  background: #f5f7fa;
  padding: 6px;
  border-radius: 4px;
  margin-top: 4px;
}

.dyn-head {
  display: flex;
  justify-content: space-between;
  font-size: 11px;
  color: #909399;
  margin-bottom: 4px;
}

.dyn-row {
  display: flex;
  align-items: center;
  gap: 4px;
  margin-bottom: 4px;
}

.api-list {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.api-item {
  background: #fff;
  border: 1px solid #ebeef5;
  border-radius: 6px;
  padding: 10px;
  display: flex;
  align-items: flex-start;
  gap: 10px;
}

.api-main {
  flex: 1;
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.api-row-1 {
  display: flex;
  align-items: center;
  gap: 8px;
}

.api-row-2 {
  display: flex;
  align-items: center;
  gap: 8px;
  background: #f5f7fa;
  padding: 6px 10px;
  border-radius: 4px;
  font-size: 13px;
  color: #606266;
}

.flow-lbl {
  font-size: 12px;
  color: #909399;
}

.arrow {
  color: #c0c4cc;
  font-size: 12px;
}

.del-btn {
  margin-top: 4px;
}

.json-editor :deep(.el-textarea__inner) {
  font-family: monospace;
  font-size: 12px;
  background: #f5f7fa;
  color: #333;
}

.mini-tabs {
  margin-top: 10px;
}
</style>
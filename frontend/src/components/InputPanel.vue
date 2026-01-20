<script setup lang="ts">
import {ref, reactive, computed} from 'vue'
import {useI18n} from 'vue-i18n'
import {List, Picture, Plus, Close} from '@element-plus/icons-vue'
import {ElMessage} from "element-plus"

import type {DeviceTemplate} from '../types/device'
import type {DeviceNode} from '../types/node'
import type {RuleForm} from "../types/rule"
import type {
  SpecTemplate,
  SpecForm,
  SpecCondition,
  SpecTemplateId
} from '../types/spec'

import {
  createEmptyCondition,
  getSpecMode,
  getTargetOptions,
  resolveTargetTypeByKey,
  getRelationOptions,
  getValueOptions
} from '../utils/spec'

const props = defineProps<{
  deviceTemplates: DeviceTemplate[]
  nodes: DeviceNode[]
  specTemplates: SpecTemplate[]
  getTemplateInitIcon: (tpl: DeviceTemplate) => string
  active: string[]
}>()

const emit = defineEmits<{
  (e: 'create-device', tpl: DeviceTemplate): void
  (e: 'add-rule', payload: RuleForm): void
  (e: 'add-spec', payload: {
    templateId: SpecTemplateId | ''
    mode: 'single' | 'ifThen'
    aConditions: SpecCondition[]
    ifConditions: SpecCondition[]
    thenConditions: SpecCondition[]
  }): void
  (e: 'device-drag-start', tpl: DeviceTemplate): void
  (e: 'device-drag-end'): void
  (e: 'update:active', value: string[]): void
  // [Modified] 只需要抛出“打开添加对话框”的信号，不需要传 payload
  (e: 'open-add-template-dialog'): void
}>()

const {t} = useI18n()

const collapseActive = computed({
  get: () => props.active,
  set: (val: string[]) => emit('update:active', val)
})

/* ========= 设备列表 ========= */

const deviceViewMode = ref<'list' | 'icon'>('list')
const deviceKeyword = ref('')

const filteredDevices = computed(() => {
  if (!deviceKeyword.value) return props.deviceTemplates
  const kw = deviceKeyword.value.toLowerCase()
  return props.deviceTemplates.filter(d => d.manifest.Name.toLowerCase().includes(kw))
})

const onSelectDevice = (tpl: DeviceTemplate) => {
  emit('create-device', tpl)
}

/* ========= 交互逻辑 ========= */
const handleOpenAddDialog = () => {
  emit('open-add-template-dialog')
}

/* ========= IFTTT 规则（每个源单独一行，含 API） ========= */
const ruleForm = reactive<RuleForm>({sources: [{ fromId: '', fromApi: '' }], toId: '', toApi: ''})

const getFromApisFor = (source: { fromId: string; fromApi: string }) => {
  if (!source || !source.fromId) return []
  const n = props.nodes.find(n => n.id === source.fromId)
  if (!n) return []
  const tpl = props.deviceTemplates.find(t => t.manifest.Name === n.templateName)
  return tpl ? tpl.manifest.APIs : []
}

const apiPlaceholder = computed(() => {
  const v = t('app.api')
  // 如果没有翻译，t 会返回 key，例如 "app.api"，则回退到 'API'
  return (typeof v === 'string' && v.includes('app.api')) ? 'API' : v
})

const getDeviceDisplayName = (node: DeviceNode) => {
  // 优先使用label，如果没有则使用模板名称
  if (node.label && node.label.trim()) {
    return node.label
  }
  // 如果label为空，查找对应的设备模板名称
  const template = props.deviceTemplates.find(t => t.manifest.Name === node.templateName)
  return template ? template.manifest.Name : node.templateName
}

const addSourceRow = () => {
  ruleForm.sources.push({ fromId: '', fromApi: '' })
}

const removeSourceRow = (index: number) => {
  if (ruleForm.sources.length === 1) return
  ruleForm.sources.splice(index, 1)
}
const toApis = computed(() => {
  const n = props.nodes.find(n => n.id === ruleForm.toId)
  if (!n) return []
  const tpl = props.deviceTemplates.find(t => t.manifest.Name === n.templateName)
  return tpl ? tpl.manifest.APIs : []
})
const onAddRule = () => {
  emit('add-rule', {...ruleForm})
  ruleForm.sources = [{ fromId: '', fromApi: '' }]
  ruleForm.toId = ''
  ruleForm.toApi = ''
}

/* ========= 规约输入 (保持不变) ========= */
const specForm = reactive<SpecForm>({
  templateId: '',
  aConditions: [createEmptyCondition('a')],
  ifConditions: [createEmptyCondition('if')],
  thenConditions: [createEmptyCondition('then')]
})
const specMode = computed<'single' | 'ifThen' | null>(() => getSpecMode(specForm.templateId))
const getTargetOptionsForCond = (cond: SpecCondition) => getTargetOptions(cond, props.nodes, props.deviceTemplates)
const getRelationOptionsForCond = (cond: SpecCondition) => getRelationOptions(cond)
const getValueOptionsForCond = (cond: SpecCondition) => getValueOptions(cond, props.nodes, props.deviceTemplates)

const onConditionDeviceChange = (cond: SpecCondition) => {
  const node = props.nodes.find(n => n.id === cond.deviceId)
  cond.deviceLabel = node ? node.label : ''
  cond.key = '';
  cond.targetType = 'state';
  cond.relation = 'in';
  cond.value = ''
}
const onConditionKeyChange = (cond: SpecCondition, value: string) => {
  cond.key = value
  cond.targetType = resolveTargetTypeByKey(cond, value, props.nodes, props.deviceTemplates)
  const rels = getRelationOptionsForCond(cond)
  cond.relation = rels[0];
  cond.value = ''
}
const addACondition = () => {
  specForm.aConditions.push(createEmptyCondition('a'))
}
const removeACondition = (id: string) => {
  if (specForm.aConditions.length === 1) return;
  specForm.aConditions = specForm.aConditions.filter(c => c.id !== id)
}
const addIfCondition = () => {
  specForm.ifConditions.push(createEmptyCondition('if'))
}
const removeIfCondition = (id: string) => {
  if (specForm.ifConditions.length === 1) return;
  specForm.ifConditions = specForm.ifConditions.filter(c => c.id !== id)
}
const addThenCondition = () => {
  specForm.thenConditions.push(createEmptyCondition('then'))
}
const removeThenCondition = (id: string) => {
  if (specForm.thenConditions.length === 1) return;
  specForm.thenConditions = specForm.thenConditions.filter(c => c.id !== id)
}

const onAddSpec = () => {
  if (!specMode.value) {
    ElMessage.warning(t('app.selectTemplate') || '请选择规约模板');
    return
  }
  emit('add-spec', {
    templateId: specForm.templateId, mode: specMode.value,
    aConditions: specMode.value === 'single' ? specForm.aConditions : [],
    ifConditions: specMode.value === 'ifThen' ? specForm.ifConditions : [],
    thenConditions: specMode.value === 'ifThen' ? specForm.thenConditions : []
  })
  specForm.templateId = '';
  specForm.aConditions = [createEmptyCondition('a')];
  specForm.ifConditions = [createEmptyCondition('if')];
  specForm.thenConditions = [createEmptyCondition('then')]
}
</script>

<template>
  <el-collapse v-model="collapseActive" class="panel-collapse" expand-icon-position="left">
    <!-- 设备列表 -->
    <el-collapse-item name="devices">
      <template #title>
        <div class="collapse-title-row">
          <span class="card-subtitle no-wrap-title" :title="t('app.devices')">{{ t('app.devices') }}</span>
          <div class="card-header-actions">
            <el-button link type="primary" @click.stop="handleOpenAddDialog"
                       :title="t('app.addDeviceTemplate') || '添加新设备'">
              <el-icon>
                <Plus/>
              </el-icon>
            </el-button>
            <el-divider direction="vertical"/>
            <el-button link :type="deviceViewMode === 'list' ? 'primary' : 'default'"
                       @click.stop="deviceViewMode = 'list'">
              <el-icon>
                <List/>
              </el-icon>
            </el-button>
            <el-button link :type="deviceViewMode === 'icon' ? 'primary' : 'default'"
                       @click.stop="deviceViewMode = 'icon'">
              <el-icon>
                <Picture/>
              </el-icon>
            </el-button>
          </div>
        </div>
      </template>

      <el-input v-model="deviceKeyword" size="default" :placeholder="t('app.searchDevice')" clearable
                class="device-search"/>

      <el-scrollbar height="260">
        <div v-if="deviceViewMode === 'list'">
          <div v-for="d in filteredDevices" :key="d.id" class="device-item device-item--list" draggable="true"
               @dragstart="emit('device-drag-start', d)" @dragend="emit('device-drag-end')" @click="onSelectDevice(d)">
            {{ d.manifest.Name }}
          </div>
        </div>
        <div v-else class="device-icon-grid">
          <div v-for="d in filteredDevices" :key="d.id" class="device-item device-item--icon" draggable="true"
               @dragstart="emit('device-drag-start', d)" @dragend="emit('device-drag-end')" @click="onSelectDevice(d)">
            <img class="device-thumb" :src="getTemplateInitIcon(d)" :alt="d.manifest.Name" draggable="false"/>
            <div class="device-thumb-label">{{ d.manifest.Name }}</div>
          </div>
        </div>
      </el-scrollbar>
    </el-collapse-item>

    <!-- IFTTT 规则 (保持不变) -->
    <el-collapse-item name="rules">
      <template #title>
        <div class="collapse-title-row"><span class="card-subtitle no-wrap-title"
                                              :title="t('app.rules')">{{ t('app.rules') }}</span></div>
      </template>
      <div class="ipt-rule-block">
        <div class="ipt-row ipt-sources-block">
          <span class="ipt-label">{{ t('app.sourceDevice') }}</span>
          <div style="flex:1; display:flex; flex-direction:column; gap:8px;">
            <div v-for="(s, idx) in ruleForm.sources" :key="idx" class="source-row">
              <el-select v-model="s.fromId" class="ipt-select" :placeholder="t('app.select')" @change="() => { s.fromApi = '' }">
                <el-option v-for="n in nodes" :key="n.id" :label="getDeviceDisplayName(n)" :value="n.id"/>
              </el-select>
              <el-select v-model="s.fromApi" class="ipt-select ipt-select-api" :placeholder="apiPlaceholder">
                <el-option v-for="api in getFromApisFor(s)" :key="api.Name" :label="api.Name" :value="api.Name"/>
              </el-select>
              <el-button type="text" class="remove-source-btn" :disabled="ruleForm.sources.length === 1" @click.prevent="removeSourceRow(idx)" title="移除此源">
                <el-icon><Close/></el-icon>
              </el-button>
              <el-button v-if="idx === ruleForm.sources.length - 1" type="text" class="add-source-inline" @click.prevent="addSourceRow" title="添加源">
                <el-icon><Plus/></el-icon>
              </el-button>
            </div>
          </div>
        </div>
        <div class="ipt-row"><span class="ipt-label">{{ t('app.targetDevice') }}</span>
          <el-select v-model="ruleForm.toId" class="ipt-select" :placeholder="t('app.select')">
            <el-option v-for="n in nodes" :key="n.id" :label="getDeviceDisplayName(n)" :value="n.id"/>
          </el-select>
        </div>
        <div class="ipt-row"><span class="ipt-label">{{ t('app.targetApi') }}</span>
          <el-select v-model="ruleForm.toApi" class="ipt-select" :placeholder="t('app.select')">
            <el-option v-for="api in toApis" :key="api.Name" :label="api.Name" :value="api.Name"/>
          </el-select>
        </div>
        <div class="ipt-row ipt-row-actions"><span class="ipt-label"></span>
          <el-button type="primary" size="default" @click="onAddRule">{{ t('app.addRule') }}</el-button>
        </div>
      </div>
    </el-collapse-item>

    <!-- 规约输入 (保持不变) -->
    <el-collapse-item name="specs">
      <template #title>
        <div class="collapse-title-row"><span class="card-subtitle no-wrap-title"
                                              :title="t('app.specifications')">{{ t('app.specifications') }}</span>
        </div>
      </template>
      <div class="spec-form">
        <div class="ipt-row"><span class="ipt-label">{{ t('app.specTemplate') }}</span>
          <el-select v-model="specForm.templateId" class="ipt-select" filterable :placeholder="t('app.select')">
            <el-option v-for="tpl in specTemplates" :key="tpl.id" :label="tpl.label" :value="tpl.id"/>
          </el-select>
        </div>
      </div>
      <div v-if="specMode === 'single'" class="spec-section">
        <div class="spec-section-header"><span class="spec-section-title">A</span>
          <el-button link size="default" @click="addACondition">+ {{ t('app.addACondition') }}</el-button>
        </div>
        <div v-for="cond in specForm.aConditions" :key="cond.id" class="spec-condition-row">
          <el-select v-model="cond.deviceId" size="default" class="spec-cond-device"
                     @change="onConditionDeviceChange(cond)" :placeholder="t('app.select')">
            <el-option v-for="n in nodes" :key="n.id" :label="getDeviceDisplayName(n)" :value="n.id"/>
          </el-select>
          <el-select v-if="cond.deviceId" v-model="cond.key" size="default" class="spec-cond-target"
                     @change="onConditionKeyChange(cond, $event)" :placeholder="t('app.select')">
            <el-option v-for="opt in getTargetOptionsForCond(cond)" :key="opt.value" :label="opt.label"
                       :value="opt.value"/>
          </el-select>
          <template v-if="cond.deviceId && cond.targetType !== 'api' && cond.key">
            <el-select v-model="cond.relation" size="default" class="spec-cond-relation" :placeholder="t('app.select')">
              <el-option v-for="rel in getRelationOptionsForCond(cond)" :key="rel" :label="rel" :value="rel"/>
            </el-select>
            <el-input v-if="cond.targetType === 'variable'" v-model="cond.value" size="default"
                      class="spec-cond-value"/>
            <el-select v-else v-model="cond.value" size="default" class="spec-cond-value" :placeholder="t('app.select')">
              <el-option v-for="v in getValueOptionsForCond(cond)" :key="v" :label="v" :value="v"/>
            </el-select>
          </template>
          <el-button link type="danger" size="default" @click="removeACondition(cond.id)">×</el-button>
        </div>
      </div>
      <div v-else-if="specMode === 'ifThen'">
        <div class="spec-section">
          <div class="spec-section-header"><span class="spec-section-title">IF</span>
            <el-button link size="default" @click="addIfCondition">+ {{ t('app.addIfCondition') }}</el-button>
          </div>
          <div v-for="cond in specForm.ifConditions" :key="cond.id" class="spec-condition-row">
            <el-select v-model="cond.deviceId" size="default" class="spec-cond-device"
                       @change="onConditionDeviceChange(cond)" :placeholder="t('app.select')">
              <el-option v-for="n in nodes" :key="n.id" :label="getDeviceDisplayName(n)" :value="n.id"/>
            </el-select>
            <el-select v-if="cond.deviceId" v-model="cond.key" size="default" class="spec-cond-target"
                       @change="onConditionKeyChange(cond, $event)" :placeholder="t('app.select')">
              <el-option v-for="opt in getTargetOptionsForCond(cond)" :key="opt.value" :label="opt.label"
                         :value="opt.value"/>
            </el-select>
            <template v-if="cond.deviceId && cond.targetType !== 'api' && cond.key">
              <el-select v-model="cond.relation" size="default" class="spec-cond-relation" :placeholder="t('app.select')">
                <el-option v-for="rel in getRelationOptionsForCond(cond)" :key="rel" :label="rel" :value="rel"/>
              </el-select>
              <el-input v-if="cond.targetType === 'variable'" v-model="cond.value" size="default"
                        class="spec-cond-value"/>
              <el-select v-else v-model="cond.value" size="default" class="spec-cond-value" :placeholder="t('app.select')">
                <el-option v-for="v in getValueOptionsForCond(cond)" :key="v" :label="v" :value="v"/>
              </el-select>
            </template>
            <el-button link type="danger" size="default" @click="removeIfCondition(cond.id)">×</el-button>
          </div>
        </div>
        <div class="spec-section">
          <div class="spec-section-header"><span class="spec-section-title">THEN</span>
            <el-button link size="default" @click="addThenCondition">+ {{ t('app.addThenCondition') }}</el-button>
          </div>
          <div v-for="cond in specForm.thenConditions" :key="cond.id" class="spec-condition-row">
            <el-select v-model="cond.deviceId" size="default" class="spec-cond-device"
                       @change="onConditionDeviceChange(cond)" :placeholder="t('app.select')">
              <el-option v-for="n in nodes" :key="n.id" :label="getDeviceDisplayName(n)" :value="n.id"/>
            </el-select>
            <el-select v-if="cond.deviceId" v-model="cond.key" size="default" class="spec-cond-target"
                       @change="onConditionKeyChange(cond, $event)" :placeholder="t('app.select')">
              <el-option v-for="opt in getTargetOptionsForCond(cond)" :key="opt.value" :label="opt.label"
                         :value="opt.value"/>
            </el-select>
            <template v-if="cond.deviceId && cond.targetType !== 'api' && cond.key">
              <el-select v-model="cond.relation" size="default" class="spec-cond-relation" :placeholder="t('app.select')">
                <el-option v-for="rel in getRelationOptionsForCond(cond)" :key="rel" :label="rel" :value="rel"/>
              </el-select>
              <el-input v-if="cond.targetType === 'variable'" v-model="cond.value" size="default"
                        class="spec-cond-value"/>
              <el-select v-else v-model="cond.value" size="default" class="spec-cond-value" :placeholder="t('app.select')">
                <el-option v-for="v in getValueOptionsForCond(cond)" :key="v" :label="v" :value="v"/>
              </el-select>
            </template>
            <el-button link type="danger" size="default" @click="removeThenCondition(cond.id)">×</el-button>
          </div>
        </div>
      </div>
      <el-button type="primary" size="default" class="spec-add-button" @click="onAddSpec">{{
          t('app.addSpec')
        }}
      </el-button>
    </el-collapse-item>
  </el-collapse>
</template>

<!-- Removed the local dialog entirely -->

<style scoped>
/* (Styles maintained as previously optimized) */
.collapse-title-row {
  display: flex;
  align-items: center;
  justify-content: space-between;
  width: 100%;
  min-width: 0;
}

.no-wrap-title {
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  flex: 1;
  min-width: 0;
  margin-right: 8px;
}

.card-header-actions {
  display: flex;
  align-items: center;
  flex-shrink: 0;
}

.device-search {
  margin-bottom: var(--iot-space-sm);
}

.device-item {
  background: var(--iot-color-device-item-bg);
  border-radius: var(--iot-radius-input);
  margin-bottom: var(--iot-space-sm);
  padding: var(--iot-space-sm) var(--iot-space-md);
  cursor: grab;
  transition: box-shadow 0.14s ease-out, background 0.14s ease-out, transform 0.12s ease-out;
  border: 1px solid var(--iot-color-device-item-border);
  color: var(--iot-color-device-item-text);
  font-size: var(--iot-font-subtitle);
}

.device-item:hover {
  background: var(--iot-color-device-item-bg-hover);
  box-shadow: var(--iot-shadow-device-hover);
  transform: translateY(-1px);
}

.device-icon-grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(6.25rem, 1fr));
  gap: var(--iot-space-sm);
}

.device-item--icon {
  text-align: center;
}

.device-thumb {
  width: var(--iot-thumb-width);
  height: var(--iot-thumb-height);
  object-fit: contain;
  margin-bottom: var(--iot-space-2xs);
}

.device-thumb-label {
  font-size: var(--iot-font-caption);
  word-break: break-all;
}

.ipt-rule-block {
  margin-top: var(--iot-space-xs);
}

.ipt-row {
  display: grid;
  grid-template-columns: max-content 1fr;
  column-gap: var(--iot-space-sm);
  align-items: center;
  margin-bottom: var(--iot-space-sm);
  overflow: visible;
}

.ipt-row-actions {
  margin-top: var(--iot-space-xs);
}

.ipt-label {
  min-width: 7.5rem;
  white-space: nowrap;
  overflow: visible;
  flex-shrink: 0;
  font-size: var(--iot-font-base);
  color: var(--iot-color-text);
}

.ipt-select {
  width: 100%;
}

/* ========== Source row styling ========== */
.ipt-sources-block .source-row {
  display: flex;
  gap: 6px;
  align-items: center;
}
.ipt-sources-block .source-row .ipt-select {
  flex: 1 1 0;
  min-width: 0; /* allow flex children to shrink */
}
.ipt-sources-block .source-row .ipt-select:first-child {
  flex: 0 0 9rem;
  max-width: 6rem;
}
.ipt-sources-block .ipt-select-api {
  flex: 0 0 12rem;
  min-width: 12rem;
}
.ipt-sources-block .remove-source-btn {
  width: 18px;
  height: 18px;
  padding: 0;
  font-size: 12px;
  line-height: 1;
  border-radius: 4px;
  color: var(--iot-color-danger);
  display: inline-flex;
  align-items: center;
  justify-content: center;
  margin-left: 2px;
}
.ipt-sources-block .remove-source-btn[disabled] {
  opacity: 0.45;
  cursor: not-allowed;
}
.ipt-sources-block .el-button[type="primary"][size="mini"] {
  align-self: flex-end;
}

.add-source-inline {
  width: 20px;
  height: 20px;
  padding: 0;
  margin-left: 2px;
  color: var(--iot-color-brand);
}
.ipt-row.ipt-sources-block {
  align-items: flex-start; /* label aligns to top of selects */
}


.spec-form {
  margin-top: var(--iot-space-2xs);
  margin-bottom: var(--iot-space-sm);
}

.spec-section {
  margin: var(--iot-space-sm) 0 var(--iot-space-xs);
  padding: var(--iot-space-sm);
  border-radius: var(--iot-radius-input);
  background: linear-gradient(135deg, var(--iot-color-spec-bg), var(--iot-color-spec-bg-strong));
  box-shadow: 0 0 0 1px var(--iot-color-spec-border);
}

.spec-section-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  margin-bottom: var(--iot-space-xs);
}

.spec-section-title {
  font-size: var(--iot-font-caption);
  font-weight: 600;
  color: var(--iot-color-text-muted);
  letter-spacing: 0.08em;
  text-transform: uppercase;
}

.spec-condition-row {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: var(--iot-space-xs);
}

.spec-condition-row + .spec-condition-row {
  margin-top: var(--iot-space-sm);
  padding-top: var(--iot-space-sm);
  border-top: 2px dashed var(--iot-color-spec-border);
}

.spec-add-button {
  margin-top: var(--iot-space-sm);
}

.spec-cond-device, .spec-cond-target, .spec-cond-relation, .spec-cond-value {
  min-width: 7rem;
  flex: 1 1 7rem;
}

.spec-cond-device {
  flex: 1.2 1 8rem;
}

.spec-cond-target {
  flex: 1 1 7rem;
}

.spec-cond-relation {
  flex: 0.8 1 6rem;
}

.spec-cond-value {
  flex: 1 1 7rem;
}

:deep(.el-form-item__label) {
  white-space: nowrap;
}
</style>
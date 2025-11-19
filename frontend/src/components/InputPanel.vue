<script setup lang="ts">
import { ref, reactive, computed } from 'vue'
import { useI18n } from 'vue-i18n'
import { List, Picture } from '@element-plus/icons-vue'

import type { DeviceTemplate } from '../types/device'
import type {
  DeviceNode,
  RuleForm,
  SpecTemplate,
  SpecForm,
  SpecCondition,
  SpecTemplateId
} from '../types/board'

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
  // 让父组件传入一个函数用于获取初始图标
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
}>()

const { t } = useI18n()

/* ========= 设备列表 ========= */

const deviceViewMode = ref<'list' | 'icon'>('list')
const deviceKeyword = ref('')

const filteredDevices = computed(() => {
  if (!deviceKeyword.value) return props.deviceTemplates
  const kw = deviceKeyword.value.toLowerCase()
  return props.deviceTemplates.filter(d => d.name.toLowerCase().includes(kw))
})

const collapseActive = computed({
  get: () => props.active,
  set: (val: string[]) => emit('update:active', val)
})

const onSelectDevice = (tpl: DeviceTemplate) => {
  emit('create-device', tpl)
}

/* ========= IFTTT 规则 ========= */

const ruleForm = reactive<RuleForm>({
  fromId: '',
  fromApi: '',
  toId: '',
  toApi: ''
})

const fromApis = computed(() => {
  const n = props.nodes.find(n => n.id === ruleForm.fromId)
  if (!n) return []
  const tpl = props.deviceTemplates.find(t => t.name === n.templateName)
  return tpl ? tpl.manifest.APIs : []
})

const toApis = computed(() => {
  const n = props.nodes.find(n => n.id === ruleForm.toId)
  if (!n) return []
  const tpl = props.deviceTemplates.find(t => t.name === n.templateName)
  return tpl ? tpl.manifest.APIs : []
})

const onAddRule = () => {
  emit('add-rule', { ...ruleForm })
  ruleForm.fromId = ''
  ruleForm.fromApi = ''
  ruleForm.toId = ''
  ruleForm.toApi = ''
}

/* ========= 规约输入 ========= */

const specForm = reactive<SpecForm>({
  templateId: '',
  aConditions: [createEmptyCondition('a')],
  ifConditions: [createEmptyCondition('if')],
  thenConditions: [createEmptyCondition('then')]
})

const specMode = computed<'single' | 'ifThen'>(() =>
    getSpecMode(specForm.templateId)
)

// 为 utils/spec.ts 包一层，让它拿到 nodes 与 templates
const getTargetOptionsForCond = (cond: SpecCondition) =>
    getTargetOptions(cond, props.nodes, props.deviceTemplates)

const getRelationOptionsForCond = (cond: SpecCondition) =>
    getRelationOptions(cond)

const getValueOptionsForCond = (cond: SpecCondition) =>
    getValueOptions(cond, props.nodes, props.deviceTemplates)

const onConditionDeviceChange = (cond: SpecCondition) => {
  const node = props.nodes.find(n => n.id === cond.deviceId)
  cond.deviceLabel = node ? node.label : ''
  cond.key = ''
  cond.targetType = 'state'
  cond.relation = 'in'
  cond.value = ''
}

const onConditionKeyChange = (cond: SpecCondition, value: string) => {
  cond.key = value
  cond.targetType = resolveTargetTypeByKey(
      cond,
      value,
      props.nodes,
      props.deviceTemplates
  )
  const rels = getRelationOptionsForCond(cond)
  cond.relation = rels[0]
  cond.value = ''
}

// A-only 条件
const addACondition = () => {
  specForm.aConditions.push(createEmptyCondition('a'))
}
const removeACondition = (id: string) => {
  if (specForm.aConditions.length === 1) return
  specForm.aConditions = specForm.aConditions.filter(c => c.id !== id)
}

// IF 条件
const addIfCondition = () => {
  specForm.ifConditions.push(createEmptyCondition('if'))
}
const removeIfCondition = (id: string) => {
  if (specForm.ifConditions.length === 1) return
  specForm.ifConditions = specForm.ifConditions.filter(c => c.id !== id)
}

// THEN 条件
const addThenCondition = () => {
  specForm.thenConditions.push(createEmptyCondition('then'))
}
const removeThenCondition = (id: string) => {
  if (specForm.thenConditions.length === 1) return
  specForm.thenConditions = specForm.thenConditions.filter(c => c.id !== id)
}

const onAddSpec = () => {
  emit('add-spec', {
    templateId: specForm.templateId,
    mode: getSpecMode(specForm.templateId),
    aConditions: specMode.value === 'single' ? specForm.aConditions : [],
    ifConditions: specMode.value === 'ifThen' ? specForm.ifConditions : [],
    thenConditions: specMode.value === 'ifThen' ? specForm.thenConditions : []
  })

  // 重置
  specForm.templateId = ''
  specForm.aConditions = [createEmptyCondition('a')]
  specForm.ifConditions = [createEmptyCondition('if')]
  specForm.thenConditions = [createEmptyCondition('then')]
}
</script>

<template>
  <el-collapse
      v-model="collapseActive"
      class="panel-collapse"
      expand-icon-position="left"
  >
    <!-- 设备列表 -->
    <el-collapse-item name="devices">
      <template #title>
        <div class="collapse-title-row">
          <span class="card-subtitle">{{ t('app.devices') }}</span>
          <div class="card-header-actions">
            <el-button
                link
                :type="deviceViewMode === 'list' ? 'primary' : 'default'"
                @click.stop="deviceViewMode = 'list'"
            >
              <el-icon><List /></el-icon>
            </el-button>
            <el-button
                link
                :type="deviceViewMode === 'icon' ? 'primary' : 'default'"
                @click.stop="deviceViewMode = 'icon'"
            >
              <el-icon><Picture /></el-icon>
            </el-button>
          </div>
        </div>
      </template>

      <el-input
          v-model="deviceKeyword"
          size="default"
          :placeholder="t('app.searchDevice')"
          clearable
          class="device-search"
      />

      <el-scrollbar height="260">
        <!-- 列表模式 -->
        <div v-if="deviceViewMode === 'list'">
          <div
              v-for="d in filteredDevices"
              :key="d.id"
              class="device-item device-item--list"
              draggable="true"
              @dragstart="emit('device-drag-start', d)"
              @dragend="emit('device-drag-end')"
              @click="onSelectDevice(d)"
          >
            {{ d.name }}
          </div>
        </div>

        <!-- 图标模式 -->
        <div v-else class="device-icon-grid">
          <div
              v-for="d in filteredDevices"
              :key="d.id"
              class="device-item device-item--icon"
              draggable="true"
              @dragstart="emit('device-drag-start', d)"
              @dragend="emit('device-drag-end')"
              @click="onSelectDevice(d)"
          >
            <img
                class="device-thumb"
                :src="getTemplateInitIcon(d)"
                :alt="d.name"
                draggable="false"
            />
            <div class="device-thumb-label">{{ d.name }}</div>
          </div>
        </div>
      </el-scrollbar>
    </el-collapse-item>

    <!-- IFTTT 规则 -->
    <el-collapse-item name="rules">
      <template #title>
        <span class="card-subtitle">{{ t('app.rules') }}</span>
      </template>

      <div class="ipt-rule-block">
        <div class="ipt-row">
          <span class="ipt-label">{{ t('app.sourceDevice') }}</span>
          <el-select
              v-model="ruleForm.fromId"
              class="ipt-select"
              :placeholder="t('app.sourceDevice')"
          >
            <el-option
                v-for="n in nodes"
                :key="n.id"
                :label="n.label"
                :value="n.id"
            />
          </el-select>
        </div>

        <div class="ipt-row">
          <span class="ipt-label">{{ t('app.sourceApi') }}</span>
          <el-select
              v-model="ruleForm.fromApi"
              class="ipt-select"
              :placeholder="t('app.sourceApi')"
          >
            <el-option
                v-for="api in fromApis"
                :key="api.Name"
                :label="api.Name"
                :value="api.Name"
            />
          </el-select>
        </div>

        <div class="ipt-row">
          <span class="ipt-label">{{ t('app.targetDevice') }}</span>
          <el-select
              v-model="ruleForm.toId"
              class="ipt-select"
              :placeholder="t('app.targetDevice')"
          >
            <el-option
                v-for="n in nodes"
                :key="n.id"
                :label="n.label"
                :value="n.id"
            />
          </el-select>
        </div>

        <div class="ipt-row">
          <span class="ipt-label">{{ t('app.targetApi') }}</span>
          <el-select
              v-model="ruleForm.toApi"
              class="ipt-select"
              :placeholder="t('app.targetApi')"
          >
            <el-option
                v-for="api in toApis"
                :key="api.Name"
                :label="api.Name"
                :value="api.Name"
            />
          </el-select>
        </div>

        <div class="ipt-row ipt-row-actions">
          <span class="ipt-label"></span>
          <el-button type="primary" size="default" @click="onAddRule">
            {{ t('app.addRule') }}
          </el-button>
        </div>
      </div>
    </el-collapse-item>

    <!-- 规约输入 -->
    <el-collapse-item name="specs">
      <template #title>
        <span class="card-subtitle">{{ t('app.specifications') }}</span>
      </template>

      <!-- 模板选择 -->
      <div class="spec-form">
        <div class="ipt-row">
          <span class="ipt-label">{{ t('app.specTemplate') }}</span>
          <el-select
              v-model="specForm.templateId"
              class="ipt-select"
              :placeholder="t('app.selectTemplate')"
              filterable
          >
            <el-option
                v-for="tpl in specTemplates"
                :key="tpl.id"
                :label="tpl.label"
                :value="tpl.id"
            />
          </el-select>
        </div>
      </div>

      <!-- A-only 模式 -->
      <div v-if="specMode === 'single'" class="spec-section">
        <div class="spec-section-header">
          <span class="spec-section-title">A</span>
          <el-button link size="default" @click="addACondition">
            + {{ t('app.addACondition') }}
          </el-button>
        </div>

        <div
            v-for="cond in specForm.aConditions"
            :key="cond.id"
            class="spec-condition-row"
        >
          <!-- 设备 -->
          <el-select
              v-model="cond.deviceId"
              :placeholder="t('app.sourceDevice')"
              size="default"
              class="spec-cond-device"
              @change="onConditionDeviceChange(cond)"
          >
            <el-option
                v-for="n in nodes"
                :key="n.id"
                :label="n.label"
                :value="n.id"
            />
          </el-select>

          <!-- 属性 / API -->
          <el-select
              v-if="cond.deviceId"
              v-model="cond.key"
              size="default"
              class="spec-cond-target"
              :placeholder="t('app.selectAttrOrApi')"
              @change="onConditionKeyChange(cond, $event)"
          >
            <el-option
                v-for="opt in getTargetOptionsForCond(cond)"
                :key="opt.value"
                :label="opt.label"
                :value="opt.value"
            />
          </el-select>

          <!-- 如果是 API：到此为止 -->
          <template v-if="cond.deviceId && cond.targetType === 'api'">
            <!-- 只保留前两个选择框 -->
          </template>

          <!-- 若为 State / 变量：继续关系 + 值 -->
          <template v-else-if="cond.deviceId && cond.key">
            <el-select
                v-model="cond.relation"
                size="default"
                class="spec-cond-relation"
            >
              <el-option
                  v-for="rel in getRelationOptionsForCond(cond)"
                  :key="rel"
                  :label="rel"
                  :value="rel"
              />
            </el-select>

            <!-- 变量：输入框 -->
            <template v-if="cond.targetType === 'variable'">
              <el-input
                  v-model="cond.value"
                  size="default"
                  class="spec-cond-value"
                  :placeholder="t('app.value')"
              />
            </template>

            <!-- State：下拉 -->
            <template v-else>
              <el-select
                  v-model="cond.value"
                  size="default"
                  class="spec-cond-value"
              >
                <el-option
                    v-for="v in getValueOptionsForCond(cond)"
                    :key="v"
                    :label="v"
                    :value="v"
                />
              </el-select>
            </template>
          </template>

          <el-button
              link
              type="danger"
              size="default"
              @click="removeACondition(cond.id)"
          >
            ×
          </el-button>
        </div>
      </div>

      <!-- IF / THEN 模式 -->
      <div v-else>
        <!-- IF 区 -->
        <div class="spec-section">
          <div class="spec-section-header">
            <span class="spec-section-title">IF</span>
            <el-button link size="default" @click="addIfCondition">
              + {{ t('app.addIfCondition') }}
            </el-button>
          </div>

          <div
              v-for="cond in specForm.ifConditions"
              :key="cond.id"
              class="spec-condition-row"
          >
            <el-select
                v-model="cond.deviceId"
                :placeholder="t('app.sourceDevice')"
                size="default"
                class="spec-cond-device"
                @change="onConditionDeviceChange(cond)"
            >
              <el-option
                  v-for="n in nodes"
                  :key="n.id"
                  :label="n.label"
                  :value="n.id"
              />
            </el-select>

            <el-select
                v-if="cond.deviceId"
                v-model="cond.key"
                size="default"
                class="spec-cond-target"
                :placeholder="t('app.selectAttrOrApi')"
                @change="onConditionKeyChange(cond, $event)"
            >
              <el-option
                  v-for="opt in getTargetOptionsForCond(cond)"
                  :key="opt.value"
                  :label="opt.label"
                  :value="opt.value"
              />
            </el-select>

            <template v-if="cond.deviceId && cond.targetType === 'api'">
              <!-- 只保留设备 + API -->
            </template>

            <template v-else-if="cond.deviceId && cond.key">
              <el-select
                  v-model="cond.relation"
                  size="default"
                  class="spec-cond-relation"
              >
                <el-option
                    v-for="rel in getRelationOptionsForCond(cond)"
                    :key="rel"
                    :label="rel"
                    :value="rel"
                />
              </el-select>

              <template v-if="cond.targetType === 'variable'">
                <el-input
                    v-model="cond.value"
                    size="default"
                    class="spec-cond-value"
                    :placeholder="t('app.value')"
                />
              </template>
              <template v-else>
                <el-select
                    v-model="cond.value"
                    size="default"
                    class="spec-cond-value"
                >
                  <el-option
                      v-for="v in getValueOptionsForCond(cond)"
                      :key="v"
                      :label="v"
                      :value="v"
                  />
                </el-select>
              </template>
            </template>

            <el-button
                link
                type="danger"
                size="default"
                @click="removeIfCondition(cond.id)"
            >
              ×
            </el-button>
          </div>
        </div>

        <!-- THEN 区 -->
        <div class="spec-section">
          <div class="spec-section-header">
            <span class="spec-section-title">THEN</span>
            <el-button link size="default" @click="addThenCondition">
              + {{ t('app.addThenCondition') }}
            </el-button>
          </div>

          <div
              v-for="cond in specForm.thenConditions"
              :key="cond.id"
              class="spec-condition-row"
          >
            <el-select
                v-model="cond.deviceId"
                :placeholder="t('app.targetDevice')"
                size="default"
                class="spec-cond-device"
                @change="onConditionDeviceChange(cond)"
            >
              <el-option
                  v-for="n in nodes"
                  :key="n.id"
                  :label="n.label"
                  :value="n.id"
              />
            </el-select>

            <el-select
                v-if="cond.deviceId"
                v-model="cond.key"
                size="default"
                class="spec-cond-target"
                :placeholder="t('app.selectAttrOrApi')"
                @change="onConditionKeyChange(cond, $event)"
            >
              <el-option
                  v-for="opt in getTargetOptionsForCond(cond)"
                  :key="opt.value"
                  :label="opt.label"
                  :value="opt.value"
              />
            </el-select>

            <template v-if="cond.deviceId && cond.targetType === 'api'">
              <!-- 只保留设备 + API -->
            </template>

            <template v-else-if="cond.deviceId && cond.key">
              <el-select
                  v-model="cond.relation"
                  size="default"
                  class="spec-cond-relation"
              >
                <el-option
                    v-for="rel in getRelationOptionsForCond(cond)"
                    :key="rel"
                    :label="rel"
                    :value="rel"
                />
              </el-select>

              <template v-if="cond.targetType === 'variable'">
                <el-input
                    v-model="cond.value"
                    size="default"
                    class="spec-cond-value"
                    :placeholder="t('app.value')"
                />
              </template>
              <template v-else>
                <el-select
                    v-model="cond.value"
                    size="default"
                    class="spec-cond-value"
                >
                  <el-option
                      v-for="v in getValueOptionsForCond(cond)"
                      :key="v"
                      :label="v"
                      :value="v"
                  />
                </el-select>
              </template>
            </template>

            <el-button
                link
                type="danger"
                size="default"
                @click="removeThenCondition(cond.id)"
            >
              ×
            </el-button>
          </div>
        </div>
      </div>

      <el-button
          type="primary"
          size="default"
          class="spec-add-button"
          @click="onAddSpec"
      >
        {{ t('app.addSpec') }}
      </el-button>
    </el-collapse-item>
  </el-collapse>
</template>

<style scoped>
/* ---- 设备搜索框 ---- */
.device-search {
  margin-bottom: var(--iot-space-sm);
}

/* ---- 设备条目（列表模式 + 图标模式通用） ---- */
.device-item {
  background: var(--iot-color-device-item-bg);
  border-radius: var(--iot-radius-input);
  margin-bottom: var(--iot-space-sm);
  padding: var(--iot-space-sm) var(--iot-space-md);
  cursor: grab;
  transition:
      box-shadow 0.14s ease-out,
      background 0.14s ease-out,
      transform 0.12s ease-out;
  border: 1px solid var(--iot-color-device-item-border);
  color: var(--iot-color-device-item-text);
  font-size: var(--iot-font-subtitle);
}

.device-item:hover {
  background: var(--iot-color-device-item-bg-hover);
  box-shadow: var(--iot-shadow-device-hover);
  transform: translateY(-1px);
}

/* ---- 设备条目：图标模式下的栅格布局 ---- */
.device-icon-grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(6.25rem, 1fr)); /* ≈100px */
  gap: var(--iot-space-sm);
}

/* 图标模式：文字居中 */
.device-item--icon {
  text-align: center;
}

/* 设备缩略图 */
.device-thumb {
  width: var(--iot-thumb-width);
  height: var(--iot-thumb-height);
  object-fit: contain;
  margin-bottom: var(--iot-space-2xs);
}

/* 缩略图下设备名称 */
.device-thumb-label {
  font-size: var(--iot-font-caption);
  word-break: break-all;
}

/* ===========================
 * IFTTT / Spec 公共行布局
 * =========================== */

.ipt-rule-block {
  margin-top: var(--iot-space-xs);
}

.ipt-row {
  display: grid;
  grid-template-columns: max-content 1fr; /* 左 label 自适应，右侧组件占满 */
  column-gap: var(--iot-space-sm);
  align-items: center;
  margin-bottom: var(--iot-space-sm);
  overflow: visible;
}

.ipt-row-actions {
  margin-top: var(--iot-space-xs);
}

.ipt-label {
  min-width: 7.5rem; /* 大约 120px，根据需要可以再调 */
  white-space: nowrap;
  overflow: visible;
  flex-shrink: 0;
  font-size: var(--iot-font-base);
  color: var(--iot-color-text);
}

.ipt-select {
  width: 100%;
}

/* ===========================
 * 规约输入区域（Specs）
 * =========================== */

.spec-form {
  margin-top: var(--iot-space-2xs);
  margin-bottom: var(--iot-space-sm);
}

/* A / IF / THEN 外框容器 */
.spec-section {
  margin: var(--iot-space-sm) 0 var(--iot-space-xs);
  padding: var(--iot-space-sm);
  border-radius: var(--iot-radius-input);
  background: linear-gradient(
      135deg,
      var(--iot-color-spec-bg),
      var(--iot-color-spec-bg-strong)
  );
  box-shadow: 0 0 0 1px var(--iot-color-spec-border);
}

/* 小标题行：左标题 + 右侧按钮（添加条件） */
.spec-section-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  margin-bottom: var(--iot-space-xs);
}

/* “A / IF / THEN” 标识 */
.spec-section-title {
  font-size: var(--iot-font-caption);
  font-weight: 600;
  color: var(--iot-color-text-muted);
  letter-spacing: 0.08em;
  text-transform: uppercase;
}

/* 每一行条件：设备 + 属性/API + 关系 + 值 + 删除按钮 */
.spec-condition-row {
  display: flex;
  flex-wrap: wrap; /* 四块时允许换行成两排 */
  align-items: center;
  gap: var(--iot-space-xs);
}

.spec-condition-row + .spec-condition-row {
  margin-top: var(--iot-space-sm); /* 条件之间垂直间距 */
  padding-top: var(--iot-space-sm); /* 分隔线与内容之间缓冲 */
  border-top: 2px dashed var(--iot-color-spec-border);
}

/* 底部 “添加规约” 按钮与内容留一点间距 */
.spec-add-button {
  margin-top: var(--iot-space-sm);
}

/* 宽度控制：允许收缩，也允许在窄屏下换行 */
.spec-cond-device,
.spec-cond-target,
.spec-cond-relation,
.spec-cond-value {
  min-width: 7rem;
  flex: 1 1 7rem;
}

/* 设备名通常最长，稍微给多一点初始比例 */
.spec-cond-device {
  flex: 1.2 1 8rem;
}

.spec-cond-target {
  flex: 1 1 7rem;
}

/* 关系通常是 <=、== 等短字符串，占用稍微少一点 */
.spec-cond-relation {
  flex: 0.8 1 6rem;
}

.spec-cond-value {
  flex: 1 1 7rem;
}

/* ===========================
 * 其他表单 label：不换行
 * =========================== */

:deep(.el-form-item__label) {
  white-space: nowrap;
}
</style>

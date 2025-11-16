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
  <el-collapse v-model="collapseActive" class="panel-collapse">
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

      <el-form :model="ruleForm" label-width="70px" size="default">
        <el-form-item :label="t('app.sourceDevice')">
          <el-select v-model="ruleForm.fromId" :placeholder="t('app.sourceDevice')">
            <el-option
                v-for="n in nodes"
                :key="n.id"
                :label="n.label"
                :value="n.id"
            />
          </el-select>
        </el-form-item>
        <el-form-item :label="t('app.sourceApi')">
          <el-select v-model="ruleForm.fromApi" :placeholder="t('app.sourceApi')">
            <el-option
                v-for="api in fromApis"
                :key="api.Name"
                :label="api.Name"
                :value="api.Name"
            />
          </el-select>
        </el-form-item>
        <el-form-item :label="t('app.targetDevice')">
          <el-select v-model="ruleForm.toId" :placeholder="t('app.targetDevice')">
            <el-option
                v-for="n in nodes"
                :key="n.id"
                :label="n.label"
                :value="n.id"
            />
          </el-select>
        </el-form-item>
        <el-form-item :label="t('app.targetApi')">
          <el-select v-model="ruleForm.toApi" :placeholder="t('app.targetApi')">
            <el-option
                v-for="api in toApis"
                :key="api.Name"
                :label="api.Name"
                :value="api.Name"
            />
          </el-select>
        </el-form-item>
        <el-form-item>
          <el-button type="primary" size="default" @click="onAddRule">
            {{ t('app.addRule') }}
          </el-button>
        </el-form-item>
      </el-form>
    </el-collapse-item>

    <!-- 规约输入 -->
    <el-collapse-item name="specs">
      <template #title>
        <span class="card-subtitle">{{ t('app.specifications') }}</span>
      </template>

      <el-form :model="specForm" label-width="90px" size="default" class="spec-form">
        <el-form-item :label="t('app.specTemplate')">
          <el-select
              v-model="specForm.templateId"
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
        </el-form-item>
      </el-form>

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

        <!-- THEN 区（B，和 IF 完全相同的结构） -->
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

<script setup lang="ts">
import {ref, watch, computed} from 'vue'
import {useI18n} from 'vue-i18n'

import type {DeviceManifest} from '../types/device'
import type {DeviceEdge} from '../types/edge'
import type {Specification} from '../types/spec'
import {buildSpecText} from "../utils/spec"

const props = defineProps<{
  visible: boolean
  deviceName: string
  description: string
  label: string
  manifest?: DeviceManifest | null
  rules?: DeviceEdge[]
  specs?: Specification[]
}>()

const emit = defineEmits<{
  (e: 'update:visible', value: boolean): void
  (e: 'save', newLabel: string): void
  (e: 'delete'): void
}>()

const {t} = useI18n()

const innerVisible = ref(props.visible)
const innerLabel = ref(props.label)

/* 同步 props -> local state */
watch(() => props.visible, v => (innerVisible.value = v))
watch(() => props.label, v => (innerLabel.value = v))

const close = () => {
  innerVisible.value = false
  emit('update:visible', false)
}

const onSave = () => emit('save', innerLabel.value)
const onDelete = () => emit('delete')

/* ---------- 核心展示数据提取 ---------- */

const manifest = computed<DeviceManifest | null>(() => props.manifest ?? null)

// 1. 基础信息表格数据
const basicRows = computed(() => {
  const m = manifest.value
  if (!m) return []

  const rows = [
    {label: t('app.name') || 'Name', value: m.Name},
    {label: t('app.instanceName') || 'Instance', value: props.label},
    {label: t('app.description') || 'Description', value: m.Description || props.description || t('app.null')},
    {label: t('app.initState') || 'Initial State', value: m.InitState},
    {label: t('app.modes') || 'Modes', value: m.Modes?.join(', ')},
    {label: t('app.impactedVariables') || 'Impacted Variables', value: m.ImpactedVariables?.join(', ')}
  ]
  // 过滤掉空值行
  return rows.filter(r => r.value !== '' && r.value != null)
})

// 2. 变量列表 (合并 Internal 和 Impacted，并展示隐私/信任)
const variables = computed(() => {
  const m = manifest.value
  if (!m) return []
  const list: any[] = []

  // Internal Variables (完整对象)
  if (m.InternalVariables) {
    m.InternalVariables.forEach(iv => {
      // 智能格式化 Value 列：显示枚举值 或 数值范围
      let valDisplay = ''
      if (iv.Values && iv.Values.length) valDisplay = iv.Values.join(' / ')
      else if (iv.LowerBound !== undefined && iv.UpperBound !== undefined) valDisplay = `[${iv.LowerBound}, ${iv.UpperBound}]`

      list.push({
        name: iv.Name,
        value: valDisplay,
        trust: iv.Trust,
        privacy: iv.Privacy, // [New]
        type: 'Internal'
      })
    })
  }

  // Impacted Variables (外部引用)
  if (m.ImpactedVariables) {
    m.ImpactedVariables.forEach(vName => {
      // 避免重复显示
      if (!list.some(item => item.name === vName)) {
        list.push({
          name: vName,
          value: '(External)',
          trust: '-',
          privacy: '-',
          type: 'Impacted'
        })
      }
    })
  }
  return list
})

// 3. 状态列表 (展示隐私、不变式)
const states = computed(() => {
  const m = manifest.value
  if (!m || !m.WorkingStates) return []
  return m.WorkingStates.map(s => ({
    name: s.Name,
    description: s.Description,
    trust: s.Trust,
    privacy: s.Privacy,     // [New]
    invariant: s.Invariant, // [New]
    hasDynamics: s.Dynamics && s.Dynamics.length > 0
  }))
})

// 4. API 列表 (展示 Signal)
const apis = computed(() => {
  const m = manifest.value
  if (!m || !m.APIs) return []
  return m.APIs.map(api => ({
    name: api.Name,
    from: api.StartState,
    to: api.EndState,
    signal: api.Signal,     // [New]
    description: api.Description
  }))
})

// 关联数据
const relatedRules = computed<DeviceEdge[]>(() => props.rules ?? [])
const relatedSpecs = computed<Specification[]>(() => props.specs ?? [])
</script>

<template>
  <el-dialog
      v-model="innerVisible"
      class="device-dialog"
      :title="t('app.deviceInfo')"
      :width="'42rem'"
      :draggable="true"
      @close="close"
  >
    <!-- Header -->
    <template #header>
      <div class="dd-header">
        <div class="dd-header-main">
          <div class="dd-title">{{ t('app.deviceInfo') || 'Device Details' }}</div>
          <div class="dd-subtitle">{{ deviceName || label }}</div>
        </div>
      </div>
    </template>

    <!-- Body -->
    <div class="dd-body">
      <div class="dd-body-scroll">

        <!-- Basic Info -->
        <section class="dd-section">
          <div class="dd-section-title">{{ t('app.deviceBasic') || 'Basic Information' }}</div>
          <table class="dd-table dd-table-basic">
            <tbody>
            <tr v-for="row in basicRows" :key="row.label">
              <th class="dd-th-label">{{ row.label }}</th>
              <td class="dd-td-value"><span class="dd-ellipsis" :title="String(row.value)">{{ row.value || '' }}</span></td>
            </tr>
            </tbody>
          </table>
        </section>

        <!-- Variables (Enhanced) -->
        <section v-if="variables.length" class="dd-section">
          <div class="dd-section-title">{{ t('app.deviceVariables') || 'Variables' }}</div>
          <table class="dd-table">
            <thead>
            <tr>
              <th width="25%">{{ t('app.name') }}</th>
              <th width="30%">{{ t('app.range') }}</th>
              <th width="15%">{{ t('app.trust') }}</th>
              <th width="15%">{{ t('app.privacy') }}</th> <!-- [New] Column -->
              <th width="15%">{{ t('app.type') }}</th>
            </tr>
            </thead>
            <tbody>
            <tr v-for="(v, idx) in variables" :key="idx">
              <td><span class="dd-ellipsis" :title="v.name">{{ v.name }}</span></td>
              <td><span class="dd-ellipsis" :title="v.value">{{ v.value }}</span></td>
              <td>
                <span :class="['dd-tag', v.trust === 'trusted' ? 'tag-success' : 'tag-warning']"
                      v-if="v.trust && v.trust !== '-'">
                  {{ v.trust }}
                </span>
                <span v-else>-</span>
              </td>
              <td>
                <!-- [New] Privacy Tag -->
                <span :class="['dd-tag', v.privacy === 'private' ? 'tag-danger' : 'tag-info']"
                      v-if="v.privacy && v.privacy !== '-'">
                  {{ v.privacy }}
                </span>
                <span v-else>-</span>
              </td>
              <td class="dd-text-muted">{{ v.type }}</td>
            </tr>
            </tbody>
          </table>
        </section>

        <!-- States (Enhanced) -->
        <section v-if="states.length" class="dd-section">
          <div class="dd-section-title">{{ t('app.deviceStates') || 'Working States' }}</div>
          <table class="dd-table">
            <thead>
            <tr>
              <th width="20%">{{ t('app.name') }}</th>
              <th width="30%">{{ t('app.description') }}</th>
              <th width="20%">{{ t('app.invariant') }}</th>
              <th width="15%">{{ t('app.trust') }}</th>
              <th width="15%">{{ t('app.privacy') }}</th> <!-- [New] Column -->
            </tr>
            </thead>
            <tbody>
            <tr v-for="(s, idx) in states" :key="idx">
              <td><span class="dd-ellipsis font-bold">{{ s.name }}</span></td>
              <td class="dd-col-desc">
                <el-tooltip v-if="s.description" :content="s.description" placement="top">
                  <span class="dd-ellipsis">{{ s.description }}</span>
                </el-tooltip>
                <span v-else>-</span>
              </td>
              <td><span class="dd-ellipsis code-font">{{ s.invariant }}</span></td>
              <td>
                <span :class="['dd-tag', s.trust === 'trusted' ? 'tag-success' : 'tag-warning']">{{ s.trust }}</span>
              </td>
              <td>
                <span :class="['dd-tag', s.privacy === 'private' ? 'tag-danger' : 'tag-info']"
                      v-if="s.privacy">{{ s.privacy }}</span>
              </td>
            </tr>
            </tbody>
          </table>
        </section>

        <!-- APIs (Enhanced) -->
        <section v-if="apis.length" class="dd-section">
          <div class="dd-section-title">{{ t('app.deviceApis') || 'APIs' }}</div>
          <table class="dd-table">
            <thead>
            <tr>
              <th width="25%">{{ t('app.name') }}</th>
              <th width="10%">{{ t('app.signal') }}</th> <!-- [New] Column -->
              <th width="25%">{{ t('app.transition') }}</th>
              <th width="40%">{{ t('app.description') }}</th>
            </tr>
            </thead>
            <tbody>
            <tr v-for="(api, idx) in apis" :key="idx">
              <td><span class="dd-ellipsis font-bold">{{ api.name }}</span></td>
              <td>
                <span v-if="api.signal" class="dd-tag tag-primary">Sig</span>
                <span v-else class="dd-text-muted">-</span>
              </td>
              <td>
                <span class="dd-flow" v-if="api.from || api.to">
                  {{ api.from || '*' }} <span class="arrow">→</span> {{ api.to || '*' }}
                </span>
              </td>
              <td class="dd-col-desc">
                <el-tooltip v-if="api.description" :content="api.description" placement="top">
                  <span class="dd-ellipsis">{{ api.description }}</span>
                </el-tooltip>
                <span v-else>-</span>
              </td>
            </tr>
            </tbody>
          </table>
        </section>

        <!-- Rules (Unchanged) -->
        <section v-if="relatedRules.length" class="dd-section">
          <div class="dd-section-title">{{ t('app.relatedRules') || 'Related Rules' }}</div>
          <table class="dd-table">
            <thead>
            <tr>
              <th>{{ t('app.sourceDevice') }}</th>
              <th>{{ t('app.sourceApi') }}</th>
              <th>{{ t('app.targetDevice') }}</th>
              <th>{{ t('app.targetApi') }}</th>
            </tr>
            </thead>
            <tbody>
            <tr v-for="r in relatedRules" :key="r.id">
              <td>{{ r.fromLabel }}</td>
              <td>{{ r.fromApi }}</td>
              <td>{{ r.toLabel }}</td>
              <td>{{ r.toApi }}</td>
            </tr>
            </tbody>
          </table>
        </section>

        <!-- Specs (Unchanged) -->
        <section v-if="relatedSpecs.length" class="dd-section">
          <div class="dd-section-title">{{ t('app.relatedSpecs') || 'Specifications' }}</div>
          <table class="dd-table">
            <thead>
            <tr>
              <th>{{ t('app.specTemplate') }}</th>
              <th>{{ t('app.specContent') }}</th>
            </tr>
            </thead>
            <tbody>
            <tr v-for="s in relatedSpecs" :key="s.id">
              <td>{{ s.templateLabel }}</td>
              <td>
                <el-tooltip :content="buildSpecText(s)" placement="top"><span class="dd-ellipsis">{{
                    buildSpecText(s)
                  }}</span></el-tooltip>
              </td>
            </tr>
            </tbody>
          </table>
        </section>
      </div>

      <!-- Rename Section -->
      <section class="dd-section dd-section-rename">
        <div class="dd-section-title">{{ t('app.renameDevice') || 'Rename Device' }}</div>
        <el-form label-width="80px">
          <el-form-item :label="t('app.name')">
            <el-input v-model="innerLabel"/>
          </el-form-item>
        </el-form>
      </section>
    </div>

    <!-- Footer -->
    <template #footer>
      <div class="dd-footer">
        <el-button type="danger" @click="onDelete">{{ t('app.deleteDevice') }}</el-button>
        <div class="dd-footer-right">
          <el-button @click="close">{{ t('app.cancel') }}</el-button>
          <el-button type="primary" @click="onSave">{{ t('app.save') }}</el-button>
        </div>
      </div>
    </template>
  </el-dialog>
</template>

<style scoped>
/* Dialog Base Style */
.dd-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
}

.dd-header-main {
  display: flex;
  flex-direction: column;
  gap: 4px;
}

.dd-title {
  font-size: 1.25rem;
  font-weight: 600;
  color: #111827;
}

.dd-subtitle {
  font-size: 0.95rem;
  color: #2d3035;
}

.dd-body {
  display: flex;
  flex-direction: column;
  gap: 16px;
}

.dd-body-scroll {
  max-height: 60vh;
  overflow-y: auto;
  display: flex;
  flex-direction: column;
  gap: 20px;
  padding-right: 4px;
}

.dd-section {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.dd-section-title {
  font-size: 1rem;
  font-weight: 600;
  color: #0f172a;
  border-left: 4px solid var(--iot-color-edge);
  padding-left: 8px;
}

/* Table Styles */
.dd-table {
  width: 100%;
  border-collapse: collapse;
  font-size: 0.9rem;
  table-layout: fixed;
}

.dd-table th {
  text-align: left;
  padding: 6px 10px;
  color: #2d3035;
  border-bottom: 1px solid rgba(148, 163, 184, 0.6);
  background: rgba(0, 0, 0, 0.02);
  font-weight: 600;
}

.dd-table td {
  padding: 8px 10px;
  border-bottom: 1px solid rgba(0, 0, 0, 0.06);
  color: #0f172a;
  vertical-align: middle;
}

.dd-table-basic th {
  width: 30%;
  background: transparent;
  border-right: 1px solid rgba(148, 163, 184, 0.6);
}

.dd-table tbody tr:hover td {
  background-color: rgba(0, 0, 0, 0.03);
}

/* Helper Classes */
.dd-ellipsis {
  display: block;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.dd-text-muted {
  color: #2d3035;
  font-size: 0.85rem;
}

.font-bold {
  font-weight: 600;
}

.code-font {
  font-family: monospace;
  font-size: 0.85rem;
  background: rgba(0, 0, 0, 0.04);
  padding: 2px 4px;
  border-radius: 3px;
}

.dd-col-desc {
  cursor: help;
}

/* Status Tags */
.dd-tag {
  display: inline-block;
  padding: 1px 6px;
  border-radius: 4px;
  font-size: 0.75rem;
  font-weight: 500;
  line-height: 1.4;
  border: 1px solid transparent;
}

.tag-success {
  background: #f0fdf4;
  color: #166534;
  border-color: #bbf7d0;
}

.tag-warning {
  background: #fefce8;
  color: #854d0e;
  border-color: #fef08a;
}

.tag-danger {
  background: #fef2f2;
  color: #991b1b;
  border-color: #fecaca;
}

.tag-info {
  background: #f8fafc;
  color: #475569;
  border-color: #e2e8f0;
}

.tag-primary {
  background: #eff6ff;
  color: #1e40af;
  border-color: #bfdbfe;
}

/* Transition Arrow */
.dd-flow {
  font-size: 0.85rem;
  display: flex;
  align-items: center;
  gap: 4px;
  color: #2d3035;
}

.arrow {
  color: var(--iot-color-edge);
  font-weight: bold;
}

/* Footer & Rename */
.dd-section-rename {
  margin-top: 8px;
  padding-top: 12px;
  border-top: 1px dashed rgba(148, 163, 184, 0.6);
}

.dd-footer {
  display: flex;
  justify-content: space-between;
  padding-top: 12px;
  border-top: 1px solid rgba(148, 163, 184, 0.6);
}

.dd-footer-right {
  display: flex;
  gap: 8px;
}
</style>
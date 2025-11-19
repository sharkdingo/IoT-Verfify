<script setup lang="ts">
import { ref, watch, computed } from 'vue'
import { useI18n } from 'vue-i18n'

import type { DeviceManifest } from '../types/device'
import type { DeviceEdge } from '../types/edge'
import type { Specification } from '../types/spec'
import { buildSpecText } from "../utils/spec.ts"
import {
  extractBasicDeviceInfo,
  extractDeviceVariables,
  extractDeviceStates,
  extractDeviceApis
} from '../utils/device'

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

const { t } = useI18n()

const innerVisible = ref(props.visible)
const innerLabel   = ref(props.label)

/* 同步外部值 -> 内部状态 */
watch(() => props.visible, v => (innerVisible.value = v))
watch(() => props.label,   v => (innerLabel.value   = v))

const close = () => {
  innerVisible.value = false
  emit('update:visible', false)
}

const onSave   = () => emit('save', innerLabel.value)
const onDelete = () => emit('delete')

/* ---------- manifest 相关的展示数据，全走 utils/device ---------- */

const manifest = computed<DeviceManifest | null>(() => props.manifest ?? null)

/** 基本信息区：再加上 i18n 标签，最终变成表格行 */
const basicInfo = computed(() =>
    extractBasicDeviceInfo(
        manifest.value,
        props.deviceName || props.label,
        props.label,
        props.description
    )
)

const basicRows = computed(() => {
  const info = basicInfo.value
  const rows = [
    {
      key: 'name',
      label: t('app.name') || 'Name',
      value: info.name
    },
    {
      key: 'instance',
      label: t('app.instanceName') || 'Instance',
      value: info.instanceLabel
    },
    {
      key: 'description',
      label: t('app.description') || 'Description',
      value: info.description
    },
    {
      key: 'initState',
      label: t('app.initState') || 'Initial State',
      value: info.initState
    },
    {
      key: 'impacted',
      label: t('app.impactedVariables') || 'Impacted Variables',
      value: info.impactedVariables.join(', ')
    }
  ]
  // 只保留有值的行
  return rows.filter(r => r.value !== '' && r.value != null)
})

/** Variables / States / APIs 列表：直接交给 utils 做数据清洗 */
const variables = computed(() => extractDeviceVariables(manifest.value))
const states    = computed(() => extractDeviceStates(manifest.value))
const apis      = computed(() => extractDeviceApis(manifest.value))

/** 当前节点相关 IFTTT 规则（Board.vue 已经筛好传进来） */
const relatedRules = computed<DeviceEdge[]>(() => props.rules ?? [])

/** 当前节点相关规约 */
const relatedSpecs = computed<Specification[]>(() => props.specs ?? [])
</script>

<template>
  <el-dialog
      v-model="innerVisible"
      class="device-dialog"
      :title="t('app.deviceInfo')"
      :width="'38rem'"
      :draggable="true"
      @close="close"
  >
    <!-- ===== Header：标题 + 设备名 ===== -->
    <template #header>
      <div class="dd-header">
        <div class="dd-header-main">
          <div class="dd-title">
            {{ t('app.deviceInfo') }}
          </div>
          <div class="dd-subtitle">
            {{ deviceName || label }}
          </div>
        </div>
      </div>
    </template>

    <!-- ===== Body：上半部滚动区域 + 下半部重命名区域 ===== -->
    <div class="dd-body">
      <!-- 上半部：所有表格，固定高度后内部滚动 -->
      <div class="dd-body-scroll">
        <!-- Basic -->
        <section class="dd-section">
          <div class="dd-section-title">
            {{ t('app.deviceBasic') || 'Basic' }}
          </div>
          <table class="dd-table dd-table-basic">
            <tbody>
            <tr v-for="row in basicRows" :key="row.key">
              <th class="dd-th-label">
                {{ row.label }}
              </th>
              <td class="dd-td-value">
                  <span class="dd-ellipsis">
                    {{ row.value || '-' }}
                  </span>
              </td>
            </tr>
            </tbody>
          </table>
        </section>

        <!-- Variables -->
        <section v-if="variables.length" class="dd-section">
          <div class="dd-section-title">
            {{ t('app.deviceVariables') || 'Variables' }}
          </div>
          <table class="dd-table">
            <thead>
            <tr>
              <th>{{ t('app.name') || 'Name' }}</th>
              <th>{{ t('app.value') || 'Value' }}</th>
              <th>{{ t('app.trust') || 'Trust' }}</th>
            </tr>
            </thead>
            <tbody>
            <tr v-for="(v, idx) in variables" :key="idx">
              <td><span class="dd-ellipsis">{{ v.name || '-' }}</span></td>
              <td><span class="dd-ellipsis">{{ v.value || '-' }}</span></td>
              <td><span class="dd-ellipsis">{{ v.trust || '-' }}</span></td>
            </tr>
            </tbody>
          </table>
        </section>

        <!-- States -->
        <section v-if="states.length" class="dd-section">
          <div class="dd-section-title">
            {{ t('app.deviceStates') || 'States' }}
          </div>
          <table class="dd-table">
            <thead>
            <tr>
              <th>{{ t('app.name') || 'Name' }}</th>
              <th>{{ t('app.description') || 'Description' }}</th>
              <th>{{ t('app.trust') || 'Trust' }}</th>
            </tr>
            </thead>
            <tbody>
            <tr v-for="(s, idx) in states" :key="idx">
              <td><span class="dd-ellipsis">{{ s.name || '-' }}</span></td>
              <td class="dd-col-desc">
                <el-tooltip
                    v-if="s.description"
                    :content="s.description"
                    placement="top"
                >
                    <span class="dd-ellipsis">
                      {{ s.description }}
                    </span>
                </el-tooltip>
                <span v-else class="dd-ellipsis">-</span>
              </td>
              <td><span class="dd-ellipsis">{{ s.trust || '-' }}</span></td>
            </tr>
            </tbody>
          </table>
        </section>

        <!-- APIs -->
        <section v-if="apis.length" class="dd-section">
          <div class="dd-section-title">
            {{ t('app.deviceApis') || 'APIs' }}
          </div>
          <table class="dd-table">
            <thead>
            <tr>
              <th>{{ t('app.name') || 'Name' }}</th>
              <th>{{ t('app.from') || 'From' }}</th>
              <th>{{ t('app.to') || 'To' }}</th>
              <th>{{ t('app.description') || 'Description' }}</th>
            </tr>
            </thead>
            <tbody>
            <tr v-for="(api, idx) in apis" :key="idx">
              <td><span class="dd-ellipsis">{{ api.name || '-' }}</span></td>
              <td><span class="dd-ellipsis">{{ api.from || '-' }}</span></td>
              <td><span class="dd-ellipsis">{{ api.to || '-' }}</span></td>
              <td class="dd-col-desc">
                <el-tooltip
                    v-if="api.description"
                    :content="api.description"
                    placement="top"
                >
                    <span class="dd-ellipsis">
                      {{ api.description }}
                    </span>
                </el-tooltip>
                <span v-else class="dd-ellipsis">-</span>
              </td>
            </tr>
            </tbody>
          </table>
        </section>

        <!-- 相关 IFTTT 规则 -->
        <section v-if="relatedRules.length" class="dd-section">
          <div class="dd-section-title">
            {{ t('app.relatedRules') || 'Related IFTTT Rules' }}
          </div>
          <table class="dd-table">
            <thead>
            <tr>
              <th>{{ t('app.sourceDevice') || 'From Device' }}</th>
              <th>{{ t('app.sourceApi') || 'From API' }}</th>
              <th>{{ t('app.targetDevice') || 'To Device' }}</th>
              <th>{{ t('app.targetApi') || 'To API' }}</th>
            </tr>
            </thead>
            <tbody>
            <tr v-for="r in relatedRules" :key="r.id">
              <td><span class="dd-ellipsis">{{ r.fromLabel }}</span></td>
              <td><span class="dd-ellipsis">{{ r.fromApi }}</span></td>
              <td><span class="dd-ellipsis">{{ r.toLabel }}</span></td>
              <td><span class="dd-ellipsis">{{ r.toApi }}</span></td>
            </tr>
            </tbody>
          </table>
        </section>

        <!-- 相关规约 -->
        <section v-if="relatedSpecs.length" class="dd-section">
          <div class="dd-section-title">
            {{ t('app.relatedSpecs') || 'Related Specifications' }}
          </div>
          <table class="dd-table">
            <thead>
            <tr>
              <th>{{ t('app.specTemplateShort') || 'Template' }}</th>
              <th>{{ t('app.specText') || 'Text' }}</th>
            </tr>
            </thead>
            <tbody>
            <tr v-for="s in relatedSpecs" :key="s.id">
              <td>
                <span class="dd-ellipsis">{{ s.templateLabel }}</span>
              </td>
              <td class="dd-col-desc">
                <el-tooltip
                    :content="buildSpecText(s)"
                    placement="top"
                >
            <span class="dd-ellipsis">
              {{ buildSpecText(s) }}
            </span>
                </el-tooltip>
              </td>
            </tr>
            </tbody>
          </table>
        </section>
      </div>

      <!-- 下半部：重命名区域（固定在表格下方，不参与 dd-body-scroll 的滚动） -->
      <section class="dd-section dd-section-rename">
        <div class="dd-section-title">
          {{ t('app.renameDevice') || 'Rename Device' }}
        </div>
        <el-form label-width="var(--iot-dialog-label-width)">
          <el-form-item :label="t('app.name')">
            <el-input v-model="innerLabel" />
          </el-form-item>
        </el-form>
      </section>
    </div>

    <!-- ===== Footer：删除 / 取消 / 保存 ===== -->
    <template #footer>
      <div class="dd-footer">
        <el-button type="danger" @click="onDelete">
          {{ t('app.deleteDevice') }}
        </el-button>

        <div class="dd-footer-right">
          <el-button @click="close">{{ t('app.cancel') }}</el-button>
          <el-button type="primary" @click="onSave">
            {{ t('app.save') }}
          </el-button>
        </div>
      </div>
    </template>
  </el-dialog>
</template>

<style scoped>
/* ===========================
 * DeviceDialog：设备信息表格面板
 * =========================== */

/* 覆盖 Element Plus 的白色对话框外壳 */
/* 头部：标题 + 副标题始终可见 */
.dd-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
}

.dd-header-main {
  display: flex;
  flex-direction: column;
  gap: var(--iot-space-2xs);
}

.dd-title {
  font-size: var(--iot-font-title);
  font-weight: 600;
  color: #121d39;
}

.dd-subtitle {
  font-size: var(--iot-font-subtitle);
  color: #121d39;
}

.dd-body {
  display: flex;
  flex-direction: column;
  gap: var(--iot-space-md);
}

/* 上半滚动区：所有表格都在这里滚动 */
.dd-body-scroll {
  max-height: 60vh;        /* 真正滚动区域高度（比 70vh 略小一点，为 header/footer 腾空间） */
  overflow-y: auto;
  display: flex;
  flex-direction: column;
  gap: var(--iot-space-md);
  padding-right: 0.15rem;  /* 给滚动条一点余地 */
}

/* Section 标题：深色主题下要明显 */
.dd-section {
  display: flex;
  flex-direction: column;
  gap: var(--iot-space-xs);
  color: #121d39;
}

.dd-section-title {
  font-size: var(--iot-font-subtitle);
  font-weight: 600;
}

/* 表格通用样式（兼容黑白主题） */
.dd-table {
  width: 100%;
  border-collapse: collapse;
  border-spacing: 0;
  font-size: var(--iot-font-base);

}

/* 基本信息表左列宽度固定一点 */
.dd-table-basic th.dd-th-label {
  width: 32%;
}

/* 表头行 */
.dd-table thead th {
  padding: 0.35rem 0.6rem;
  text-align: left;
  font-weight: 600;
  color: #4b515a;
  border-bottom: 1px solid rgba(148, 163, 184, 0.4);
  background: linear-gradient(
      180deg,
      rgba(148, 163, 184, 0.22),
      rgba(148, 163, 184, 0.06)
  );
}

/* 表格内容行 */
.dd-table tbody th,
.dd-table tbody td {
  padding: 0.35rem 0.6rem;
  border-bottom: 1px solid rgba(148, 163, 184, 0.24);
}

/* Basic 表左列 label */
.dd-th-label {
  text-align: left;
  font-weight: 500;
  color: #4b515a;
  border-right: 1px solid rgba(148, 163, 184, 0.35);
}

.dd-td-value {
  color: #121d39;
  font-weight: 600;
}

/* 单元格文本省略号 + tooltip */
.dd-ellipsis {
  display: inline-block;
  max-width: 100%;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.dd-col-desc {
  cursor: help;
}

/* hover 行柔和高亮 */
.dd-table tbody tr:hover td,
.dd-table tbody tr:hover th {
  background-color: rgba(148, 163, 184, 0.08);
}

/* 重命名区域：固定在底部，不跟着上半部分滚动 */
.dd-section-rename {
  padding-top: var(--iot-space-sm);
  margin-top: var(--iot-space-xs);
  border-top: 1px dashed rgba(148, 163, 184, 0.4);
}

/* 重命名输入框：使用统一输入皮肤，避免白底白字 */
.dd-section-rename :deep(.el-input__wrapper) {
  border-radius: var(--iot-radius-input);
}

/* Footer：结构和按钮样式 */
.dd-footer {
  display: flex;
  justify-content: space-between;
  align-items: center;
  gap: var(--iot-space-sm);
  padding: 0 var(--iot-space-lg);
  padding-top: var(--iot-space-sm);
  border-top: 1px solid rgba(148, 163, 184, 0.25);
}

.dd-footer-right {
  display: flex;
  gap: var(--iot-space-xs);
}

/* 按钮统一胶囊形状 */
.dd-footer :deep(.el-button--danger),
.dd-footer :deep(.el-button--primary),
.dd-footer :deep(.el-button:not(.el-button--danger):not(.el-button--primary)) {
  border-radius: 999px;
}

.dd-footer :deep(.el-button--danger),
.dd-footer :deep(.el-button--primary) {
  padding-inline: 1.5rem;
}

.dd-footer :deep(.el-button:not(.el-button--danger):not(.el-button--primary)) {
  padding-inline: 1.25rem;
}
</style>


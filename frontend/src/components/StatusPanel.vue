<script setup lang="ts">
import { computed } from 'vue'
import { useI18n } from 'vue-i18n'
import type {DeviceNode, DeviceEdge, Specification, SpecCondition} from '../types/board'

const props = defineProps<{
  nodes: DeviceNode[]
  edges: DeviceEdge[]
  specifications: Specification[]
  active: string[]
}>()

const emit = defineEmits<{
  (e: 'delete-node', id: string): void
  (e: 'delete-edge', id: string): void
  (e: 'delete-spec', id: string): void
  (e: 'update:active', value: string[]): void
}>()

const { t } = useI18n()

const collapseActive = computed({
  get: () => props.active,
  set: (val: string[]) => emit('update:active', val)
})

// 构造单个条件的短语
const describeCondition = (c: SpecCondition): string => {
  const target =
      c.targetType === 'state'
          ? 'state'
          : c.key || ''  // variable/api 用 key
  // 统一用 "relation value" 的形式
  return `'${c.deviceLabel}' ${target} ${c.relation} '${c.value}'`
}

// 根据 templateId 把整条规约串成一句话
const buildSpecText = (spec: Specification): string => {
  const aPart = spec.aConditions.map(describeCondition).join(' and ')
  const ifPart = spec.ifConditions.map(describeCondition).join(' and ')
  const thenPart = spec.thenConditions.map(describeCondition).join(' and ')

  switch (spec.templateId) {
    case '1':
      // A holds forever
      return `${aPart} holds forever`
    case '2':
      // A will happen later
      return `${aPart} will happen later`
    case '3':
      // A never happens
      return `${aPart} never happens`
    case '4':
      // IF A happens, B should happen at the same time
      return `If ${ifPart} happens, then ${thenPart} should happen at the same time`
    case '5':
      // IF A happens, B should happen later
      return `If ${ifPart} happens, then ${thenPart} should happen later`
    case '6':
      // IF A happens, B should happen later and last forever
      return `If ${ifPart} happens, then ${thenPart} should happen later and last forever`
    case '7':
      // A will not happen because of something untrusted
      return `${aPart} will not happen because of something untrusted`
    default:
      return spec.templateLabel
  }
}
</script>

<template>
  <el-collapse v-model="collapseActive" class="panel-collapse" expand-icon-position="left">
    <!-- 当前设备 -->
    <el-collapse-item name="devices">
      <template #title>
        <span class="card-subtitle">{{ t('app.currentDevices') }}</span>
      </template>
      <el-table
          :data="props.nodes"
          size="small"
          height="160"
          border
          :fit="false"
      >
        <el-table-column
            prop="label"
            :label="t('app.device')"
            min-width="140"
            show-overflow-tooltip
        />
        <el-table-column
            prop="state"
            :label="t('app.state')"
            min-width="100"
            show-overflow-tooltip
        />
        <el-table-column
            :label="t('app.actions')"
            min-width="80"
        >
          <template #default="scope">
            <el-button
                link
                type="danger"
                size="small"
                @click="emit('delete-node', scope.row.id)"
            >
              {{ t('app.delete') }}
            </el-button>
          </template>
        </el-table-column>
      </el-table>
    </el-collapse-item>

    <!-- 当前规则 -->
    <el-collapse-item name="edges">
      <template #title>
        <span class="card-subtitle">{{ t('app.currentRules') }}</span>
      </template>
      <el-table
          :data="props.edges"
          size="small"
          height="160"
          border
          :fit="false"
      >
        <el-table-column
            prop="fromLabel"
            label="from"
            min-width="120"
            show-overflow-tooltip
        />
        <el-table-column
            prop="fromApi"
            label="API"
            min-width="110"
            show-overflow-tooltip
        />
        <el-table-column
            prop="toLabel"
            label="to"
            min-width="120"
            show-overflow-tooltip
        />
        <el-table-column
            prop="toApi"
            label="API"
            min-width="110"
            show-overflow-tooltip
        />
        <el-table-column
            :label="t('app.actions')"
            min-width="80"
        >
          <template #default="scope">
            <el-button
                link
                type="danger"
                size="small"
                @click="emit('delete-edge', scope.row.id)"
            >
              {{ t('app.delete') }}
            </el-button>
          </template>
        </el-table-column>
      </el-table>
    </el-collapse-item>

    <!-- 当前规约 -->
    <el-collapse-item name="specs">
      <template #title>
        <span class="card-subtitle">{{ t('app.currentSpecs') }}</span>
      </template>

      <el-table
          :data="props.specifications"
          size="small"
          height="160"
          border
          :fit="false"
      >
        <el-table-column
            :label="t('app.specContent')"
            min-width="260"
        >
          <template #default="scope">
            <el-tooltip
                placement="top"
                :content="buildSpecText(scope.row)"
                effect="dark"
            >
        <span class="spec-cell-text">
          {{ buildSpecText(scope.row) }}
        </span>
            </el-tooltip>
          </template>
        </el-table-column>

        <el-table-column
            :label="t('app.actions')"
            min-width="80"
        >
          <template #default="scope">
            <el-button
                link
                type="danger"
                size="small"
                @click="emit('delete-spec', scope.row.id)"
            >
              {{ t('app.delete') }}
            </el-button>
          </template>
        </el-table-column>
      </el-table>
    </el-collapse-item>
  </el-collapse>
</template>

<style scoped>
/* ===========================
 * StatusPanel：三张状态表
 * 当前设备 / 规则 / 规约
 * 主要做统一的深色表格皮肤
 * =========================== */
.spec-cell-text {
  display: inline-block;
  max-width: 100%;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

/* 表格整体：透明背景 + 统一边框与文字风格 */
:deep(.el-table) {
  --el-table-bg-color: transparent;
  --el-table-tr-bg-color: transparent;
  --el-table-header-bg-color: transparent;
  --el-table-border-color: var(--iot-color-table-border);

  background-color: transparent;
  color: var(--iot-color-text);
  font-size: var(--iot-font-base);
}

/* 表头 / 单元格：去掉默认白底 */
:deep(.el-table th),
:deep(.el-table td) {
  background-color: transparent !important;
}

/* 表头文字稍弱一些做层次 */
:deep(.el-table th .cell) {
  color: var(--iot-color-text-muted);
  font-weight: 500;
}

/* 单元格：单行显示 + 溢出省略号，避免长文本撑爆布局 */
:deep(.el-table .cell) {
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

/* 悬停高亮行：柔和的蓝色底，视觉上不太“炸” */
:deep(.el-table__row:hover > td) {
  background-color: var(--iot-color-table-row-hover) !important;
}
</style>


<script setup lang="ts">
import { computed } from 'vue'
import { useI18n } from 'vue-i18n'
import type { DeviceNode, DeviceEdge, Specification } from '../types/board'

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
            prop="templateLabel"
            :label="t('app.specTemplateShort')"
            min-width="160"
            show-overflow-tooltip
        />
        <el-table-column
            prop="naturalLanguage"
            :label="t('app.specText')"
            min-width="220"
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

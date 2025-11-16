<script setup lang="ts">
import { ref } from 'vue'
import { useI18n } from 'vue-i18n'
import type { DeviceNode, DeviceEdge, Specification } from '../types/board'

const props = defineProps<{
  nodes: DeviceNode[]
  edges: DeviceEdge[]
  specifications: Specification[]
}>()

const emit = defineEmits<{
  (e: 'delete-node', id: string): void
  (e: 'delete-edge', id: string): void
  (e: 'delete-spec', id: string): void
}>()

const { t } = useI18n()

const statusActive = ref<string[]>(['devices', 'edges', 'specs'])
</script>

<template>
  <div class="card-body">
    <el-collapse v-model="statusActive" class="panel-collapse">
      <!-- 当前设备 -->
      <el-collapse-item name="devices">
        <template #title>
          <span class="card-subtitle">{{ t('app.currentDevices') }}</span>
        </template>
        <el-table :data="props.nodes" size="small" height="160">
          <el-table-column prop="label" :label="t('app.device')" />
          <el-table-column prop="state" :label="t('app.state')" width="80" />
          <el-table-column :label="t('app.actions')" width="70">
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
        <el-table :data="props.edges" size="small" height="160">
          <el-table-column prop="fromLabel" label="from" />
          <el-table-column prop="fromApi" label="API" width="90" />
          <el-table-column prop="toLabel" label="to" />
          <el-table-column prop="toApi" label="API" width="90" />
          <el-table-column :label="t('app.actions')" width="70">
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
        <el-table :data="props.specifications" size="small" height="160">
          <el-table-column
              prop="templateLabel"
              :label="t('app.specTemplateShort')"
              width="140"
          />
          <el-table-column prop="naturalLanguage" :label="t('app.specText')" />
          <el-table-column :label="t('app.actions')" width="70">
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
  </div>
</template>

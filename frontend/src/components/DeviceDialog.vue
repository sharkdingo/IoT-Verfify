<script setup lang="ts">
import { ref, watch } from 'vue'
import { useI18n } from 'vue-i18n'

const props = defineProps<{
  visible: boolean
  deviceName: string
  description: string
  label: string
}>()

const emit = defineEmits<{
  (e: 'update:visible', value: boolean): void
  (e: 'save', newLabel: string): void
  (e: 'delete'): void
}>()

const { t } = useI18n()

const innerVisible = ref(props.visible)
const innerLabel = ref(props.label)

// 同步外部状态到内部
watch(
    () => props.visible,
    val => {
      innerVisible.value = val
    }
)

watch(
    () => props.label,
    val => {
      innerLabel.value = val
    }
)

const close = () => {
  innerVisible.value = false
  emit('update:visible', false)
}

const onSave = () => {
  emit('save', innerLabel.value)
}

const onDelete = () => {
  emit('delete')
}
</script>

<template>
  <el-dialog
      v-model="innerVisible"
      :title="t('app.deviceInfo')"
      width="380px"
      :draggable="true"
      @close="emit('update:visible', false)"
  >
    <el-form label-width="80px" size="small">
      <el-form-item :label="t('app.device')">
        <span>{{ deviceName }}</span>
      </el-form-item>
      <el-form-item :label="t('app.description')">
        <span>{{ description }}</span>
      </el-form-item>
      <el-form-item :label="t('app.name')">
        <el-input v-model="innerLabel" />
      </el-form-item>
    </el-form>

    <template #footer>
      <div class="device-dialog-footer">
        <el-button type="danger" @click="onDelete">
          {{ t('app.deleteDevice') || t('app.delete') }}
        </el-button>
        <div>
          <el-button @click="close">
            {{ t('app.cancel') }}
          </el-button>
          <el-button type="primary" @click="onSave">
            {{ t('app.save') }}
          </el-button>
        </div>
      </div>
    </template>
  </el-dialog>
</template>

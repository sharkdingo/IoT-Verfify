<script setup lang="ts">
import { computed } from 'vue'
import { useI18n } from 'vue-i18n'
import { useModalAccessibility } from '@/composables/useModalAccessibility'

const { t } = useI18n()

const props = withDefaults(defineProps<{
  visible: boolean
  loading?: boolean
}>(), {
  loading: false
})

const emit = defineEmits<{
  'update:visible': [value: boolean]
  'confirm': []
  'cancel': []
  'delete-account': []
}>()

const handleConfirm = () => {
  if (props.loading) return
  emit('confirm')
}

const handleCancel = () => {
  if (props.loading) return
  emit('cancel')
  emit('update:visible', false)
}

const handleDeleteAccount = () => {
  if (props.loading) return
  emit('delete-account')
  emit('update:visible', false)
}

const isDialogOpen = computed(() => props.visible)
const { setDialogRef, handleModalKeydown } = useModalAccessibility(isDialogOpen, handleCancel)
</script>

<template>
  <Teleport to="body">
    <Transition name="iot-dialog">
      <div
        v-if="visible"
        class="iot-dialog-overlay iot-dialog-overlay--session"
        @click.self="handleCancel"
        @keydown="handleModalKeydown"
      >
        <div
          :ref="setDialogRef"
          class="iot-dialog iot-dialog--sm"
          role="dialog"
          aria-modal="true"
          aria-labelledby="logout-dialog-title"
          tabindex="-1"
        >
          <div class="iot-dialog__header">
            <div class="iot-dialog__icon">
              <span class="material-symbols-outlined" aria-hidden="true">logout</span>
            </div>
            <div class="iot-dialog__heading">
              <h2 id="logout-dialog-title" class="iot-dialog__title">{{ t('app.logoutTitle') }}</h2>
            </div>
          </div>

          <div class="iot-dialog__body">{{ t('app.logoutMessage') }}</div>

          <div class="iot-dialog__footer">
            <!-- The only route to account deletion, so it needs to be addressable — but it is not one of
                 the two answers to this question, so it sits apart from the pair. -->
            <button
              type="button"
              class="iot-dialog-btn iot-dialog-btn--quiet iot-dialog__footer-aside"
              data-testid="open-account-delete"
              :disabled="loading"
              @click="handleDeleteAccount"
            >
              {{ t('app.deleteAccountEntry') }}
            </button>
            <button type="button" class="iot-dialog-btn iot-dialog-btn--ghost" @click="handleCancel" :disabled="loading">
              {{ t('app.cancel') }}
            </button>
            <button type="button" class="iot-dialog-btn iot-dialog-btn--primary" @click="handleConfirm" :disabled="loading">
              <span v-if="loading" class="iot-dialog-btn__spinner" aria-hidden="true"></span>
              <span v-else>{{ t('app.logout') }}</span>
            </button>
          </div>
        </div>
      </div>
    </Transition>
  </Teleport>
</template>

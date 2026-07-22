<script setup lang="ts">
import { computed, reactive, ref, watch } from 'vue'
import { useI18n } from 'vue-i18n'
import { useModalAccessibility } from '@/composables/useModalAccessibility'
import { normalizeAccountIdentifier } from '@/utils/accountIdentifier'

const { t } = useI18n()

const props = withDefaults(defineProps<{
  visible: boolean
  username?: string
  phone?: string
  loading?: boolean
}>(), {
  username: '',
  phone: '',
  loading: false
})

const emit = defineEmits<{
  'update:visible': [value: boolean]
  'confirm': [payload: { password: string; confirmation: string }]
  'cancel': []
}>()

const form = reactive({
  confirmation: '',
  password: ''
})
const confirmationWasEdited = ref(false)
let confirmationEditPending = false

const confirmationHint = computed(() => t('app.deleteAccountConfirmationHint'))
const confirmationMatches = computed(() => {
  const value = normalizeAccountIdentifier(form.confirmation)
  return value.length > 0 && (value === props.username || value === props.phone)
})
const canConfirm = computed(() => confirmationWasEdited.value
  && confirmationMatches.value
  && form.password.length > 0
  && !props.loading)

const markConfirmationEditIntent = () => {
  confirmationEditPending = true
}

const markConfirmationEditIntentByKeyboard = (event: KeyboardEvent) => {
  if (event.isComposing || event.ctrlKey || event.metaKey || event.altKey) return
  if (event.key.length === 1 || event.key === 'Backspace' || event.key === 'Delete') {
    markConfirmationEditIntent()
  }
}

const confirmConfirmationEdited = () => {
  if (!confirmationEditPending) return
  confirmationWasEdited.value = true
  confirmationEditPending = false
}

const resetForm = () => {
  form.confirmation = ''
  form.password = ''
  confirmationWasEdited.value = false
  confirmationEditPending = false
}

const handleCancel = () => {
  if (props.loading) return
  emit('cancel')
  emit('update:visible', false)
  resetForm()
}

const handleConfirm = () => {
  if (!canConfirm.value) return
  emit('confirm', {
    password: form.password,
    confirmation: normalizeAccountIdentifier(form.confirmation)
  })
}

watch(() => props.visible, () => {
  resetForm()
})

const isDialogOpen = computed(() => props.visible)
const { setDialogRef, handleModalKeydown } = useModalAccessibility(isDialogOpen, handleCancel)
</script>

<template>
  <Teleport to="body">
    <Transition name="account-delete-dialog">
      <div
        v-if="visible"
        class="account-delete-overlay"
        @click.self="handleCancel"
        @keydown="handleModalKeydown"
      >
        <form
          :ref="setDialogRef"
          class="account-delete-dialog"
          role="dialog"
          aria-modal="true"
          aria-labelledby="account-delete-title"
          tabindex="-1"
          @submit.prevent="handleConfirm"
        >
          <div class="account-delete-icon">
            <span class="material-symbols-outlined" aria-hidden="true">person_remove</span>
          </div>

          <div class="account-delete-copy">
            <h2 id="account-delete-title">{{ t('app.deleteAccountTitle') }}</h2>
            <p>{{ t('app.deleteAccountMessage') }}</p>
          </div>

          <div class="account-delete-warning">
            <span class="material-symbols-outlined" aria-hidden="true">warning</span>
            <span>{{ t('app.deleteAccountDataWarning') }}</span>
          </div>

          <label class="account-delete-field">
            <span>{{ t('app.deleteAccountConfirmationLabel') }}</span>
            <input
              v-model="form.confirmation"
              type="text"
              autocomplete="off"
              name="delete-account-confirmation"
              data-1p-ignore
              data-lpignore="true"
              :placeholder="t('app.deleteAccountConfirmationPlaceholder')"
              :aria-invalid="Boolean(form.confirmation) && !confirmationMatches"
              :disabled="loading"
              @keydown="markConfirmationEditIntentByKeyboard"
              @paste="markConfirmationEditIntent"
              @compositionstart="markConfirmationEditIntent"
              @input="confirmConfirmationEdited"
            >
            <small :class="{ danger: form.confirmation && !confirmationMatches }">
              {{ confirmationHint }}
            </small>
          </label>

          <label class="account-delete-field">
            <span>{{ t('auth.password') }}</span>
            <input
              v-model="form.password"
              type="password"
              autocomplete="current-password"
              :placeholder="t('app.deleteAccountPasswordPlaceholder')"
              :disabled="loading"
            >
          </label>

          <div class="account-delete-actions">
            <button type="button" class="account-delete-btn secondary" :disabled="loading" @click="handleCancel">
              {{ t('app.cancel') }}
            </button>
            <button type="submit" class="account-delete-btn danger" :disabled="!canConfirm">
              <span v-if="loading" class="account-delete-spinner" aria-hidden="true"></span>
              <span v-else>{{ t('app.deleteAccountConfirm') }}</span>
            </button>
          </div>
        </form>
      </div>
    </Transition>
  </Teleport>
</template>

<style scoped>
.account-delete-overlay {
  position: fixed;
  inset: 0;
  z-index: 10000;
  display: flex;
  align-items: center;
  justify-content: center;
  padding: 1rem;
  overflow-y: auto;
  overscroll-behavior: contain;
  background: color-mix(in srgb, var(--text, #0f172a) 56%, transparent);
  backdrop-filter: blur(5px);
}

.account-delete-dialog {
  box-sizing: border-box;
  width: min(100%, 28rem);
  max-height: calc(100vh - 2rem);
  max-height: calc(100dvh - 2rem);
  margin: auto;
  padding: 1.5rem;
  overflow-y: auto;
  overscroll-behavior: contain;
  scrollbar-gutter: stable;
  border: 1px solid color-mix(in srgb, #ef4444 28%, var(--border, #e2e8f0));
  border-radius: 1.25rem;
  background: var(--surface-overlay, #ffffff);
  color: var(--text, #0f172a);
  box-shadow: 0 24px 60px rgba(15, 23, 42, 0.28);
}

.account-delete-icon {
  width: 3.5rem;
  height: 3.5rem;
  margin: 0 auto 1rem;
  display: grid;
  place-items: center;
  border-radius: 999px;
  background: color-mix(in srgb, #ef4444 14%, var(--surface-muted, #f8fafc));
  color: #dc2626;
}

.account-delete-icon .material-symbols-outlined {
  font-size: 1.85rem;
}

.account-delete-copy {
  text-align: center;
}

.account-delete-copy h2 {
  margin: 0;
  font-size: 1.25rem;
  font-weight: 800;
}

.account-delete-copy p {
  margin: 0.5rem 0 0;
  color: var(--text-muted, #64748b);
  font-size: 0.9rem;
  line-height: 1.55;
}

.account-delete-warning {
  display: flex;
  gap: 0.5rem;
  margin: 1.25rem 0;
  padding: 0.75rem;
  border: 1px solid color-mix(in srgb, #ef4444 30%, var(--border, #e2e8f0));
  border-radius: 0.875rem;
  background: color-mix(in srgb, #ef4444 8%, var(--surface-muted, #f8fafc));
  color: #b91c1c;
  font-size: 0.8rem;
  line-height: 1.45;
}

.account-delete-warning .material-symbols-outlined {
  flex: 0 0 auto;
  font-size: 1.1rem;
}

.account-delete-field {
  display: block;
  margin-top: 0.85rem;
  font-size: 0.78rem;
  font-weight: 700;
  color: var(--text-muted, #64748b);
}

.account-delete-field input {
  width: 100%;
  margin-top: 0.4rem;
  padding: 0.7rem 0.8rem;
  border: 1px solid var(--border, #cbd5e1);
  border-radius: 0.75rem;
  background: var(--surface, #ffffff);
  color: var(--text, #0f172a);
  font-size: 0.9rem;
  outline: none;
}

.account-delete-field input:focus {
  border-color: #ef4444;
  box-shadow: 0 0 0 3px color-mix(in srgb, #ef4444 16%, transparent);
}

.account-delete-field input[aria-invalid="true"] {
  border-color: #ef4444;
}

.account-delete-field small {
  display: block;
  margin-top: 0.35rem;
  color: var(--text-muted, #64748b);
  font-weight: 500;
  line-height: 1.4;
}

.account-delete-field small.danger {
  color: #dc2626;
}

.account-delete-actions {
  display: flex;
  gap: 0.75rem;
  margin-top: 1.25rem;
}

.account-delete-btn {
  flex: 1;
  min-height: 2.75rem;
  border: 0;
  border-radius: 0.85rem;
  font-size: 0.9rem;
  font-weight: 800;
  cursor: pointer;
  transition: transform 0.18s ease, opacity 0.18s ease, background 0.18s ease;
}

.account-delete-btn:not(:disabled):active {
  transform: scale(0.98);
}

.account-delete-btn.secondary {
  background: var(--surface-muted, #f1f5f9);
  color: var(--text-muted, #475569);
  border: 1px solid var(--border, #cbd5e1);
}

.account-delete-btn.danger {
  background: #dc2626;
  color: #ffffff;
  box-shadow: 0 12px 24px rgba(220, 38, 38, 0.24);
}

.account-delete-btn:disabled {
  cursor: not-allowed;
  opacity: 0.58;
}

.account-delete-spinner {
  display: inline-block;
  width: 1rem;
  height: 1rem;
  border: 2px solid rgba(255, 255, 255, 0.35);
  border-top-color: #ffffff;
  border-radius: 999px;
  animation: account-delete-spin 0.8s linear infinite;
}

@keyframes account-delete-spin {
  to { transform: rotate(360deg); }
}

.account-delete-dialog-enter-active,
.account-delete-dialog-leave-active {
  transition: opacity 0.2s ease;
}

.account-delete-dialog-enter-from,
.account-delete-dialog-leave-to {
  opacity: 0;
}
</style>

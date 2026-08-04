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

const confirmationHint = computed(() => t('app.deleteAccountConfirmationHint'))
const confirmationMatches = computed(() => {
  const value = normalizeAccountIdentifier(form.confirmation)
  return value.length > 0 && (value === props.username || value === props.phone)
})
const canConfirm = computed(() => confirmationWasEdited.value
  && confirmationMatches.value
  && form.password.length > 0
  && !props.loading)

/**
 * Requires the confirmation text to have been entered through a real edit, so a password manager
 * filling the field cannot satisfy the typed-confirmation gate on its own.
 *
 * Keyed on `InputEvent.inputType` rather than on preceding keystrokes: every genuine edit reports
 * one — including Android soft keyboards, which report `KeyboardEvent.key` as `Unidentified`, and
 * dropped text, which fires no keydown at all. Gating on printable keys left the delete button
 * permanently disabled in both cases, with nothing on screen explaining why. Programmatic value
 * assignment fires a plain `Event` with no `inputType`, which is what this rejects.
 */
const confirmConfirmationEdited = (event: Event) => {
  if (event instanceof InputEvent && event.inputType) confirmationWasEdited.value = true
}

const resetForm = () => {
  form.confirmation = ''
  form.password = ''
  confirmationWasEdited.value = false
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
          data-testid="account-delete-dialog"
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

          <!--
            What can still be saved, stated honestly.

            The product already has a scene export — `buildSceneExport` writes templates, devices, the
            Environment Pool, rules and specifications to a portable JSON file — and this dialog never mentioned
            it. All three reviews asked for exactly that: "there is no visible export/download or backup action
            before irreversible deletion. I would want a way to export boards, rules, specifications, runs, and
            counterexamples."

            Two of those cannot be exported, so the note says so rather than implying a full backup. Run history
            and counterexamples are *results* — reproducible by re-running against an exported design, but not
            themselves portable. Offering "export everything" here would be the more comforting message and the
            false one, and on the one screen where a user is deciding whether to destroy their work, an overstated
            reassurance is worse than none.
          -->
          <p class="account-delete-export-note" data-testid="account-delete-export-note">
            <span class="material-symbols-outlined" aria-hidden="true">download</span>
            <span>{{ t('app.deleteAccountExportHint') }}</span>
          </p>

          <label class="account-delete-field">
            <span>{{ t('app.deleteAccountConfirmationLabel') }}</span>
            <input
              v-model="form.confirmation"
              type="text"
              autocomplete="off"
              name="delete-account-confirmation"
              data-testid="account-delete-confirmation"
              data-1p-ignore
              data-lpignore="true"
              :placeholder="t('app.deleteAccountConfirmationPlaceholder')"
              :aria-invalid="Boolean(form.confirmation) && !confirmationMatches"
              :disabled="loading"
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
              data-testid="account-delete-password"
              :placeholder="t('app.deleteAccountPasswordPlaceholder')"
              :disabled="loading"
            >
          </label>

          <!-- Test ids on the controls of the product's one irreversible action.
               They were absent, so nothing outside this component could address the dialog: a browser check
               looking for the delete flow found no route to it and reported the affordance missing. A
               destructive action is the last thing that should be unaddressable by a test. -->
          <div class="account-delete-actions">
            <button
              type="button"
              class="account-delete-btn secondary"
              data-testid="account-delete-cancel"
              :disabled="loading"
              @click="handleCancel"
            >
              {{ t('app.cancel') }}
            </button>
            <button
              type="submit"
              class="account-delete-btn danger"
              data-testid="account-delete-confirm"
              :disabled="!canConfirm"
            >
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
  z-index: var(--z-session-modal);
  display: flex;
  align-items: center;
  justify-content: center;
  padding: 1rem;
  overflow-y: auto;
  overscroll-behavior: contain;
  background: color-mix(in srgb, var(--text, var(--text)) 56%, transparent);
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
  border: 1px solid color-mix(in srgb, var(--danger) 28%, var(--border, var(--border)));
  border-radius: 1.25rem;
  background: var(--surface-overlay);
  color: var(--text, var(--text));
  box-shadow: 0 24px 60px rgba(15, 23, 42, 0.28);
}

.account-delete-icon {
  width: 3.5rem;
  height: 3.5rem;
  margin: 0 auto 1rem;
  display: grid;
  place-items: center;
  border-radius: 999px;
  background: color-mix(in srgb, var(--danger) 14%, var(--surface-muted));
  color: var(--danger);
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
  color: var(--text-muted, var(--text-muted));
  font-size: 0.9rem;
  line-height: 1.55;
}

.account-delete-warning {
  display: flex;
  gap: 0.5rem;
  margin: 1.25rem 0;
  padding: 0.75rem;
  border: 1px solid color-mix(in srgb, var(--danger) 30%, var(--border, var(--border)));
  border-radius: 0.875rem;
  background: color-mix(in srgb, var(--danger) 8%, var(--surface-muted));
  color: var(--danger);
  font-size: 0.8rem;
  line-height: 1.45;
}

/* The export note sits below the warning and is deliberately quieter than it: it is a way out, not another
   alarm. Two danger-coloured blocks stacked would make neither read as the more urgent. */
.account-delete-export-note {
  display: flex;
  gap: 0.5rem;
  align-items: flex-start;
  margin: -0.5rem 0 1.25rem;
  padding: 0.625rem 0.75rem;
  border: 1px solid var(--border);
  border-radius: 0.875rem;
  background: var(--surface-muted);
  color: var(--text-muted);
  font-size: 0.8125rem;
  line-height: 1.45;
}

.account-delete-export-note .material-symbols-outlined {
  flex: 0 0 auto;
  font-size: 1.05rem;
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
  color: var(--text-muted, var(--text-muted));
}

.account-delete-field input {
  width: 100%;
  margin-top: 0.4rem;
  padding: 0.7rem 0.8rem;
  border: 1px solid var(--border, var(--border-strong));
  border-radius: 0.75rem;
  background: var(--surface);
  color: var(--text, var(--text));
  font-size: 0.9rem;
  outline: none;
}

.account-delete-field input:focus {
  border-color: var(--danger);
  box-shadow: 0 0 0 3px color-mix(in srgb, var(--danger) 16%, transparent);
}

.account-delete-field input[aria-invalid="true"] {
  border-color: var(--danger);
}

.account-delete-field small {
  display: block;
  margin-top: 0.35rem;
  color: var(--text-muted, var(--text-muted));
  font-weight: 500;
  line-height: 1.4;
}

.account-delete-field small.danger {
  color: var(--danger);
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
  background: var(--surface-muted);
  color: var(--text-muted);
  border: 1px solid var(--border, var(--border-strong));
}

.account-delete-btn.danger {
  background: var(--danger-fill);
  color: #ffffff;
  box-shadow: 0 12px 24px rgba(220, 38, 38, 0.24);
}

/* A disarmed destructive button must look disarmed.
 *
 * `opacity: 0.58` alone left the danger button saturated red *and* still wearing its
 * `box-shadow: 0 12px 24px rgba(220,38,38,.24)` glow, so at 58% it read as armed. All three reviews of this
 * dialog said so — "'Delete Permanently' appears enabled even though both confirmation fields are empty" —
 * while measurement showed `disabled: true` in every case. The button was correct and its appearance was not,
 * which is the worse of the two failures on the product's only irreversible action: a user who believes the
 * control is live cannot tell whether their click was ignored or is about to destroy their work.
 *
 * Dropping the glow and the fill's saturation makes the state legible without relying on opacity alone. */
.account-delete-btn:disabled {
  cursor: not-allowed;
  opacity: 0.58;
  box-shadow: none;
}

.account-delete-btn.danger:disabled {
  /* Mixed toward the surface rather than merely faded, so the fill itself stops reading as a live danger
     colour. The `opacity` above then softens what is already a muted button instead of dimming a saturated
     one. */
  background: color-mix(in srgb, var(--danger) 34%, var(--surface-elevated));
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

<script setup lang="ts">
import { onErrorCaptured, ref, watch } from 'vue'
import { useI18n } from 'vue-i18n'

const props = defineProps<{ resetKey?: string | number }>()
const { t } = useI18n()
const capturedError = ref<unknown>(null)
const renderEpoch = ref(0)

onErrorCaptured((error, _instance, info) => {
  capturedError.value = error
  console.error('Vue subtree failed to render:', info, error)
  return false
})

watch(() => props.resetKey, () => {
  capturedError.value = null
  renderEpoch.value += 1
})

const retry = () => {
  capturedError.value = null
  renderEpoch.value += 1
}

const reloadPage = () => window.location.reload()
</script>

<template>
  <template v-if="capturedError === null">
    <div :key="renderEpoch" class="error-boundary-content">
      <slot />
    </div>
  </template>
  <section v-else class="error-boundary-fallback" role="alert">
    <div class="error-boundary-fallback__icon" aria-hidden="true">error_outline</div>
    <h2>{{ t('app.viewErrorTitle') }}</h2>
    <p>{{ t('app.viewErrorDescription') }}</p>
    <div class="error-boundary-fallback__actions">
      <button type="button" class="error-boundary-fallback__button error-boundary-fallback__button--primary" @click="retry">
        {{ t('app.retry') }}
      </button>
      <button type="button" class="error-boundary-fallback__button" @click="reloadPage">
        {{ t('app.reloadPage') }}
      </button>
    </div>
  </section>
</template>

<style scoped>
.error-boundary-content {
  display: contents;
}

.error-boundary-fallback {
  min-height: 220px;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  gap: 12px;
  padding: 32px;
  color: var(--text);
  text-align: center;
  background: var(--surface);
}

.error-boundary-fallback__icon {
  color: var(--danger);
  font-family: 'Material Symbols Outlined';
  font-size: 42px;
}

.error-boundary-fallback h2,
.error-boundary-fallback p {
  margin: 0;
}

.error-boundary-fallback p {
  max-width: 520px;
  color: var(--text-muted);
}

.error-boundary-fallback__actions {
  display: flex;
  flex-wrap: wrap;
  justify-content: center;
  gap: 10px;
  margin-top: 8px;
}

.error-boundary-fallback__button {
  min-height: 38px;
  padding: 8px 16px;
  border: 1px solid var(--border-strong);
  border-radius: var(--iot-radius-control);
  background: var(--surface-elevated);
  color: var(--text);
  cursor: pointer;
}

.error-boundary-fallback__button--primary {
  border-color: var(--accent-fill);
  /* Base state, so the base fill — my first pass mapped `--accent-strong` to the hover half, but this is not
     a hover. `--accent-strong` is the *text* accent's strong variant, and white ink on it measured 1.80:1 in
     dark theme. */
  background: var(--accent-fill);
  color: #ffffff;
}
</style>

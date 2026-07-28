<script setup lang="ts">
/**
 * Accessible on/off control for board run settings.
 *
 * Uses `role="switch"` + `aria-checked` so assistive technology can read the state; the
 * hand-rolled `<button>` variants this replaces exposed no name and no state at all.
 * `label` is the control's accessible name — pass the same text the adjacent visual
 * label shows, and link the description with `describedbyId` when one exists.
 */
withDefaults(defineProps<{
  checked: boolean
  label: string
  tone?: 'red' | 'purple' | 'cyan' | 'blue'
  disabled?: boolean
  title?: string
  describedbyId?: string
  testId?: string
}>(), {
  tone: 'blue',
  disabled: false,
  title: undefined,
  describedbyId: undefined,
  testId: undefined
})

const emit = defineEmits<{ (e: 'change', checked: boolean): void }>()
</script>

<template>
  <button
    type="button"
    role="switch"
    :aria-checked="checked"
    :aria-label="label"
    :aria-describedby="describedbyId"
    :data-testid="testId"
    :disabled="disabled"
    :title="title"
    class="iot-toggle-switch"
    :class="[`iot-toggle-switch--${tone}`, { 'iot-toggle-switch--on': checked }]"
    @click="emit('change', !checked)"
  >
    <span class="iot-toggle-switch__thumb" aria-hidden="true" />
  </button>
</template>

<style scoped>
.iot-toggle-switch {
  position: relative;
  display: inline-flex;
  align-items: center;
  flex: 0 0 auto;
  width: 2.75rem;
  height: 1.5rem;
  padding: 0;
  border: 0;
  border-radius: 999px;
  background: #cbd5e1;
  cursor: pointer;
  transition: background-color 0.2s ease;
}

.iot-toggle-switch:disabled {
  cursor: not-allowed;
  opacity: 0.6;
}

.iot-toggle-switch--on.iot-toggle-switch--red { background: #ef4444; }
.iot-toggle-switch--on.iot-toggle-switch--purple { background: #a855f7; }
.iot-toggle-switch--on.iot-toggle-switch--cyan { background: #0891b2; }
.iot-toggle-switch--on.iot-toggle-switch--blue { background: #3b82f6; }

.iot-toggle-switch__thumb {
  position: absolute;
  left: 0.25rem;
  width: 1rem;
  height: 1rem;
  border-radius: 999px;
  background: #fff;
  box-shadow: 0 1px 3px rgba(15, 23, 42, 0.4);
  transition: transform 0.2s ease;
}

.iot-toggle-switch--on .iot-toggle-switch__thumb {
  transform: translateX(1.25rem);
}

@media (prefers-reduced-motion: reduce) {
  .iot-toggle-switch,
  .iot-toggle-switch__thumb {
    transition: none;
  }
}
</style>

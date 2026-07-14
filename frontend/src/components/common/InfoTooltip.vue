<script setup lang="ts">
import { ElTooltip } from 'element-plus'
import 'element-plus/theme-chalk/el-popper.css'
import 'element-plus/theme-chalk/el-tooltip.css'

withDefaults(defineProps<{
  text: string
  label: string
  placement?: 'top' | 'top-start' | 'top-end' | 'bottom' | 'bottom-start' | 'bottom-end' | 'left' | 'right'
  tone?: 'neutral' | 'danger' | 'privacy' | 'amber'
  testId?: string
}>(), {
  placement: 'top',
  tone: 'neutral',
  testId: undefined
})
</script>

<template>
  <ElTooltip
    :content="text"
    :placement="placement"
    :trigger="['hover', 'focus', 'click']"
    :show-after="120"
    :hide-after="80"
    :enterable="true"
    :teleported="true"
    popper-class="iot-info-tooltip-popper"
  >
    <button
      type="button"
      class="iot-info-tooltip-trigger"
      :class="`iot-info-tooltip-trigger--${tone}`"
      :data-testid="testId"
      :aria-label="label"
      @click.stop
    >
      <span class="material-symbols-outlined" aria-hidden="true">info</span>
    </button>
  </ElTooltip>
</template>

<style scoped>
.iot-info-tooltip-trigger {
  display: inline-flex;
  width: 1.5rem;
  height: 1.5rem;
  flex: 0 0 auto;
  align-items: center;
  justify-content: center;
  border: 1px solid color-mix(in srgb, currentColor 28%, transparent);
  border-radius: 999px;
  background: color-mix(in srgb, currentColor 8%, white);
  color: #475569;
  transition: background-color 0.15s ease, border-color 0.15s ease, color 0.15s ease;
}

.iot-info-tooltip-trigger:hover,
.iot-info-tooltip-trigger:focus-visible {
  border-color: currentColor;
  background: color-mix(in srgb, currentColor 14%, white);
  outline: none;
}

.iot-info-tooltip-trigger .material-symbols-outlined {
  font-size: 0.95rem;
}

.iot-info-tooltip-trigger--danger {
  color: #dc2626;
}

.iot-info-tooltip-trigger--privacy {
  color: #7e22ce;
}

.iot-info-tooltip-trigger--amber {
  color: #b45309;
}

:global(.dark) .iot-info-tooltip-trigger {
  background: color-mix(in srgb, currentColor 14%, #0f172a);
}

:global(.iot-info-tooltip-popper) {
    max-width: min(24rem, calc(100vw - 2rem));
    white-space: pre-line;
    line-height: 1.5;
    letter-spacing: 0;
}
</style>

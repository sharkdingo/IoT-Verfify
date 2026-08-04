<script setup lang="ts">
import { ElTooltip } from 'element-plus'
import 'element-plus/theme-chalk/el-popper.css'
import 'element-plus/theme-chalk/el-tooltip.css'

withDefaults(defineProps<{
  text: string
  label: string
  placement?: 'top' | 'top-start' | 'top-end' | 'bottom' | 'bottom-start' | 'bottom-end' | 'left' | 'right'
  /**
   * What the help concerns, not what colour to paint.
   *
   * `amber` was the odd one out — a colour name beside three meanings — and it was used for the
   * Environment Pool's help icon, where two independent reviews read the warm tint as an unresolved
   * warning on an otherwise informational panel. Help about ordinary state is `neutral`; `caution` is
   * reserved for help that genuinely warns, so the colour claim has to be earned.
   */
  tone?: 'neutral' | 'danger' | 'sensitivity' | 'caution'
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
/* A 44px hit area around a 24px badge.
 *
 * The trigger measured 24×24px — the smallest control anywhere in the System Inspector, and a help affordance is
 * exactly the thing a confused user reaches for. The visible badge stays 1.5rem, because a 44px circle would read
 * as a button competing with the content it annotates; the target grows instead, via padding that the surrounding
 * flex layouts absorb.
 *
 * `background-clip: content-box` keeps the padding transparent, so the badge still looks 24px while the pointer
 * and touch target are 44px. */
.iot-info-tooltip-trigger {
  display: inline-flex;
  box-sizing: content-box;
  width: 1.5rem;
  height: 1.5rem;
  padding: 0.625rem;
  margin: -0.625rem;
  background-clip: content-box;
  flex: 0 0 auto;
  align-items: center;
  justify-content: center;
  border: 1px solid color-mix(in srgb, currentColor 28%, transparent);
  border-radius: 999px;
  /* Theme token, not `white`: the hardcoded blend made the dark override below the only rule that
     could set a usable background, which in turn outranked hover/focus and killed both cues. */
  background: color-mix(in srgb, currentColor 8%, var(--surface-elevated));
  color: var(--text-muted);
  transition: background-color 0.15s ease, border-color 0.15s ease, color 0.15s ease;
}

.iot-info-tooltip-trigger:hover,
.iot-info-tooltip-trigger:focus-visible {
  border-color: currentColor;
  background: color-mix(in srgb, currentColor 22%, var(--surface-elevated));
}

/* A real focus ring: the hover background alone is too subtle to serve as the keyboard cue, and
   suppressing the outline left keyboard users with nothing. */
.iot-info-tooltip-trigger:focus-visible {
  outline: 2px solid color-mix(in srgb, currentColor 75%, transparent);
  outline-offset: 2px;
}

.iot-info-tooltip-trigger .material-symbols-outlined {
  font-size: 0.95rem;
}

/* Token-driven rather than three private hex literals, which stayed at their light-theme values in
   dark and were invisible to the shared contrast work. */
.iot-info-tooltip-trigger--danger {
  color: var(--danger);
}

.iot-info-tooltip-trigger--sensitivity {
  color: var(--accent-strong);
}

.iot-info-tooltip-trigger--caution {
  color: var(--warning);
}

/* No dark-theme background override is needed any more: `--surface-elevated` already differs per
   theme. The old `[data-theme='dark']` rule was more specific than :hover/:focus-visible, so it
   silently disabled both in dark mode. */

:global(.iot-info-tooltip-popper) {
    max-width: min(24rem, calc(100vw - 2rem));
    white-space: pre-line;
    line-height: 1.5;
    letter-spacing: 0;
}
</style>

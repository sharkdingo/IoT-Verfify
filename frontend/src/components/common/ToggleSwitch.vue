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
  /**
   * What being *on* means, not what colour to paint.
   *
   * The prop was `'red' | 'purple' | 'cyan' | 'blue'` — colour names, so the call site said "purple"
   * when it meant "privacy", and three of the four values were not even in the declared union yet were
   * passed anyway. `enabled` is the default because a switch's on-state carries one meaning; the two
   * exceptions are real analysis dimensions the product treats as distinct, per the convention that
   * colour distinguishes *kind*:
   *  - `adversarial` — attack analysis, which changes what the model admits
   *  - `sensitivity` — privacy/sensitivity propagation
   * A preference such as "save this run to history" is not a kind, so it takes `enabled`.
   */
  tone?: 'enabled' | 'adversarial' | 'sensitivity'
  disabled?: boolean
  title?: string
  describedbyId?: string
  testId?: string
}>(), {
  tone: 'enabled',
  disabled: false,
  title: undefined,
  describedbyId: undefined,
  testId: undefined
})

const emit = defineEmits<{ (e: 'change', checked: boolean): void }>()
</script>

<template>
  <!-- `title` stays a prop: three call sites pass a *conditional* hint that explains why the switch is
       disabled, so the hint is the caller's to decide. `HintTooltip` disables itself on an empty value, which
       is why those callers can keep passing `undefined` with no `v-if`. -->
  <HintTooltip :content="title">
    <button
      type="button"
      role="switch"
      :aria-checked="checked"
      :aria-label="label"
      :aria-describedby="describedbyId"
      :data-testid="testId"
      :disabled="disabled"
      class="iot-toggle-switch"
      :class="[`iot-toggle-switch--${tone}`, { 'iot-toggle-switch--on': checked }]"
      @click="emit('change', !checked)"
    >
      <span class="iot-toggle-switch__thumb" aria-hidden="true" />
    </button>
  </HintTooltip>
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
  border-radius: var(--iot-radius-pill);
  /* Was a private grey literal that stayed light in dark theme, so an off switch glowed against the
     dark panel instead of receding. */
  background: var(--border);
  cursor: pointer;
  transition: background-color 0.2s ease;
}

.iot-toggle-switch:disabled {
  cursor: not-allowed;
  opacity: 0.6;
}

/* The on-state colours come from the shared tokens rather than four private hex values, so this
   control follows the theme instead of carrying its own palette. */
.iot-toggle-switch--on.iot-toggle-switch--enabled { background: var(--accent); }
.iot-toggle-switch--on.iot-toggle-switch--adversarial { background: var(--danger); }
.iot-toggle-switch--on.iot-toggle-switch--sensitivity { background: var(--accent-strong); }

.iot-toggle-switch__thumb {
  position: absolute;
  left: 0.25rem;
  width: 1rem;
  height: 1rem;
  border-radius: var(--iot-radius-pill);
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

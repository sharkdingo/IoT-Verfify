<script setup lang="ts">
import { computed } from 'vue'
import { useI18n } from 'vue-i18n'
import { useTheme } from '@/composables/useTheme'

type Tone = 'light' | 'dark' | 'glass'

withDefaults(defineProps<{
  tone?: Tone
  compact?: boolean
}>(), {
  tone: 'light',
  compact: false
})

const { t } = useI18n()
const { theme, followsSystem, cycleThemeMode } = useTheme()

// Three-state control: the label names the *current* mode so the state is readable,
// while aria-label names the next mode so the action is announced.
const currentModeLabel = computed(() => {
  if (followsSystem.value) return t('app.systemTheme')
  return theme.value === 'dark' ? t('app.darkTheme') : t('app.lightTheme')
})
const currentModeDescription = computed(() => {
  if (followsSystem.value) return t('app.themeModeSystem')
  return theme.value === 'dark' ? t('app.themeModeDark') : t('app.themeModeLight')
})
const iconName = computed(() => {
  if (followsSystem.value) return 'brightness_auto'
  return theme.value === 'dark' ? 'dark_mode' : 'light_mode'
})
</script>

<template>
  <button
    type="button"
    class="theme-toggle"
    :class="[
      `theme-toggle--${tone}`,
      { 'theme-toggle--compact': compact }
    ]"
    :title="`${currentModeDescription} — ${t('app.switchTheme')}`"
    :aria-label="`${currentModeDescription} — ${t('app.switchTheme')}`"
    @click="cycleThemeMode"
  >
    <span class="material-symbols-outlined theme-toggle__icon" aria-hidden="true">{{ iconName }}</span>
    <span class="theme-toggle__label">{{ currentModeLabel }}</span>
  </button>
</template>

<style scoped>
.theme-toggle {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  gap: 6px;
  min-width: 104px;
  height: 36px;
  padding: 0 12px;
  border-radius: var(--iot-radius-pill);
  border: 1px solid transparent;
  font-size: 0.875rem;
  font-weight: 700;
  line-height: 1;
  cursor: pointer;
  transition:
    transform 0.18s ease,
    box-shadow 0.18s ease,
    background-color 0.18s ease,
    border-color 0.18s ease;
}

.theme-toggle:hover {
  transform: translateY(-1px);
}

.theme-toggle:active {
  transform: translateY(0);
}

.theme-toggle:focus-visible {
  outline: 3px solid var(--accent-border);
  outline-offset: 2px;
}

.theme-toggle__icon {
  font-size: 18px;
  line-height: 1;
}

.theme-toggle__label {
  /* `min-width` keeps the button from jumping as the label changes between modes, but the label must
     still be allowed to grow past it: "跟随系统" needs 56px and was clipped to 42px, so the control
     that reports the current theme could not state which theme was current. `flex-shrink: 0` stops a
     tight header from taking the width back. */
  min-width: 42px;
  flex-shrink: 0;
  text-align: center;
  white-space: nowrap;
}

.theme-toggle--compact {
  min-width: 44px;
  width: 44px;
  height: 44px;
  padding: 0;
}

.theme-toggle--compact .theme-toggle__label {
  position: absolute;
  width: 1px;
  height: 1px;
  padding: 0;
  margin: -1px;
  overflow: hidden;
  clip: rect(0, 0, 0, 0);
  white-space: nowrap;
  border: 0;
}

.theme-toggle--light {
  background: var(--surface-elevated);
  border-color: rgba(148, 163, 184, 0.4);
  color: var(--accent-strong);
  box-shadow: 0 8px 20px rgba(15, 23, 42, 0.08);
}

.theme-toggle--light:hover {
  background: var(--surface-muted);
  /* `rgba(53, 158, 255, 0.45)` measured **1.54:1** against the `--surface-muted` it sits on — a hover
     border almost nobody could see, and the same `#359eff` that `focusIndicator.spec.ts` records as a
     failed focus ring elsewhere. `--accent-border` is the token for a 3:1 edge and measures 3.15:1. */
  border-color: var(--accent-border);
  box-shadow: 0 12px 24px rgba(15, 23, 42, 0.12);
}

.theme-toggle--dark {
  background: rgba(15, 23, 42, 0.78);
  border-color: rgba(148, 163, 184, 0.28);
  color: #ffffff;
  box-shadow: 0 8px 20px rgba(2, 6, 23, 0.2);
}

.theme-toggle--dark:hover {
  background: rgba(30, 41, 59, 0.9);
  border-color: rgba(148, 163, 184, 0.45);
}

.theme-toggle--glass {
  background: rgba(255, 255, 255, 0.08);
  border-color: rgba(255, 255, 255, 0.24);
  color: #ffffff;
  box-shadow: inset 0 1px 1px rgba(255, 255, 255, 0.12);
  backdrop-filter: blur(8px);
  -webkit-backdrop-filter: blur(8px);
}

.theme-toggle--glass:hover {
  background: rgba(255, 255, 255, 0.14);
  border-color: rgba(255, 255, 255, 0.36);
}
</style>

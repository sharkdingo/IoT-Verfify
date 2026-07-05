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
const { theme, toggleTheme } = useTheme()

const nextThemeLabel = computed(() => theme.value === 'dark' ? t('app.lightTheme') : t('app.darkTheme'))
const iconName = computed(() => theme.value === 'dark' ? 'light_mode' : 'dark_mode')
</script>

<template>
  <button
    type="button"
    class="theme-toggle"
    :class="[
      `theme-toggle--${tone}`,
      { 'theme-toggle--compact': compact }
    ]"
    :title="t('app.switchTheme')"
    :aria-label="t('app.switchTheme')"
    @click="toggleTheme"
  >
    <span class="material-symbols-outlined theme-toggle__icon">{{ iconName }}</span>
    <span class="theme-toggle__label">{{ nextThemeLabel }}</span>
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
  border-radius: 999px;
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
  outline: 3px solid rgba(53, 158, 255, 0.32);
  outline-offset: 2px;
}

.theme-toggle__icon {
  font-size: 18px;
  line-height: 1;
}

.theme-toggle__label {
  min-width: 42px;
  text-align: center;
  white-space: nowrap;
}

.theme-toggle--compact {
  min-width: 40px;
  width: 40px;
  height: 34px;
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
  background: #ffffff;
  border-color: rgba(148, 163, 184, 0.4);
  color: #1d4ed8;
  box-shadow: 0 8px 20px rgba(15, 23, 42, 0.08);
}

.theme-toggle--light:hover {
  background: #f8fafc;
  border-color: rgba(53, 158, 255, 0.45);
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

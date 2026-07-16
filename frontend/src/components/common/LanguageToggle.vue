<script setup lang="ts">
import { computed } from 'vue'
import { useI18n } from 'vue-i18n'

type Tone = 'light' | 'dark' | 'glass'

withDefaults(defineProps<{
  tone?: Tone
  compact?: boolean
}>(), {
  tone: 'light',
  compact: false
})

const { t, locale } = useI18n()

const targetLocaleLabel = computed(() => locale.value === 'zh-CN' ? 'EN' : '中')

const toggleLocale = () => {
  const nextLocale = locale.value === 'zh-CN' ? 'en' : 'zh-CN'
  locale.value = nextLocale
  localStorage.setItem('locale', nextLocale)
}
</script>

<template>
  <button
    type="button"
    class="language-toggle"
    :class="[
      `language-toggle--${tone}`,
      { 'language-toggle--compact': compact }
    ]"
    :title="t('app.switchLanguage')"
    :aria-label="t('app.switchLanguage')"
    @click="toggleLocale"
  >
    <span class="material-symbols-outlined language-toggle__icon">language</span>
    <span class="language-toggle__label">{{ targetLocaleLabel }}</span>
  </button>
</template>

<style scoped>
.language-toggle {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  gap: 6px;
  min-width: 72px;
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

.language-toggle:hover {
  transform: translateY(-1px);
}

.language-toggle:active {
  transform: translateY(0);
}

.language-toggle:focus-visible {
  outline: 3px solid rgba(53, 158, 255, 0.32);
  outline-offset: 2px;
}

.language-toggle__icon {
  font-size: 18px;
  line-height: 1;
}

.language-toggle__label {
  min-width: 20px;
  text-align: center;
}

.language-toggle--compact {
  min-width: 56px;
  height: 44px;
  padding: 0 8px;
}

.language-toggle--light {
  background: #ffffff;
  border-color: rgba(148, 163, 184, 0.4);
  color: #1d4ed8;
  box-shadow: 0 8px 20px rgba(15, 23, 42, 0.08);
}

.language-toggle--light:hover {
  background: #f8fafc;
  border-color: rgba(53, 158, 255, 0.45);
  box-shadow: 0 12px 24px rgba(15, 23, 42, 0.12);
}

.language-toggle--dark {
  background: rgba(15, 23, 42, 0.78);
  border-color: rgba(148, 163, 184, 0.28);
  color: #ffffff;
  box-shadow: 0 8px 20px rgba(2, 6, 23, 0.2);
}

.language-toggle--dark:hover {
  background: rgba(30, 41, 59, 0.9);
  border-color: rgba(148, 163, 184, 0.45);
}

.language-toggle--glass {
  background: rgba(255, 255, 255, 0.08);
  border-color: rgba(255, 255, 255, 0.24);
  color: #ffffff;
  box-shadow: inset 0 1px 1px rgba(255, 255, 255, 0.12);
  backdrop-filter: blur(8px);
  -webkit-backdrop-filter: blur(8px);
}

.language-toggle--glass:hover {
  background: rgba(255, 255, 255, 0.14);
  border-color: rgba(255, 255, 255, 0.36);
}
</style>

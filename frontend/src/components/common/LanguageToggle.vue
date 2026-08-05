<script setup lang="ts">
import { computed } from 'vue'
import { useI18n } from 'vue-i18n'
import { setLocale } from '@/assets/i18n'

type Tone = 'light' | 'dark' | 'glass'

withDefaults(defineProps<{
  tone?: Tone
  compact?: boolean
}>(), {
  tone: 'light',
  compact: false
})

const { t, locale } = useI18n()

/**
 * Both languages, with the current one marked — so the label cannot be misread.
 *
 * It used to show only the target ("EN" while the interface was Chinese). Two reviews of the 404 page,
 * looking at nothing but the screen, read that as a claim about the *current* language and reported it
 * as a localization bug: English label, Chinese body text. That is a fair reading — a lone "EN" is
 * genuinely ambiguous between "you are here" and "go here", and a tooltip does not help someone
 * scanning.
 *
 * Showing `中 · EN` with the active side emphasised states the choice and the current position at once,
 * which is the convention a language switch can be read correctly at a glance.
 *
 * The button carries `lang` matching its accessible name, which is deliberately written in the language
 * it leads to ("Switch to English" while the interface is Chinese). Without that attribute a screen
 * reader would announce those words using the surrounding document's language rules — English read as
 * if it were Chinese, or the reverse — which is the one control where that is guaranteed to happen.
 */
const isChinese = computed(() => locale.value === 'zh-CN')

/**
 * Name the destination, not just the act.
 *
 * The visible label is the *target* locale by design — "EN" while the interface is Chinese — but two
 * letters cannot say whether they mean "you are here" or "go here". A review of the 404 page read the
 * "EN" beside Chinese body text as a contradiction and reported it as a real localization defect, which
 * is a fair reading of the label alone. The accessible name was "Switch language", which says it is an
 * action but not to what, so neither a sighted nor a screen-reader user learned the destination.
 */
const switchTargetDescription = computed(() =>
  locale.value === 'zh-CN' ? t('app.switchToEnglish') : t('app.switchToChinese'))

/**
 * Delegates to `setLocale`, which owns all three steps: apply, persist, and re-declare the document's
 * language. This component used to do the first two inline and the third did not exist anywhere, so
 * `<html lang>` stayed at its hardcoded `en` no matter what the user chose.
 */
const toggleLocale = () => {
  setLocale(locale.value === 'zh-CN' ? 'en' : 'zh-CN')
}
</script>

<template>
  <HintTooltip :content="switchTargetDescription">
    <button
      type="button"
      class="language-toggle"
      :class="[
        `language-toggle--${tone}`,
        { 'language-toggle--compact': compact }
      ]"
      :aria-label="switchTargetDescription"
      :lang="isChinese ? 'en' : 'zh-CN'"
      @click="toggleLocale"
    >
      <span class="material-symbols-outlined language-toggle__icon" aria-hidden="true">language</span>
      <!-- aria-hidden: `aria-label` already states the destination in a full sentence, so reading the
           pair out again would only add noise. -->
      <span class="language-toggle__label" aria-hidden="true">
        <span :class="['language-toggle__side', { 'language-toggle__side--active': isChinese }]">中</span>
        <span class="language-toggle__divider">·</span>
        <span :class="['language-toggle__side', { 'language-toggle__side--active': !isChinese }]">EN</span>
      </span>
    </button>
  </HintTooltip>
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

.language-toggle:hover {
  transform: translateY(-1px);
}

.language-toggle:active {
  transform: translateY(0);
}

.language-toggle:focus-visible {
  outline: 3px solid var(--accent-border);
  outline-offset: 2px;
}

.language-toggle__icon {
  font-size: 18px;
  line-height: 1;
}

.language-toggle__label {
  display: inline-flex;
  align-items: baseline;
  gap: 3px;
  /* Both sides are always rendered, so the width no longer changes with the locale and the control
     cannot shift the header when it is used. */
  flex-shrink: 0;
  text-align: center;
  white-space: nowrap;
}

/* The inactive side stays legible rather than being dimmed into decoration — it is the affordance, and
   it must read as a choice you can take. Weight and opacity together carry the distinction, so it does
   not depend on colour alone.
 *
 * `0.55` was my own first value and it failed. Measured on the board in light theme, the inactive side came to
 * **2.62 contrast** — well under AA — while the same opacity gave 6.07 in dark. One alpha cannot serve both
 * grounds when one is dark-on-light and the other light-on-dark, and I had verified only the theme where it
 * happened to work.
 *
 * Raising the alpha was not enough either: `0.72` reached only 3.73 in light, because the button's own colour is
 * already muted on that ground — the *active* side measures just 6.7 there, so opacity was dividing a small
 * budget. Alpha is the wrong instrument for a legibility floor.
 *
 * The inactive side now takes `--text-muted`, which was measured earlier in this audit against white and all five
 * role surfaces (4.55-4.98) and darkened specifically so it clears AA on every one. The active/inactive
 * distinction rests on colour plus the weight step, and neither depends on a translucency that behaves
 * differently per theme. */
.language-toggle__side {
  color: var(--text-muted);
  font-weight: 600;
}

.language-toggle__side--active {
  /* `inherit` keeps the active side on the button's own colour, which each `--tone` variant sets — so the
     active/inactive pair stays correct on the glass header, the board nav and the dark variant alike. */
  color: inherit;
  font-weight: 800;
}

/* Also raised: at 0.4 the separator was fainter than the text it separates, which made `中 · EN` read as two
   loose glyphs rather than one control with two sides. */
.language-toggle__divider {
  opacity: 0.55;
}

.language-toggle--compact {
  min-width: 56px;
  height: 44px;
  padding: 0 8px;
}

.language-toggle--light {
  background: var(--surface-elevated);
  border-color: rgba(148, 163, 184, 0.4);
  color: var(--accent-strong);
  box-shadow: 0 8px 20px rgba(15, 23, 42, 0.08);
}

.language-toggle--light:hover {
  background: var(--surface-muted);
  /* 1.54:1 as `rgba(53, 158, 255, 0.45)`; `--accent-border` is 3.15:1. Same fix as `ThemeToggle`, which
     sits beside this control in the public header and had the identical value. */
  border-color: var(--accent-border);
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

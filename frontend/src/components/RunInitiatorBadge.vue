<script setup lang="ts">
import { useI18n } from 'vue-i18n'
import type { RunInitiator } from '@/types/model'

defineProps<{
  initiator: RunInitiator
}>()

const { t } = useI18n()
</script>

<template>
  <span
    v-if="initiator !== 'USER'"
    class="inline-flex max-w-full items-center gap-1 rounded-full border px-2 py-0.5 text-[length:var(--iot-font-min)] font-semibold"
    :class="initiator === 'AI_ASSISTANT'
      ? 'board-surface-accent'
      : 'border-slate-200 bg-slate-50 text-slate-600 dark:border-slate-600 dark:bg-slate-800 dark:text-slate-300'"
    :data-testid="`run-initiator-${initiator.toLowerCase()}`"
  >
    <span class="material-symbols-outlined text-[13px]" aria-hidden="true">
      {{ initiator === 'AI_ASSISTANT' ? 'smart_toy' : 'help' }}
    </span>
    <span class="truncate">
      {{ initiator === 'AI_ASSISTANT' ? t('app.runInitiatedByAssistant') : t('app.runInitiatorUnknown') }}
    </span>
  </span>
</template>

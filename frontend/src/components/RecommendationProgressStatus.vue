<script setup lang="ts">
import { computed } from 'vue'
import { useI18n } from 'vue-i18n'

const props = defineProps<{
  kind: 'rule' | 'device' | 'spec' | 'scenario'
  elapsedSeconds: number
  templateCount: number
  deviceCount: number
  ruleCount: number
  specCount: number
}>()

const { t } = useI18n()

const toolLabel = computed(() => t(`app.recommendationProgressTool_${props.kind}`))
const phaseLabel = computed(() => {
  if (props.elapsedSeconds < 3) return t('app.recommendationProgressSubmitting')
  if (props.elapsedSeconds < 30) return t('app.recommendationProgressAnalyzing')
  return t('app.recommendationProgressStillWorking')
})
</script>

<template>
  <div class="recommendation-progress" role="status" aria-live="polite">
    <div class="recommendation-progress__heading">
      <span class="material-symbols-outlined recommendation-progress__spinner" aria-hidden="true">progress_activity</span>
      <strong>{{ t('app.recommendationProgressTitle') }}</strong>
      <span>{{ t('app.recommendationProgressElapsed', { seconds: elapsedSeconds }) }}</span>
    </div>
    <p>
      {{ t('app.recommendationProgressContext', {
        templates: templateCount,
        devices: deviceCount,
        rules: ruleCount,
        specs: specCount
      }) }}
    </p>
    <p>{{ t('app.recommendationProgressTool', { tool: toolLabel }) }}</p>
    <p class="recommendation-progress__phase">{{ phaseLabel }}</p>
  </div>
</template>

<style scoped>
.recommendation-progress {
  border-left: 3px solid #0f766e;
  background: color-mix(in srgb, #0f766e 7%, white);
  padding: 0.65rem 0.75rem;
  color: #475569;
  font-size: 0.75rem;
  line-height: 1.45;
}

.recommendation-progress__heading {
  display: flex;
  align-items: center;
  gap: 0.4rem;
  color: #0f172a;
}

.recommendation-progress__heading span:last-child {
  margin-left: auto;
  color: #64748b;
  font-variant-numeric: tabular-nums;
}

.recommendation-progress p {
  margin: 0.25rem 0 0;
}

.recommendation-progress__phase {
  color: #0f766e;
  font-weight: 650;
}

.recommendation-progress__spinner {
  font-size: 1rem;
  animation: recommendation-progress-spin 1.1s linear infinite;
}

@keyframes recommendation-progress-spin {
  to { transform: rotate(360deg); }
}
</style>

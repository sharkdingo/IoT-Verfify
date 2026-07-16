// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { describe, expect, it } from 'vitest'
import RecommendationProgressStatus from '../RecommendationProgressStatus.vue'

const i18n = createI18n({
  legacy: false,
  locale: 'en',
  messages: {
    en: {
      app: {
        recommendationProgressTool_rule: 'rule recommendation tool',
        recommendationProgressTitle: 'AI recommendation in progress',
        recommendationProgressElapsed: '{seconds}s elapsed',
        recommendationProgressContext: '{templates}/{devices}/{rules}/{specs}',
        recommendationProgressTool: 'Calling: {tool}',
        recommendationProgressSubmitting: 'Submitting the request',
        recommendationProgressAnalyzing: 'Waiting for the model service; private reasoning is not observable.',
        recommendationProgressStillWorking: 'Still processing; you can stop at any time.'
      }
    }
  }
})

const mountStatus = (elapsedSeconds: number) => mount(RecommendationProgressStatus, {
  props: {
    kind: 'rule',
    elapsedSeconds,
    templateCount: 45,
    deviceCount: 2,
    ruleCount: 1,
    specCount: 1
  },
  global: { plugins: [i18n] }
})

describe('RecommendationProgressStatus', () => {
  it('does not infer unobservable model phases from elapsed time', () => {
    expect(mountStatus(12).text()).toContain('Waiting for the model service')
  })

  it('offers an accurate long-wait recovery cue', () => {
    expect(mountStatus(31).text()).toContain('you can stop at any time')
  })
})

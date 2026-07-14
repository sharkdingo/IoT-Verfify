import { defineComponent } from 'vue'
import { mount } from '@vue/test-utils'
import { describe, expect, it } from 'vitest'

import InfoTooltip from '@/components/common/InfoTooltip.vue'

const ElTooltipStub = defineComponent({
  name: 'ElTooltip',
  props: {
    content: String,
    placement: String,
    trigger: [String, Array],
    popperClass: String
  },
  template: '<div data-testid="tooltip-host"><slot /></div>'
})

describe('InfoTooltip', () => {
  it('keeps long help behind an accessible icon trigger', () => {
    const wrapper = mount(InfoTooltip, {
      props: {
        text: 'Detailed model semantics',
        label: 'Show model semantics help',
        tone: 'danger',
        testId: 'model-help'
      },
      global: {
        stubs: { ElTooltip: ElTooltipStub }
      }
    })

    const trigger = wrapper.get('[data-testid="model-help"]')
    expect(trigger.attributes('aria-label')).toBe('Show model semantics help')
    expect(wrapper.getComponent(ElTooltipStub).props('content')).toBe('Detailed model semantics')
    expect(wrapper.text()).not.toContain('Detailed model semantics')
  })
})

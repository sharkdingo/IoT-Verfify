// @vitest-environment jsdom
import { flushPromises, mount } from '@vue/test-utils'
import { describe, expect, it, vi } from 'vitest'

import { i18n } from '@/assets/i18n'
import ControlCenter from '../ControlCenter.vue'

// `HintTooltip` imports `ElTooltip`; a whole-module mock without it fails at import time with a
// message naming the mock rather than the component that needs it.
vi.mock('element-plus', () => ({
  ElMessage: { success: vi.fn(), warning: vi.fn(), error: vi.fn() },
  ElTooltip: { name: 'ElTooltip', template: '<slot />' }
}))

/**
 * The device-import preview is debounced by 300ms to avoid re-parsing on every keystroke. That is a
 * property of typing, and applying it to a *file selection* opened a window in which the preview, the
 * validity count and the create button all still described the previously loaded content — while the
 * button was already enabled from it. Choosing a second file and clicking Create inside that window
 * imported the first file's devices again.
 *
 * Caught in E2E as two unexpected `import_phone_1`/`import_alarm_1` devices where a CSV's own devices
 * were expected, which is an expensive way to learn it; this pins the behaviour where it is cheap.
 */
describe('ControlCenter device import freshness', () => {
  /**
   * `findTemplateByName` resolves an imported row's template against the `deviceTemplates` prop, and
   * `validImportedDevices` drops any row whose template does not resolve — so without these the create
   * button stays disabled for a reason unrelated to the staleness under test.
   */
  const deviceTemplates = [
    { name: 'Mobile Phone', manifest: { Name: 'Mobile Phone' } },
    { name: 'Alarm', manifest: { Name: 'Alarm' } }
  ]

  const mountImportPanel = () => mount(ControlCenter, {
    attachTo: document.body,
    props: { activeSection: 'devices', deviceTemplates },
    global: { plugins: [i18n] }
  })

  // No `state`: these fixture templates declare no state machine, and the importer rejects an explicit
  // initial state for such a template. The staleness under test is independent of that validation.
  const jsonPayload = JSON.stringify([
    { templateName: 'Mobile Phone', label: 'first_phone' }
  ])
  // `template,name` is the header the importer accepts, per `e2e/board-full-flow.spec.ts:1072`.
  const csvPayload = 'template,name\nAlarm,second_alarm\n'

  /** The import panel is behind a create-mode selector, not just the devices section. */
  const openImportMode = async (wrapper: ReturnType<typeof mountImportPanel>) => {
    await wrapper.get('[data-testid="device-create-mode-import"]').trigger('click')
    await wrapper.vm.$nextTick()
  }

  /**
   * A `change` on the hidden file input, with a File whose `text()` resolves to `content`.
   *
   * jsdom does not implement `Blob.prototype.text` (verified: `typeof new File([...]).text` is
   * `undefined` here), so it is supplied rather than stubbed around — the handler awaits it, and in a
   * real browser it exists. Without this the read throws, the catch shows an error toast, and the
   * assertions below would fail for a reason unrelated to the debounce they are testing.
   */
  const selectFile = async (wrapper: ReturnType<typeof mountImportPanel>, name: string, content: string) => {
    const input = wrapper.get('[data-testid="device-import-file"]').element as HTMLInputElement
    const file = new File([content], name, { type: 'text/plain' })
    Object.defineProperty(file, 'text', { value: () => Promise.resolve(content), configurable: true })
    Object.defineProperty(input, 'files', { value: [file], configurable: true })
    await wrapper.get('[data-testid="device-import-file"]').trigger('change')
    await flushPromises()
    await wrapper.vm.$nextTick()
  }

  it('reflects a newly chosen file without waiting out the keystroke debounce', async () => {
    vi.useFakeTimers()
    try {
      const wrapper = mountImportPanel()
      await openImportMode(wrapper)

      await selectFile(wrapper, 'devices.json', jsonPayload)
      // No timer advance: the parsed preview must already describe THIS file. Advancing here would
      // make the assertion pass whether or not the debounce was flushed.
      expect(wrapper.text()).toContain('first_phone')

      await selectFile(wrapper, 'devices.csv', csvPayload)
      expect(wrapper.text(), 'the second file must replace the first immediately')
        .toContain('second_alarm')
      expect(wrapper.text(), 'the first file must not still be offered for creation')
        .not.toContain('first_phone')

      wrapper.unmount()
    } finally {
      vi.useRealTimers()
    }
  })

  /**
   * The file path was fixed first, by flushing the debounce for that one entry point. That left the
   * same window open on the *paste* path, which E2E then caught one assertion further along: typing or
   * pasting a payload and clicking Create within 300ms still created whatever the previous text parsed
   * to, because the button was gated on the count alone.
   *
   * So the invariant lives on the gate: enabled must mean "ready for what is in the box right now".
   */
  it('keeps create disabled while the preview still describes replaced text', async () => {
    vi.useFakeTimers()
    try {
      const wrapper = mountImportPanel()
      await openImportMode(wrapper)

      const textarea = wrapper.get('[data-testid="device-import-text"]')
      await textarea.setValue(jsonPayload)
      await vi.advanceTimersByTimeAsync(400)
      await wrapper.vm.$nextTick()
      expect(
        wrapper.get('[data-testid="device-import-create"]').attributes('disabled'),
        'a settled payload must be creatable'
      ).toBeUndefined()

      // Replace the text and do NOT let the debounce settle: the preview still describes the old
      // payload, so creating now would import the wrong devices.
      await textarea.setValue('template,name\nAlarm,pasted_alarm\n')
      await wrapper.vm.$nextTick()
      expect(
        wrapper.get('[data-testid="device-import-create"]').attributes('disabled'),
        'create must be disabled while the preview is stale'
      ).toBeDefined()

      await vi.advanceTimersByTimeAsync(400)
      await wrapper.vm.$nextTick()
      expect(
        wrapper.get('[data-testid="device-import-create"]').attributes('disabled'),
        'and enabled again once the preview catches up'
      ).toBeUndefined()
      expect(wrapper.text()).toContain('pasted_alarm')

      wrapper.unmount()
    } finally {
      vi.useRealTimers()
    }
  })
})

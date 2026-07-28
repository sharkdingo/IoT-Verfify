// @vitest-environment jsdom
import { flushPromises, mount } from '@vue/test-utils'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

import { i18n } from '@/assets/i18n'
import ControlCenter from '../ControlCenter.vue'

const boardApiMocks = vi.hoisted(() => ({
  addDeviceTemplate: vi.fn(),
  deleteDeviceTemplate: vi.fn(),
  getDeviceTemplates: vi.fn(),
  getEnvironment: vi.fn(),
  previewDefaultTemplateReset: vi.fn(),
  previewDeviceTemplateDeletion: vi.fn(),
  resetDefaultTemplates: vi.fn()
}))

// Assert on the semantic feedback boundary, not on Element Plus option objects.
const messageMocks = vi.hoisted(() => ({
  success: vi.fn(),
  // `notifyBlocked` and `notifyInfo` are distinct boundaries: sharing one spy would let a
  // blocked-action warning silently downgrade to an informational toast and still pass.
  warning: vi.fn(),
  info: vi.fn(),
  error: vi.fn()
}))

vi.mock('@/api/board', async () => {
  const actual = await vi.importActual<typeof import('@/api/board')>('@/api/board')
  return {
    ...actual,
    default: { ...actual.default, ...boardApiMocks }
  }
})

vi.mock('@/utils/feedback', () => ({
  notifySuccess: messageMocks.success,
  notifyBlocked: messageMocks.warning,
  notifyInfo: messageMocks.info,
  notifyError: messageMocks.error
}))

const manifest = {
  Name: 'CustomSwitch',
  Description: 'Custom switch template',
  InitState: 'off',
  Modes: ['SwitchState'],
  WorkingStates: [{ Name: 'off', Trust: 'trusted', Privacy: 'public' }],
  InternalVariables: [],
  APIs: [],
  Transitions: []
}

const template = {
  id: 9,
  name: 'CustomSwitch',
  defaultTemplate: false,
  manifest
}

const resetPreview = {
  operation: 'preview' as const,
  impactToken: 'reset-impact-token',
  canApply: true,
  templateChanges: [],
  affectedDevices: [],
  blockers: [],
  environmentChanges: [],
  currentTemplates: [template],
  environmentVariables: []
}

const deletionPreview = {
  operation: 'preview' as const,
  impactToken: 'delete-impact-token',
  canDelete: true,
  template,
  blockers: [],
  currentTemplates: [template]
}

const deletionConflict = (reasonCode: string, currentPreview: unknown) => ({
  response: {
    status: 409,
    data: { data: { reasonCode, currentPreview } }
  }
})

const mountTemplates = () => mount(ControlCenter, {
  attachTo: document.body,
  props: { activeSection: 'templates', deviceTemplates: [template] },
  global: { plugins: [i18n] }
})

beforeEach(() => {
  vi.resetAllMocks()
  i18n.global.locale.value = 'en'
})

afterEach(() => {
  document.body.innerHTML = ''
})

describe('ControlCenter template authority recovery', () => {
  it('marks the template catalog unavailable when import outcome and refresh are both unknown', async () => {
    boardApiMocks.addDeviceTemplate.mockRejectedValue(new Error('response lost'))
    boardApiMocks.getDeviceTemplates.mockRejectedValue(new Error('refresh failed'))
    const wrapper = mountTemplates()
    const input = wrapper.get<HTMLInputElement>('input[type="file"]')
    Object.defineProperty(input.element, 'files', {
      configurable: true,
      value: [{ size: 128, text: async () => JSON.stringify(manifest) }]
    })

    await input.trigger('change')
    await flushPromises()

    expect(wrapper.emitted('authoritative-state-unavailable')).toEqual([[['templates']]])
    wrapper.unmount()
  })

  it('marks templates and environment unavailable when reset reconciliation fails', async () => {
    boardApiMocks.previewDefaultTemplateReset.mockResolvedValue(resetPreview)
    boardApiMocks.resetDefaultTemplates.mockRejectedValue(new Error('response lost'))
    boardApiMocks.getDeviceTemplates.mockRejectedValue(new Error('template refresh failed'))
    boardApiMocks.getEnvironment.mockRejectedValue(new Error('environment refresh failed'))
    const wrapper = mountTemplates()

    await wrapper.get('[data-testid="reset-default-templates"]').trigger('click')
    await flushPromises()
    await wrapper.get('.template-reset-dialog__btn.primary').trigger('click')
    await flushPromises()

    expect(wrapper.emitted('authoritative-state-unavailable'))
      .toEqual([[['templates', 'environment']]])
    wrapper.unmount()
  })

  it('marks the template catalog unavailable when deletion outcome and refresh are both unknown', async () => {
    boardApiMocks.previewDeviceTemplateDeletion.mockResolvedValue(deletionPreview)
    boardApiMocks.deleteDeviceTemplate.mockRejectedValue(new Error('response lost'))
    boardApiMocks.getDeviceTemplates.mockRejectedValue(new Error('refresh failed'))
    const wrapper = mountTemplates()

    await wrapper.get('.template-card__action--danger').trigger('click')
    await flushPromises()
    await wrapper.get('.control-center-delete-dialog button:last-child').trigger('click')
    await flushPromises()

    expect(wrapper.emitted('authoritative-state-unavailable')).toEqual([[['templates']]])
    wrapper.unmount()
  })

  it('adopts a validated blocked deletion preview returned by a known conflict', async () => {
    const blockedPreview = {
      ...deletionPreview,
      impactToken: 'current-delete-impact-token',
      canDelete: false,
      blockers: [{
        reasonCode: 'DEVICE_INSTANCE_USES_TEMPLATE',
        itemId: 'hall_switch',
        itemLabel: 'Hall switch',
        reason: 'The device still uses this type.'
      }]
    }
    boardApiMocks.previewDeviceTemplateDeletion.mockResolvedValue(deletionPreview)
    boardApiMocks.deleteDeviceTemplate.mockRejectedValue(deletionConflict(
      'TEMPLATE_DELETION_BLOCKED',
      blockedPreview
    ))
    const wrapper = mountTemplates()

    await wrapper.get('.template-card__action--danger').trigger('click')
    await flushPromises()
    await wrapper.get('.control-center-delete-dialog button:last-child').trigger('click')
    await flushPromises()

    expect(wrapper.get('.control-center-delete-dialog').text()).toContain('Hall switch')
    expect(wrapper.get('.control-center-delete-dialog button:last-child').attributes('disabled')).toBeDefined()
    expect(boardApiMocks.getDeviceTemplates).not.toHaveBeenCalled()
    expect(messageMocks.warning)
      .toHaveBeenCalledWith(i18n.global.t('app.templateDeletePreviewChanged'))
    wrapper.unmount()
  })

  it('rejects a malformed conflict preview, refreshes authority, and closes the stale confirmation', async () => {
    boardApiMocks.previewDeviceTemplateDeletion.mockResolvedValue(deletionPreview)
    boardApiMocks.deleteDeviceTemplate.mockRejectedValue(deletionConflict(
      'TEMPLATE_DELETION_PREVIEW_STALE',
      { ...deletionPreview, operation: 'deleted', currentTemplates: [] }
    ))
    boardApiMocks.getDeviceTemplates.mockResolvedValue([template])
    const wrapper = mountTemplates()

    await wrapper.get('.template-card__action--danger').trigger('click')
    await flushPromises()
    await wrapper.get('.control-center-delete-dialog button:last-child').trigger('click')
    await flushPromises()

    expect(boardApiMocks.getDeviceTemplates).toHaveBeenCalledTimes(1)
    expect(wrapper.emitted('replace-template-catalog')).toEqual([[[template]]])
    expect(wrapper.find('.control-center-delete-dialog').exists()).toBe(false)
    expect(messageMocks.warning)
      .not.toHaveBeenCalledWith(i18n.global.t('app.templateDeletePreviewChanged'))
    expect(messageMocks.error).toHaveBeenCalledWith(
      i18n.global.t('app.deleteFailedWithReason', {
        reason: i18n.global.t('app.boardMutationResponseIncomplete')
      })
    )
    wrapper.unmount()
  })

  it('does not trust a deletion preview attached to an unknown 409 reason', async () => {
    boardApiMocks.previewDeviceTemplateDeletion.mockResolvedValue(deletionPreview)
    boardApiMocks.deleteDeviceTemplate.mockRejectedValue(deletionConflict(
      'UNRELATED_CONFLICT',
      deletionPreview
    ))
    boardApiMocks.getDeviceTemplates.mockResolvedValue([template])
    const wrapper = mountTemplates()

    await wrapper.get('.template-card__action--danger').trigger('click')
    await flushPromises()
    await wrapper.get('.control-center-delete-dialog button:last-child').trigger('click')
    await flushPromises()

    expect(boardApiMocks.getDeviceTemplates).toHaveBeenCalledTimes(1)
    expect(wrapper.find('.control-center-delete-dialog').exists()).toBe(false)
    expect(messageMocks.warning)
      .not.toHaveBeenCalledWith(i18n.global.t('app.templateDeletePreviewChanged'))
    wrapper.unmount()
  })

  it('refreshes authority when a template-deletion 409 omits its conflict data', async () => {
    boardApiMocks.previewDeviceTemplateDeletion.mockResolvedValue(deletionPreview)
    boardApiMocks.deleteDeviceTemplate.mockRejectedValue({
      response: { status: 409, data: { data: null } }
    })
    boardApiMocks.getDeviceTemplates.mockResolvedValue([template])
    const wrapper = mountTemplates()

    await wrapper.get('.template-card__action--danger').trigger('click')
    await flushPromises()
    await wrapper.get('.control-center-delete-dialog button:last-child').trigger('click')
    await flushPromises()

    expect(boardApiMocks.getDeviceTemplates).toHaveBeenCalledTimes(1)
    expect(wrapper.find('.control-center-delete-dialog').exists()).toBe(false)
    // Assert *which* error, so a wrong or generic message cannot pass.
    expect(messageMocks.error).toHaveBeenCalledWith(
      i18n.global.t('app.deleteFailedWithReason', {
        reason: i18n.global.t('app.boardMutationResponseIncomplete')
      })
    )
    wrapper.unmount()
  })
})

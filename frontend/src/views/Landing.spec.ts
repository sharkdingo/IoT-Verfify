// @vitest-environment jsdom
import { flushPromises, mount } from '@vue/test-utils'
import { createMemoryHistory, createRouter } from 'vue-router'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'
import { i18n } from '@/assets/i18n'
import Landing from './Landing.vue'

const authApi = vi.hoisted(() => ({
  login: vi.fn(),
  register: vi.fn()
}))

vi.mock('@/api/auth', () => ({ authApi }))
vi.mock('element-plus', () => ({
  ElMessage: {
    success: vi.fn(),
    error: vi.fn()
  }
}))

const deferred = <T>() => {
  let resolve!: (value: T) => void
  const promise = new Promise<T>(done => { resolve = done })
  return { promise, resolve }
}

const mountLanding = async () => {
  const router = createRouter({
    history: createMemoryHistory(),
    routes: [
      { path: '/', component: Landing },
      { path: '/board', component: { template: '<div>board</div>' } }
    ]
  })
  await router.push('/?mode=login')
  await router.isReady()
  const wrapper = mount(Landing, {
    attachTo: document.body,
    global: {
      plugins: [router, i18n],
      stubs: { PublicHeader: true }
    }
  })
  return { router, wrapper }
}

describe('Landing authentication usability', () => {
  beforeEach(() => {
    authApi.login.mockReset()
    authApi.register.mockReset()
    i18n.global.locale.value = 'zh-CN'
  })

  afterEach(() => {
    document.body.innerHTML = ''
  })

  it('focuses the first invalid field and exposes validation messages as alerts', async () => {
    const { wrapper } = await mountLanding()

    await wrapper.get('#login-panel').trigger('submit')

    const account = wrapper.get<HTMLInputElement>('input[autocomplete="username"]')
    expect(document.activeElement).toBe(account.element)
    expect(wrapper.findAll('[role="alert"]').map(node => node.text())).toEqual([
      '请输入手机号或用户名',
      '请输入密码'
    ])
    wrapper.unmount()
  })

  it('shows action-specific busy feedback and keeps a failed request visible for recovery', async () => {
    const pending = deferred<any>()
    authApi.login.mockReturnValueOnce(pending.promise)
    const { wrapper } = await mountLanding()

    await wrapper.get('input[autocomplete="username"]').setValue('missing-user')
    await wrapper.get('input[autocomplete="current-password"]').setValue('wrong-password')
    await wrapper.get('#login-panel').trigger('submit')

    expect(wrapper.get('.auth-panel').attributes('aria-busy')).toBe('true')
    expect(wrapper.get('.auth-submit').text()).toContain('正在验证账号')

    pending.resolve({ code: 401, message: '账号或密码不正确', data: null })
    await flushPromises()

    const requestError = wrapper.get<HTMLElement>('.auth-request-error')
    expect(requestError.text()).toContain('账号或密码不正确')
    expect(document.activeElement).toBe(requestError.element)
    expect(wrapper.get('.auth-panel').attributes('aria-busy')).toBe('false')
    wrapper.unmount()
  })

  it('provides a discoverable exit from the authentication panel', async () => {
    const { router, wrapper } = await mountLanding()

    await wrapper.get('[aria-label="返回产品概览"]').trigger('click')
    await flushPromises()

    expect(router.currentRoute.value.query).toEqual({})
    expect(wrapper.get('.hero-cta').isVisible()).toBe(true)
    wrapper.unmount()
  })
})

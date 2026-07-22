// @vitest-environment jsdom
import { afterEach, describe, expect, it, vi } from 'vitest'

import api, { isBoardMutationRequest } from './http'
import { router } from '@/router'
import { useAuth } from '@/stores/auth'

const validToken = (signature: string) => {
  const payload = btoa(JSON.stringify({ exp: Math.floor(Date.now() / 1000) + 3600 }))
    .replace(/=/g, '').replace(/\+/g, '-').replace(/\//g, '_')
  return `header.${payload}.${signature}`
}

afterEach(() => {
  useAuth().logout()
  vi.restoreAllMocks()
})

describe('board mutation request classification', () => {
  it('publishes invalidations only for requests that can change board semantics', () => {
    expect(isBoardMutationRequest({ method: 'post', url: '/board/nodes' })).toBe(true)
    expect(isBoardMutationRequest({ method: 'patch', url: '/board/rules/12' })).toBe(true)
    expect(isBoardMutationRequest({ method: 'post', url: '/verify/traces/12/fix/apply' })).toBe(true)
  })

  it('does not classify read-only recommendation and validation posts as mutations', () => {
    expect(isBoardMutationRequest({ method: 'post', url: '/board/rules/recommend' })).toBe(false)
    expect(isBoardMutationRequest({ method: 'post', url: '/board/specs/recommend?requestId=req-1' })).toBe(false)
    expect(isBoardMutationRequest({ method: 'post', url: '/board/rules/check-duplicate' })).toBe(false)
    expect(isBoardMutationRequest({ method: 'get', url: '/board/nodes' })).toBe(false)
  })

  it('keeps Bob logged in when Alice request receives a delayed 401', async () => {
    const auth = useAuth()
    const aliceToken = validToken('alice')
    const bobToken = validToken('bob')
    auth.login(aliceToken, { userId: 7, phone: '13800138000', username: 'alice' })
    const push = vi.spyOn(router, 'push')
    let rejectRequest!: (reason: unknown) => void
    let requestConfig: any

    const delayedRequest = api.get('/delayed-auth-check', {
      adapter: config => new Promise((_resolve, reject) => {
        requestConfig = config
        rejectRequest = reject
      })
    })
    await vi.waitFor(() => expect(requestConfig?.authTokenAtRequest).toBe(aliceToken))

    auth.login(bobToken, { userId: 8, phone: '13900139000', username: 'bob' })
    rejectRequest({
      config: requestConfig,
      response: { status: 401, config: requestConfig }
    })

    await expect(delayedRequest).rejects.toMatchObject({ response: { status: 401 } })
    expect(auth.getToken()).toBe(bobToken)
    expect(auth.getUser()?.username).toBe('bob')
    expect(push).not.toHaveBeenCalled()
  })
})

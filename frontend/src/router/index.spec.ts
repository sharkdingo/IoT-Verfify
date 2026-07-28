// @vitest-environment jsdom
import { describe, expect, it } from 'vitest'

import { resolveAuthenticatedEntry } from './index'
import { loginRedirectTarget } from './loginRedirect'

const location = (path: string, meta: { public?: boolean } = {}) =>
  ({ path, fullPath: path, meta }) as Parameters<typeof resolveAuthenticatedEntry>[0]

describe('resolveAuthenticatedEntry', () => {
  it('sends an anonymous visitor to the login surface with a return path', () => {
    expect(resolveAuthenticatedEntry(location('/board'), false))
      .toEqual({ path: '/', query: { mode: 'login', redirect: '/board' } })
  })

  it('keeps an authenticated visitor out of the landing page', () => {
    expect(resolveAuthenticatedEntry(location('/', { public: true }), true)).toBe('/board')
  })

  it('lets an authenticated visitor reach a private route', () => {
    expect(resolveAuthenticatedEntry(location('/board'), true)).toBeUndefined()
  })

  it('lets anyone reach a public route that is not the landing page', () => {
    expect(resolveAuthenticatedEntry(location('/404', { public: true }), false)).toBeUndefined()
    expect(resolveAuthenticatedEntry(location('/404', { public: true }), true)).toBeUndefined()
  })
})

describe('loginRedirectTarget', () => {
  it('returns null when already on the login surface', () => {
    expect(loginRedirectTarget({ path: '/', fullPath: '/?mode=login' })).toBeNull()
  })

  it('preserves the current location as the return path', () => {
    expect(loginRedirectTarget({ path: '/board', fullPath: '/board?panel=verify' }))
      .toEqual({ path: '/', query: { mode: 'login', redirect: '/board?panel=verify' } })
  })
})

// @vitest-environment jsdom
import { beforeEach, describe, expect, it, vi } from 'vitest'
import { useAuth } from './auth'

const tokenExpiringIn = (seconds: number, signature = 'signature') => {
  const payload = btoa(JSON.stringify({ exp: Math.floor(Date.now() / 1000) + seconds }))
    .replace(/=/g, '').replace(/\+/g, '-').replace(/\//g, '_')
  return `header.${payload}.${signature}`
}

const validToken = (signature = 'signature') => tokenExpiringIn(3600, signature)

describe('auth cross-tab synchronization', () => {
  const auth = useAuth()

  beforeEach(() => {
    auth.logout()
    localStorage.clear()
  })

  it('applies login and logout events emitted by another tab', () => {
    const token = validToken()
    const user = { userId: 7, phone: '13800138000', username: 'alice' }

    window.dispatchEvent(new StorageEvent('storage', {
      key: 'iot_verify_auth_sync',
      newValue: JSON.stringify({ token, user, updatedAt: Date.now() }),
      storageArea: localStorage
    }))

    expect(auth.state.isLoggedIn).toBe(true)
    expect(auth.state.user).toEqual(user)

    window.dispatchEvent(new StorageEvent('storage', {
      key: 'iot_verify_auth_sync',
      newValue: JSON.stringify({ token: null, user: null, updatedAt: Date.now() }),
      storageArea: localStorage
    }))

    expect(auth.state.isLoggedIn).toBe(false)
    expect(auth.state.token).toBeNull()
    expect(auth.state.user).toBeNull()
  })

  it('replaces Alice with Bob after a cross-tab logout/login sequence', () => {
    const alice = { userId: 7, phone: '13800138000', username: 'alice' }
    const bob = { userId: 8, phone: '13900139000', username: 'bob' }
    // Built once: `validToken` embeds a whole-second `exp`, so calling it again below could land in
    // the next second and produce a different string for the same logical token.
    const bobToken = validToken('bob')

    for (const next of [
      { token: validToken('alice'), user: alice },
      { token: null, user: null },
      { token: bobToken, user: bob }
    ]) {
      window.dispatchEvent(new StorageEvent('storage', {
        key: 'iot_verify_auth_sync',
        newValue: JSON.stringify({ ...next, updatedAt: Date.now() }),
        storageArea: localStorage
      }))
    }

    expect(auth.state.isLoggedIn).toBe(true)
    expect(auth.state.token).toBe(bobToken)
    expect(auth.state.user).toEqual(bob)
  })

  it('does not let an old request token log out a newer session', () => {
    const aliceToken = validToken('alice')
    const bobToken = validToken('bob')

    auth.login(aliceToken, { userId: 7, phone: '13800138000', username: 'alice' })
    auth.login(bobToken, { userId: 8, phone: '13900139000', username: 'bob' })

    expect(auth.logoutIfTokenMatches(aliceToken)).toBe(false)
    expect(auth.state.token).toBe(bobToken)
    expect(auth.state.user?.username).toBe('bob')
    expect(auth.logoutIfTokenMatches(bobToken)).toBe(true)
    expect(auth.state.isLoggedIn).toBe(false)
  })

  it('drops a session whose token expired while the tab stayed open', () => {
    // The token must lapse *in place*: delivering an already-expired token through a storage event
    // instead exercises `applyAuthState`'s own `isLocallyUsableJwt` gate, which clears the session
    // before `revalidateSession` is ever consulted — so the test passed with the production body
    // replaced by `() => state.isLoggedIn`, proving nothing about the behaviour the router guard needs.
    vi.useFakeTimers()
    try {
      auth.login(tokenExpiringIn(60), { userId: 7, phone: '13800138000', username: 'alice' })
      expect(auth.revalidateSession()).toBe(true)
      expect(auth.state.isLoggedIn).toBe(true)

      vi.advanceTimersByTime(61_000)

      expect(auth.revalidateSession()).toBe(false)
      expect(auth.state.isLoggedIn).toBe(false)
      expect(auth.state.token).toBeNull()
    } finally {
      vi.useRealTimers()
    }
  })
})

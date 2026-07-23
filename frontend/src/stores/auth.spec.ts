// @vitest-environment jsdom
import { beforeEach, describe, expect, it } from 'vitest'
import { useAuth } from './auth'

const validToken = (signature = 'signature') => {
  const payload = btoa(JSON.stringify({ exp: Math.floor(Date.now() / 1000) + 3600 }))
    .replace(/=/g, '').replace(/\+/g, '-').replace(/\//g, '_')
  return `header.${payload}.${signature}`
}

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

    for (const next of [
      { token: validToken('alice'), user: alice },
      { token: null, user: null },
      { token: validToken('bob'), user: bob }
    ]) {
      window.dispatchEvent(new StorageEvent('storage', {
        key: 'iot_verify_auth_sync',
        newValue: JSON.stringify({ ...next, updatedAt: Date.now() }),
        storageArea: localStorage
      }))
    }

    expect(auth.state.isLoggedIn).toBe(true)
    expect(auth.state.token).toBe(validToken('bob'))
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
})

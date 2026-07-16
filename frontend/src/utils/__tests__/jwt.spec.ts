import { describe, expect, it, vi } from 'vitest'
import { isLocallyUsableJwt } from '../jwt'

const tokenWithExpiry = (exp: number) => {
  const encode = (value: unknown) => btoa(JSON.stringify(value))
    .replace(/=/g, '')
    .replace(/\+/g, '-')
    .replace(/\//g, '_')
  return `${encode({ alg: 'HS256' })}.${encode({ exp })}.signature`
}

describe('isLocallyUsableJwt', () => {
  it('accepts an unexpired token and rejects expired or malformed values', () => {
    vi.useFakeTimers()
    vi.setSystemTime(new Date('2026-07-16T00:00:00Z'))
    const nowSeconds = Math.floor(Date.now() / 1000)
    expect(isLocallyUsableJwt(tokenWithExpiry(nowSeconds + 60))).toBe(true)
    expect(isLocallyUsableJwt(tokenWithExpiry(nowSeconds - 1))).toBe(false)
    expect(isLocallyUsableJwt('not-a-jwt')).toBe(false)
    expect(isLocallyUsableJwt(null)).toBe(false)
    vi.useRealTimers()
  })
})

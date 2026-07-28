// @vitest-environment jsdom
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

const THEME_KEY = 'iot_verify_theme'

let prefersDark = false
const listeners = new Set<() => void>()

const loadTheme = async () => {
  vi.resetModules()
  return import('../useTheme')
}

beforeEach(() => {
  prefersDark = false
  listeners.clear()
  localStorage.clear()
  document.documentElement.className = ''
  vi.stubGlobal('matchMedia', (query: string) => ({
    matches: query.includes('prefers-color-scheme: dark') ? prefersDark : false,
    media: query,
    addEventListener: (_: string, handler: () => void) => { listeners.add(handler) },
    removeEventListener: (_: string, handler: () => void) => { listeners.delete(handler) }
  }))
})

afterEach(() => {
  vi.unstubAllGlobals()
})

describe('useTheme', () => {
  it('follows the system when the user has never chosen a theme', async () => {
    prefersDark = true
    const { useTheme } = await loadTheme()
    const { theme, followsSystem } = useTheme()

    expect(followsSystem.value).toBe(true)
    expect(theme.value).toBe('dark')
    expect(document.documentElement.classList.contains('dark')).toBe(true)
    expect(localStorage.getItem(THEME_KEY)).toBeNull()
  })

  it('reacts to system changes only while following the system', async () => {
    const { useTheme } = await loadTheme()
    const { theme, setTheme } = useTheme()

    prefersDark = true
    listeners.forEach(handler => handler())
    expect(theme.value).toBe('dark')

    setTheme('light')
    prefersDark = false
    listeners.forEach(handler => handler())
    prefersDark = true
    listeners.forEach(handler => handler())
    expect(theme.value).toBe('light')
  })

  it('treats a stored theme as an explicit choice that survives reload', async () => {
    localStorage.setItem(THEME_KEY, 'dark')
    prefersDark = false
    const { useTheme } = await loadTheme()
    const { theme, followsSystem } = useTheme()

    expect(followsSystem.value).toBe(false)
    expect(theme.value).toBe('dark')
  })

  it('cycles light -> dark -> system and clears storage on the system step', async () => {
    localStorage.setItem(THEME_KEY, 'light')
    prefersDark = true
    const { useTheme } = await loadTheme()
    const { theme, followsSystem, cycleThemeMode } = useTheme()

    cycleThemeMode()
    expect(theme.value).toBe('dark')
    expect(localStorage.getItem(THEME_KEY)).toBe('dark')

    cycleThemeMode()
    expect(followsSystem.value).toBe(true)
    expect(theme.value).toBe('dark')
    expect(localStorage.getItem(THEME_KEY)).toBeNull()

    cycleThemeMode()
    expect(followsSystem.value).toBe(false)
    expect(theme.value).toBe('light')
    expect(localStorage.getItem(THEME_KEY)).toBe('light')
  })
})

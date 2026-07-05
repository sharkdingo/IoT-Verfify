import { computed, ref } from 'vue'

export type ThemeMode = 'light' | 'dark'

const THEME_STORAGE_KEY = 'iot_verify_theme'
const theme = ref<ThemeMode>('light')
const followsSystem = ref(false)
let initialized = false

const getSystemTheme = (): ThemeMode => {
  if (typeof window === 'undefined') return 'light'
  return window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light'
}

const readStoredTheme = (): ThemeMode | null => {
  if (typeof localStorage === 'undefined') return null
  const stored = localStorage.getItem(THEME_STORAGE_KEY)
  return stored === 'dark' || stored === 'light' ? stored : null
}

const applyTheme = (mode: ThemeMode) => {
  if (typeof document === 'undefined') return
  const root = document.documentElement
  root.dataset.theme = mode
  root.classList.toggle('dark', mode === 'dark')
  root.classList.toggle('light', mode === 'light')
  root.style.colorScheme = mode
}

const handleSystemThemeChange = () => {
  if (!followsSystem.value) return
  theme.value = getSystemTheme()
  applyTheme(theme.value)
}

export const initializeTheme = () => {
  if (initialized) return
  initialized = true

  const storedTheme = readStoredTheme()
  followsSystem.value = false
  theme.value = storedTheme ?? 'light'
  applyTheme(theme.value)

  if (typeof window !== 'undefined') {
    const mediaQuery = window.matchMedia('(prefers-color-scheme: dark)')
    mediaQuery.addEventListener?.('change', handleSystemThemeChange)
  }
}

export const useTheme = () => {
  initializeTheme()

  const setTheme = (mode: ThemeMode) => {
    followsSystem.value = false
    theme.value = mode
    localStorage.setItem(THEME_STORAGE_KEY, mode)
    applyTheme(mode)
  }

  const toggleTheme = () => {
    setTheme(theme.value === 'dark' ? 'light' : 'dark')
  }

  const resetThemeToSystem = () => {
    followsSystem.value = true
    localStorage.removeItem(THEME_STORAGE_KEY)
    theme.value = getSystemTheme()
    applyTheme(theme.value)
  }

  return {
    theme,
    followsSystem,
    isDark: computed(() => theme.value === 'dark'),
    setTheme,
    toggleTheme,
    resetThemeToSystem
  }
}

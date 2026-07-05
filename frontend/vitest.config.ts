import { configDefaults, defineConfig } from 'vitest/config'
import vue from '@vitejs/plugin-vue'

export default defineConfig({
  plugins: [vue()],
  test: {
    environment: 'jsdom',
    globals: true,
    include: [
      'src/**/*.spec.ts',
      'src/**/*.test.ts'
    ],
    exclude: [
      ...configDefaults.exclude,
      'e2e/**',
      '**/e2e/**',
      'test-results/**',
      '**/test-results/**',
      'playwright-report/**',
      '**/playwright-report/**'
    ],
    coverage: {
      provider: 'v8'
    }
  }
})



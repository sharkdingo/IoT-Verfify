import { configDefaults, defineConfig } from 'vitest/config'
import vue from '@vitejs/plugin-vue'
import { fileURLToPath } from 'node:url'

export default defineConfig({
  plugins: [vue()],
  resolve: {
    alias: {
      '@': fileURLToPath(new URL('./src', import.meta.url))
    }
  },
  test: {
    environment: 'jsdom',
    globals: true,
    /**
     * Cap the worker fan-out, because the default is a function of core count and the cost is a function of
     * memory.
     *
     * Vitest defaults to one worker per logical core. On a 28-core / 16 GB machine that is 28 concurrent jsdom
     * environments — and a jsdom environment is the dominant cost in this suite (the successful run reports
     * ~790s of `environment` against a 45s wall clock). The result was a hard crash, not a slow run:
     * `NewSpace::EnsureCurrentCapacity … heap out of memory` followed by `ERR_IPC_CHANNEL_CLOSED` as the
     * parent messaged dead workers.
     *
     * `NewSpace` / `Committing semi space failed` is V8 failing to get pages *from the OS*, not failing to fit
     * inside its own heap limit — which is why raising `--max-old-space-size` made it worse (three OOM lines
     * instead of one) and why the fix belongs here rather than in `NODE_OPTIONS`.
     *
     * Three separate agents independently hit this and each worked around it with a different ad-hoc flag, so
     * `npm run test:unit` did not work as documented for anyone who had not already learned the trick. 6 is
     * chosen to stay useful on smaller machines while bounding peak memory; the suite runs in ~45-55s either
     * way, because it was never CPU-bound.
     */
    maxWorkers: 6,
    minWorkers: 1,
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



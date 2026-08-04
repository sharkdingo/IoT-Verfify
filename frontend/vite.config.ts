import { defineConfig } from 'vite'
import vue from '@vitejs/plugin-vue'
import AutoImport from 'unplugin-auto-import/vite'
import Components from 'unplugin-vue-components/vite'
import { ElementPlusResolver } from 'unplugin-vue-components/resolvers'
import { fileURLToPath } from 'node:url'

/**
 * Where `/api` is proxied, for both the dev server and `vite preview`.
 *
 * Hardcoding `localhost:8080` here made pointing a run at a different backend *silently half-work*:
 * `E2E_API_BASE_URL` is honoured by the specs' direct API calls, but the browser still went through this
 * proxy to 8080, so the two halves of one run talked to two different servers. That matters concretely —
 * a full E2E pass needs more registrations than the default rate limit allows, and the fix is to run it
 * against a second backend started with raised caps, which is impossible while this is a constant.
 *
 * Same variable the specs read, so one setting moves the whole run.
 */
const apiProxyTarget = process.env.E2E_API_BASE_URL || 'http://localhost:8080'

// https://vite.dev/config/
export default defineConfig(({ command }) => ({
    plugins: [
        vue(),
        AutoImport({
            dts: false,
            resolvers: [ElementPlusResolver()],
        }),
        Components({
            // Production builds must not mutate the tracked development declaration file.
            dts: command === 'serve' ? 'components.d.ts' : false,
            resolvers: [ElementPlusResolver()],
        }),
    ],
    server: {
        host: '127.0.0.1',
        port: 3000,
        open: false,
        proxy: {
            '/api': {
                target: apiProxyTarget,
                changeOrigin: true,
            }
        }
    },
    // `vite preview` does not inherit `server.proxy`. E2E runs against a production build, so it
    // needs the same `/api` proxy to reach the backend.
    preview: {
        host: '127.0.0.1',
        port: 3000,
        proxy: {
            '/api': {
                target: apiProxyTarget,
                changeOrigin: true,
            }
        }
    },
    resolve: {
        alias: {
            '@': fileURLToPath(new URL('./src', import.meta.url)),
        },
    },
    base: './',
}))

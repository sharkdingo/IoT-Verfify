import { defineConfig } from 'vite'
import vue from '@vitejs/plugin-vue'
import AutoImport from 'unplugin-auto-import/vite'
import Components from 'unplugin-vue-components/vite'
import { ElementPlusResolver } from 'unplugin-vue-components/resolvers'
import { fileURLToPath } from 'node:url'

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
                target: 'http://localhost:8080',
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

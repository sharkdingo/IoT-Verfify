import { defineConfig } from 'vite'
import vue from '@vitejs/plugin-vue'

// Element UI 自动导入支持
import AutoImport from 'unplugin-auto-import/vite'
import Components from 'unplugin-vue-components/vite'
import { ElementPlusResolver } from 'unplugin-vue-components/resolvers'
import { fileURLToPath } from 'node:url'

// https://vite.dev/config/
export default defineConfig({
    plugins: [
        vue(),
        AutoImport({
            resolvers: [ElementPlusResolver()],
        }),
        Components({
            resolvers: [ElementPlusResolver()],
        }),
    ],
    server: {
        port: 3000,   // 前端端口保持不变
        open: true,
        // ⭐ 关键：把 /api 代理到 Spring Boot
        proxy: {
            '/api': {
                target: 'http://localhost:8080', // 你的后端地址
                changeOrigin: true,
                // 如果将来后端不带 /api 前缀，可以用 rewrite 做路径重写
                // rewrite: path => path.replace(/^\/api/, ''),
            },
        },
    },
    resolve: {
        alias: {
            '@': fileURLToPath(new URL('./src', import.meta.url)),
        },
    },
    base: './',
    define: {
        // enable hydration mismatch details in production build
        __VUE_PROD_HYDRATION_MISMATCH_DETAILS__: 'true',
    },
})

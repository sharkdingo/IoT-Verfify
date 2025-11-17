import { createRouter, createWebHashHistory } from 'vue-router'

const router = createRouter({
    history: createWebHashHistory(),
    routes: [
        {
            path: '/',
            redirect: '/board',
        },
        {
            path: '/board',
            name: 'board',
            component: () => import('../views/Board.vue'),
            meta: { title: 'Iot-Verify' }
        },
        {
            path: '/404',
            name: '404',
            component: () => import('../views/NotFound.vue'),
            meta: { title: '404' }
        },
        {
            path: '/:catchAll(.*)',
            redirect: '/404'
        }
    ]
})

export { router }

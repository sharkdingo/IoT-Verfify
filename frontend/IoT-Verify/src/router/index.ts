import { createRouter, createWebHashHistory } from 'vue-router'

const router = createRouter({
    history: createWebHashHistory(),
    routes: [{
        path: '/',
        redirect: '/login',
    }, {
        path: '/login',
        component: () => import('../views/user/Login.vue'),
        meta: { title: '用户登录' }
    }, {
        path: '/register',
        component: () => import('../views/user/Register.vue'),
        meta: {title: "用户注册"}
    }, {
        path: '/404',
        name: '404',
        component: () => import('../views/NotFound.vue'),
        meta: {title: '404'}
    }, {
        path: '/home',
        redirect: '/homePage',
        component: () => import('../views/Home.vue'),
        children: [
            {
                path: '/homePage',
                name: 'homePage',
                component: () => import('../views/HomePage.vue'),
                meta: {title: '首页'}
            },]
    },{
        path: '/:catchAll(.*)',
        redirect: '/404'
    }, ]
})

export {router}
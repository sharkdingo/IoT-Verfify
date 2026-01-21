import { createRouter, createWebHashHistory, RouteRecordRaw } from 'vue-router';

const TOKEN_KEY = 'iot_verify_token';

// 同步检查是否已登录（避免响应式状态时序问题）
const checkAuthSync = (): boolean => {
  const token = localStorage.getItem(TOKEN_KEY);
  return !!token;
};

const routes: RouteRecordRaw[] = [
  {
    path: '/login',
    name: 'login',
    component: () => import('../views/Login.vue'),
    meta: { title: 'Login', public: true }
  },
  {
    path: '/register',
    name: 'register',
    component: () => import('../views/Register.vue'),
    meta: { title: 'Register', public: true }
  },
  {
    path: '/',
    redirect: '/board'
  },
  {
    path: '/board',
    name: 'board',
    component: () => import('../views/Board.vue'),
    meta: { title: 'IoT-Verify' }
  },
  {
    path: '/404',
    name: '404',
    component: () => import('../views/NotFound.vue'),
    meta: { title: '404', public: true }
  },
  {
    path: '/:catchAll(.*)',
    redirect: '/404'
  }
];

const router = createRouter({
  history: createWebHashHistory(),
  routes
});

// 路由守卫 - 使用同步检查避免时序问题
router.beforeEach((to, _from, next) => {
  // 使用同步检查（直接从localStorage读取，避免响应式状态时序问题）
  const isLoggedIn = checkAuthSync();
  const isPublic = to.meta.public as boolean | undefined;
  
  // 如果是公开页面，直接放行
  if (isPublic) {
    // 如果已登录且访问登录/注册页，跳转到board
    if (isLoggedIn && ['/login', '/register'].includes(to.path)) {
      next('/board');
    } else {
      next();
    }
    return;
  }
  
  // 保护页面需要登录
  if (!isLoggedIn) {
    next({ path: '/login', query: { redirect: to.fullPath } });
  } else {
    next();
  }
});

// 路由跳转后清理 URL（移除 ?redirect= 参数）
router.afterEach((to) => {
  // 如果刚跳转到 /board 且有 redirect 参数，重定向到纯净的 /board
  if (to.path === '/board' && to.query.redirect) {
    router.replace('/board');
  }
});

export { router };
export default router;

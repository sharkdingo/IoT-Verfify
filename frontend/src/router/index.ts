import { createRouter, createWebHashHistory, RouteRecordRaw } from 'vue-router';

const TOKEN_KEY = 'iot_verify_token';

const normalizeDirectPathForHashHistory = () => {
  if (window.location.hash || window.location.pathname === '/' || window.location.pathname.endsWith('/index.html')) {
    return;
  }

  const path = window.location.pathname.replace(/\/+$/, '') || '/';
  const search = window.location.search || '';
  window.history.replaceState(null, '', `/#${path}${search}`);
};

// 同步检查是否已登录（避免响应式状态时序问题）
const checkAuthSync = (): boolean => {
  const token = localStorage.getItem(TOKEN_KEY);
  return !!token;
};

// 在应用启动时清除可能的无效token，确保从登录页面开始
const clearInvalidTokens = () => {
  // 如果当前页面不是公开页面但没有token，清除所有认证相关数据
  const currentPath = (window.location.hash.replace('#', '') || '/').split('?')[0];
  const isPublicPath = ['/', '/404'].includes(currentPath);

  if (!isPublicPath && !checkAuthSync()) {
    // 清除可能的无效认证数据
    localStorage.removeItem(TOKEN_KEY);
    localStorage.removeItem('iot_verify_user');
  }
};

normalizeDirectPathForHashHistory();

const routes: RouteRecordRaw[] = [
  {
    path: '/',
    name: 'landing',
    component: () => import('../views/Landing.vue'),
    meta: { title: 'IoT-Verify', public: true }
  },
  {
    path: '/board',
    name: 'board',
    component: () => import('../views/Board.vue'),
    meta: { title: 'IoT-Verify', usesOwnHeader: true }
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

// 应用启动时清除无效token
clearInvalidTokens();

// 路由守卫 - 使用同步检查避免时序问题
router.beforeEach((to, _from, next) => {
  // 使用同步检查（直接从localStorage读取，避免响应式状态时序问题）
  const isLoggedIn = checkAuthSync();
  const isPublic = to.meta.public as boolean | undefined;

  // 如果是公开页面，直接放行
  if (isPublic) {
    // 如果已登录且访问 landing 页，跳转到 board
    if (isLoggedIn && to.path === '/') {
      next('/board');
    } else {
      next();
    }
    return;
  }

  // 特殊处理根路径重定向
  if (to.path === '/' || to.path === '') {
    if (isLoggedIn) {
      next('/board');
    } else {
      next('/'); // 跳转到 Landing 页面
    }
    return;
  }

  // 保护页面需要登录
  if (!isLoggedIn) {
    next({ path: '/', query: { mode: 'login', redirect: to.fullPath } });
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

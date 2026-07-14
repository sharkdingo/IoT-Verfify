// src/api/http.ts - Axios配置（带Token自动携带和401处理）
import axios from 'axios';
import { useAuth } from '../stores/auth';
import { router } from '../router';

const api = axios.create({
  // Default to a relative "/api" so dev goes through the Vite proxy and prod through
  // the same-origin reverse proxy (Nginx). Set VITE_API_BASE_URL for cross-origin.
  baseURL: (import.meta.env.VITE_API_BASE_URL || '') + '/api',
  timeout: 100000,
  headers: {
    'Content-Type': 'application/json'
  }
});

// 请求拦截器 - 自动添加Token
api.interceptors.request.use(
  (config) => {
    const { getToken } = useAuth();
    const token = getToken();
    if (token) {
      config.headers.Authorization = `Bearer ${token}`;
    }
    return config;
  },
  (error) => {
    return Promise.reject(error);
  }
);

// 响应拦截器 - 处理401错误
api.interceptors.response.use(
  (response) => response,
  (error) => {
    if (error.response?.status === 401) {
      // Token无效或已加入黑名单，清除登录状态并跳转登录页
      const { logout } = useAuth();
      logout();
      const currentRoute = router.currentRoute.value;
      if (currentRoute.path !== '/') {
        const query: Record<string, string> = { mode: 'login' };
        if (currentRoute.fullPath && currentRoute.fullPath !== '/') {
          query.redirect = currentRoute.fullPath;
        }
        router.push({ path: '/', query });
      }
    }
    return Promise.reject(error);
  }
);

export default api;

// src/api/http.ts - Axios配置（带Token自动携带和401处理）
import axios from 'axios';
import { useAuth } from '../stores/auth';
import { router } from '../router';

const api = axios.create({
  baseURL: 'http://localhost:8080/api',
  timeout: 10000,
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
      // 跳转到登录页（排除登录/注册页避免死循环）
      const currentPath = router.currentRoute.value.path;
      if (!['/login', '/register'].includes(currentPath)) {
        router.push({ path: '/login', query: { redirect: currentPath } });
      }
    }
    return Promise.reject(error);
  }
);

export default api;

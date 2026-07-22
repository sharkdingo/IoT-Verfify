// src/api/http.ts - Axios配置（带Token自动携带和401处理）
import axios from 'axios';
import type { InternalAxiosRequestConfig } from 'axios';
import { useAuth } from '../stores/auth';
import { router } from '../router';
import { publishBoardInvalidation } from '@/utils/boardInvalidation';

const api = axios.create({
  // Default to a relative "/api" so dev goes through the Vite proxy and prod through
  // the same-origin reverse proxy (Nginx). Set VITE_API_BASE_URL for cross-origin.
  baseURL: (import.meta.env.VITE_API_BASE_URL || '') + '/api',
  timeout: 100000,
  headers: {
    'Content-Type': 'application/json'
  }
});

type BoardAwareRequestConfig = InternalAxiosRequestConfig & {
  boardInvalidationUserId?: number
  authTokenAtRequest?: string | null
}

export const isBoardMutationRequest = (config: { url?: string; method?: string }) => {
  const method = (config.method || 'get').toLowerCase()
  if (method === 'get' || method === 'head' || method === 'options') return false
  const path = (config.url || '').split('?')[0]
  if (/^\/?board\/(?:rules\/check-(?:duplicate|similarity)|(?:rules|specs)\/recommend)$/.test(path)) return false
  return /^\/?board\/(nodes|environment|specs|rules|templates|batch)(?:\/|$)/.test(path)
    || /^\/?verify\/traces\/[^/]+\/fix\/apply$/.test(path)
}

// 请求拦截器 - 自动添加Token
api.interceptors.request.use(
  (config) => {
    const { getToken, getUser } = useAuth();
    const token = getToken();
    if (token) {
      config.headers.Authorization = `Bearer ${token}`;
    }
    ;(config as BoardAwareRequestConfig).authTokenAtRequest = token
    ;(config as BoardAwareRequestConfig).boardInvalidationUserId = getUser()?.userId
    return config;
  },
  (error) => {
    return Promise.reject(error);
  }
);

// 响应拦截器 - 处理401错误
api.interceptors.response.use(
  (response) => {
    if (isBoardMutationRequest(response.config)) {
      publishBoardInvalidation(
        (response.config as BoardAwareRequestConfig).boardInvalidationUserId,
        'http-mutation'
      )
    }
    return response
  },
  (error) => {
    if (error.response?.status === 401) {
      const requestConfig = (error.config || error.response?.config) as BoardAwareRequestConfig | undefined
      const requestToken = requestConfig?.authTokenAtRequest ?? null
      const { logoutIfTokenMatches } = useAuth();
      if (logoutIfTokenMatches(requestToken)) {
        const currentRoute = router.currentRoute.value;
        if (currentRoute.path !== '/') {
          const query: Record<string, string> = { mode: 'login' };
          if (currentRoute.fullPath && currentRoute.fullPath !== '/') {
            query.redirect = currentRoute.fullPath;
          }
          router.push({ path: '/', query });
        }
      }
    }
    return Promise.reject(error);
  }
);

export default api;

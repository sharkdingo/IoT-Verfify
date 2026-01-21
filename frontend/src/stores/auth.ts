// src/stores/auth.ts - 认证状态管理（使用Vue reactive）
import { reactive, readonly } from 'vue';
import type { UserInfo } from '../types/auth';

interface AuthState {
  token: string | null;
  user: UserInfo | null;
  isLoggedIn: boolean;
}

const TOKEN_KEY = 'iot_verify_token';
const USER_KEY = 'iot_verify_user';

// 初始化状态
const getInitialState = (): AuthState => {
  const token = localStorage.getItem(TOKEN_KEY);
  const userStr = localStorage.getItem(USER_KEY);
  
  if (token && userStr) {
    try {
      const user = JSON.parse(userStr);
      return {
        token,
        user,
        isLoggedIn: true
      };
    } catch {
      return {
        token: null,
        user: null,
        isLoggedIn: false
      };
    }
  }
  
  return {
    token: null,
    user: null,
    isLoggedIn: false
  };
};

const state = reactive<AuthState>(getInitialState());

// 只读引用，供外部使用
export const useAuth = () => {
  // 登录成功
  const login = (token: string, user: UserInfo) => {
    state.token = token;
    state.user = user;
    state.isLoggedIn = true;
    localStorage.setItem(TOKEN_KEY, token);
    localStorage.setItem(USER_KEY, JSON.stringify(user));
  };

  // 登出
  const logout = () => {
    state.token = null;
    state.user = null;
    state.isLoggedIn = false;
    localStorage.removeItem(TOKEN_KEY);
    localStorage.removeItem(USER_KEY);
  };

  // 获取token
  const getToken = (): string | null => state.token;

  // 获取用户信息
  const getUser = (): UserInfo | null => state.user;

  // 是否已登录
  const isAuthenticated = (): boolean => state.isLoggedIn;

  return {
    state: readonly(state),
    login,
    logout,
    getToken,
    getUser,
    isAuthenticated
  };
};

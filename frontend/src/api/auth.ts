// src/api/auth.ts - 认证API
import api from './http';
import type { 
  LoginRequest, 
  LoginResponse, 
  RegisterRequest, 
  RegisterResponse,
  Result 
} from '../types/auth';

export const authApi = {
  // 登录
  async login(data: LoginRequest): Promise<Result<LoginResponse>> {
    const response = await api.post<Result<LoginResponse>>('/auth/login', data);
    return response.data;
  },

  // 注册
  async register(data: RegisterRequest): Promise<Result<RegisterResponse>> {
    const response = await api.post<Result<RegisterResponse>>('/auth/register', data);
    return response.data;
  },

  // 登出
  async logout(): Promise<Result<void>> {
    const response = await api.post<Result<void>>('/auth/logout');
    return response.data;
  }
};

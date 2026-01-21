// src/types/auth.ts

// 登录请求
export interface LoginRequest {
  phone: string;
  password: string;
}

// 注册请求
export interface RegisterRequest {
  phone: string;
  username: string;
  password: string;
}

// 登录响应（包含token）
export interface LoginResponse {
  userId: number;
  phone: string;
  username: string;
  token: string;
}

// 注册响应（不包含token）
export interface RegisterResponse {
  userId: number;
  phone: string;
  username: string;
}

// 当前用户信息
export interface UserInfo {
  userId: number;
  phone: string;
  username: string;
}

// 全局Result响应包装
export interface Result<T> {
  code: number;
  message: string;
  data: T;
}

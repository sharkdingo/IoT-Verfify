// src/types/verify.ts

export interface VerificationRequest {
  devices: any[];
  rules: any[];
  specs: any[];
  isAttack: boolean;
  intensity: number;
}

export interface VerificationResult {
  safe: boolean;
  traces: Trace[];
  specResults: boolean[];
  checkLogs: string[];
  nusmvOutput: string;
}

export interface Trace {
  id: number;
  userId: number;
  violatedSpecId: string;
  violatedSpecJson: string;
  states: TraceState[];
  createdAt: string;
}

export interface TraceState {
  stateIndex: number;
  devices: TraceDevice[];
  envVariables?: TraceVariable[];  // 环境变量（如 a_temperature, a_airQuality）
}

export interface TraceDevice {
  deviceId: string;
  deviceLabel: string;
  templateName: string;
  state?: string;  // 新字段
  newState?: string;  // 兼容旧数据
  variables: TraceVariable[];
  trustPrivacy: TraceTrustPrivacy[];
  privacies: TraceTrustPrivacy[];
}

export interface TraceVariable {
  name: string;
  value: string;
  trust: string;
}

export interface TraceTrustPrivacy {
  name: string;
  trust: boolean;
  privacy: string;
}

export interface VerificationTask {
  id: number;
  userId: number;
  status: 'PENDING' | 'RUNNING' | 'COMPLETED' | 'FAILED' | 'CANCELLED';
  createdAt: string;
  startedAt?: string;
  completedAt?: string;
  processingTimeMs?: number;
  isSafe?: boolean;
  violatedSpecCount?: number;
  checkLogs?: string[];
  nusmvOutput?: string;
  errorMessage?: string;
}










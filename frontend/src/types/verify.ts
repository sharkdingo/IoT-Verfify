// src/types/verify.ts

export interface VerificationRequest {
  devices: any[];
  rules: any[];
  specs: any[];
  isAttack: boolean;
  intensity: number;
  enablePrivacy: boolean;
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
  state?: string;
  mode?: string;                       // 新增：状态机名称
  newState?: string;                   // 保留：旧数据兼容，多处组件仍在 fallback 读取
  variables: TraceVariable[];
  trustPrivacy?: TraceTrustPrivacy[];   // 改为可选
  privacies?: TraceTrustPrivacy[];      // 改为可选
}

export interface TraceVariable {
  name: string;
  value: string;
  trust?: string;    // 改为可选
}

export interface TraceTrustPrivacy {
  name: string;
  trust?: boolean | null;   // 后端 Boolean 包装类型，支持 true/false/null
  privacy: string;
}

export interface VerificationTask {
  id: number;
  // userId 已删除 — 后端不返回，前端无使用处
  status: 'PENDING' | 'RUNNING' | 'COMPLETED' | 'FAILED' | 'CANCELLED';
  createdAt: string;
  startedAt?: string;
  completedAt?: string;
  processingTimeMs?: number;
  progress?: number;       // 新增：0-100 进度
  isSafe?: boolean;
  violatedSpecCount?: number;
  checkLogs?: string[];
  nusmvOutput?: string;    // 后端 TaskDto 不返回，但 Board.vue 仍在读取，保留为可选
  errorMessage?: string;
}










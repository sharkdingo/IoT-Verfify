// src/types/verify.ts

export interface VerificationRequest {
  devices: any[];
  rules: any[];
  specs: any[];
  isAttack: boolean;
  intensity: number;
  enablePrivacy: boolean;
}

export interface SpecResult {
  specId: string;
  passed: boolean;
  expression: string;
}

export interface VerificationResult {
  safe: boolean;
  traces: Trace[];
  specResults: SpecResult[];
  checkLogs: string[];
  nusmvOutput: string;
  disabledRuleCount?: number;
  skippedSpecCount?: number;
}

export interface Trace {
  id: number;
  userId: number;
  verificationTaskId?: number;   // backend TraceDto.verificationTaskId (Long, null for sync verifications)
  violatedSpecId: string;
  violatedSpecJson: string;
  states: TraceState[];
  // Verification-context flags derived from the trace's stored request snapshot (backend TraceDto).
  // Null/undefined for legacy traces recorded before the snapshot was saved.
  isAttack?: boolean;
  intensity?: number;
  enablePrivacy?: boolean;
  createdAt: string;
}

export interface TraceState {
  stateIndex: number;
  devices: TraceDevice[];
  rules?: number[];                     // indices of rules triggered in this state (backend List<Integer>)
  trustPrivacies?: TraceTrustPrivacy[]; // state-level trust/privacy entries (backend List<TraceTrustPrivacyDto>)
  envVariables?: TraceVariable[];       // environment variables (e.g. a_temperature, a_airQuality)
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
  disabledRuleCount?: number;
  skippedSpecCount?: number;
  specResults?: SpecResult[];
  nusmvOutput?: string;
  errorMessage?: string;
}

export type VerificationTaskSummary = Pick<
  VerificationTask,
  | 'id'
  | 'status'
  | 'createdAt'
  | 'startedAt'
  | 'completedAt'
  | 'processingTimeMs'
  | 'progress'
  | 'isSafe'
  | 'violatedSpecCount'
  | 'disabledRuleCount'
  | 'skippedSpecCount'
  | 'errorMessage'
>

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
}

export interface TraceDevice {
  deviceId: string;
  deviceLabel: string;
  templateName: string;
  newState: string;
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






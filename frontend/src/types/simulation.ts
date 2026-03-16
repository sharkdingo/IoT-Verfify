// src/types/simulation.ts - 模拟功能相关类型定义

// 模拟请求 DTO
export interface SimulationRequest {
  devices: any[]
  rules: any[]
  steps: number
  isAttack: boolean
  intensity: number
  enablePrivacy: boolean
}

// 模拟结果 DTO
export interface SimulationResult {
  states: SimulationState[]
  steps: number
  requestedSteps: number
  nusmvOutput: string
  logs: string[]
}

// 模拟状态
export interface SimulationState {
  stateIndex: number
  devices: SimulationDevice[]
  envVariables?: SimulationVariable[]
}

// 模拟中的设备
export interface SimulationDevice {
  deviceId: string
  deviceLabel: string
  templateName: string
  state?: string
  mode?: string
  variables: SimulationVariable[]
  trustPrivacy?: SimulationTrustPrivacy[]
  privacies?: SimulationTrustPrivacy[]
}

// 模拟变量
export interface SimulationVariable {
  name: string
  value: string
  trust?: string
}

// 可信度/隐私
export interface SimulationTrustPrivacy {
  name: string
  trust?: boolean
  privacy?: string
}

// 模拟记录摘要 (列表用) — SimulationTraceSummaryDto 不返回 userId
export interface SimulationTraceSummary {
  id: number
  requestedSteps: number
  steps: number
  createdAt: string
}

// 模拟记录详情 — SimulationTraceDto 返回 userId
export interface SimulationTrace extends SimulationTraceSummary {
  userId?: number          // 详情接口返回，摘要不返回，标可选
  states: SimulationState[]
  logs: string[]
  nusmvOutput: string
  requestJson: string
}

// 模拟任务状态
export type SimulationTaskStatus = 'PENDING' | 'RUNNING' | 'COMPLETED' | 'FAILED' | 'CANCELLED'

// 模拟任务
export interface SimulationTask {
  id: number
  // userId 已删除 — 后端不返回
  status: SimulationTaskStatus
  requestedSteps: number
  steps: number
  errorMessage?: string
  checkLogs?: string[]
  createdAt: string
  startedAt?: string
  completedAt?: string
  processingTimeMs?: number
  progress?: number       // 新增：0-100 进度
  simulationTraceId?: number
}



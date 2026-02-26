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

// 模拟记录摘要 (列表用)
export interface SimulationTraceSummary {
  id: number
  userId: number
  requestedSteps: number
  steps: number
  createdAt: string
}

// 模拟记录详情
export interface SimulationTrace extends SimulationTraceSummary {
  states: SimulationState[]
  logs: string[]
  nusmvOutput: string
  requestJson: string
}



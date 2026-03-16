// src/api/simulation.ts - Simulation API
import api from './http'
import type { SimulationRequest, SimulationResult, SimulationTrace, SimulationTraceSummary, SimulationTask } from '@/types/simulation'

// 辅助函数：解包Result
const unpack = <T>(response: any): T => {
  return response.data.data
}

export default {
  // 执行模拟（不保存）- 同步
  simulate: async (req: SimulationRequest): Promise<SimulationResult> => {
    return unpack<SimulationResult>(await api.post('/simulate', req))
  },

  // 执行异步模拟（不保存，返回任务ID）
  simulateAsync: async (req: SimulationRequest): Promise<number> => {
    return unpack<number>(await api.post('/simulate/async', req))
  },

  // 获取任务状态
  getTask: async (taskId: number): Promise<SimulationTask> => {
    return unpack<SimulationTask>(await api.get(`/simulate/tasks/${taskId}`))
  },

  // 获取任务进度
  getTaskProgress: async (taskId: number): Promise<number> => {
    return unpack<number>(await api.get(`/simulate/tasks/${taskId}/progress`))
  },

  // 取消任务
  cancelTask: async (taskId: number): Promise<boolean> => {
    return unpack<boolean>(await api.post(`/simulate/tasks/${taskId}/cancel`))
  },

  // 执行模拟并保存到数据库
  simulateAndSave: async (req: SimulationRequest): Promise<SimulationTrace> => {
    return unpack<SimulationTrace>(await api.post('/simulate/traces', req))
  },

  // 获取用户模拟记录列表
  getUserSimulations: async (): Promise<SimulationTraceSummary[]> => {
    return unpack<SimulationTraceSummary[]>(await api.get('/simulate/traces'))
  },

  // 获取单条模拟记录
  getSimulation: async (id: number): Promise<SimulationTrace> => {
    return unpack<SimulationTrace>(await api.get(`/simulate/traces/${id}`))
  },

  // 删除模拟记录
  deleteSimulation: async (id: number): Promise<void> => {
    return unpack<void>(await api.delete(`/simulate/traces/${id}`))
  }
}

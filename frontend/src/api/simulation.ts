// src/api/simulation.ts - Simulation API
import api from './http'
import type { SimulationRequest, SimulationResult, SimulationTrace, SimulationTraceSummary } from '@/types/simulation'

// 辅助函数：解包Result
const unpack = <T>(response: any): T => {
  return response.data.data
}

export default {
  // 执行模拟（不保存）
  simulate: async (req: SimulationRequest): Promise<SimulationResult> => {
    return unpack<SimulationResult>(await api.post('/verify/simulate', req))
  },

  // 执行模拟并保存到数据库
  simulateAndSave: async (req: SimulationRequest): Promise<SimulationTrace> => {
    return unpack<SimulationTrace>(await api.post('/verify/simulations', req))
  },

  // 获取用户模拟记录列表
  getUserSimulations: async (): Promise<SimulationTraceSummary[]> => {
    return unpack<SimulationTraceSummary[]>(await api.get('/verify/simulations'))
  },

  // 获取单条模拟记录
  getSimulation: async (id: number): Promise<SimulationTrace> => {
    return unpack<SimulationTrace>(await api.get(`/verify/simulations/${id}`))
  },

  // 删除模拟记录
  deleteSimulation: async (id: number): Promise<void> => {
    return unpack<void>(await api.delete(`/verify/simulations/${id}`))
  }
}



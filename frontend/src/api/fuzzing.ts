import api from './http'
import type {
  FuzzingFinding,
  FuzzPaperDomainPreview,
  FuzzWorkloadPreview,
  FuzzingRequest,
  FuzzingRun,
  FuzzingRunSummary,
  FuzzingTask,
  FuzzingTaskSummary
} from '@/types/fuzzing'
import { isValidFuzzPaperDomainFingerprint } from '@/types/fuzzing'
import type { TaskCancellationResult } from '@/types/task'
import {
  validateFuzzingFinding,
  validateFuzzingFindingList,
  validateFuzzingRun,
  validateFuzzingRunSummaryList,
  validateFuzzingTask,
  validateFuzzingTaskSummaryList,
  validateFuzzPaperDomainPreview,
  validateFuzzWorkloadPreview
} from '@/utils/fuzzingResponse'
import { validateTaskCancellationResult, validateTaskProgress } from '@/utils/runResponse'

const unpack = <T>(response: any): T => response.data.data

export default {
  getCurrentModelFingerprint: async (): Promise<string> => {
    const fingerprint = unpack<unknown>(await api.get('/fuzz/model-fingerprint'))
    if (!isValidFuzzPaperDomainFingerprint(fingerprint)) {
      throw new TypeError('The current Board model fingerprint is invalid')
    }
    return fingerprint
  },

  previewPaperDomain: async (pathLength: number): Promise<FuzzPaperDomainPreview> =>
    validateFuzzPaperDomainPreview(
      unpack<unknown>(await api.post('/fuzz/paper-domain/preview', { pathLength })),
      pathLength
    ),

  previewWorkload: async (request: Pick<
    FuzzingRequest,
    'maxIterations' | 'pathLength' | 'populationSize'
  >): Promise<FuzzWorkloadPreview> =>
    validateFuzzWorkloadPreview(
      unpack<unknown>(await api.post('/fuzz/workload/preview', request)),
      request
    ),

  startAsync: async (request: FuzzingRequest): Promise<FuzzingTask> => {
    if (request.explorationMode === 'PAPER_COMPATIBLE'
      && !isValidFuzzPaperDomainFingerprint(request.paperDomainFingerprint)) {
      throw new TypeError('The random-state input range is missing or no longer valid')
    }
    if (request.explorationMode === 'BOARD_SNAPSHOT'
      && request.paperDomainFingerprint !== undefined) {
      throw new TypeError('The selected search strategy contains incompatible input-range data')
    }
    return validateFuzzingTask(unpack<unknown>(await api.post('/fuzz/async', request)))
  },

  getTasks: async (
    excludeTaskIds: number[] = [],
    page = 0,
    size = 100
  ): Promise<FuzzingTaskSummary[]> => {
    const params = {
      ...(excludeTaskIds.length > 0 ? { excludeTaskIds: excludeTaskIds.join(',') } : {}),
      page,
      size
    }
    return validateFuzzingTaskSummaryList(
      unpack<unknown>(await api.get('/fuzz/tasks', { params }))
    )
  },

  getTask: async (taskId: number): Promise<FuzzingTask> =>
    validateFuzzingTask(unpack<unknown>(await api.get(`/fuzz/tasks/${taskId}`))),

  getTaskProgress: async (taskId: number): Promise<number> =>
    validateTaskProgress(
      unpack<unknown>(await api.get(`/fuzz/tasks/${taskId}/progress`)),
      'Fuzz task progress'
    ),

  cancelTask: async (taskId: number): Promise<TaskCancellationResult> =>
    validateTaskCancellationResult(
      unpack<unknown>(await api.post(`/fuzz/tasks/${taskId}/cancel`)),
      taskId,
      'Fuzz task cancellation'
    ),

  deleteTask: async (taskId: number): Promise<void> =>
    unpack<void>(await api.delete(`/fuzz/tasks/${taskId}`)),

  getRuns: async (page = 0, size = 25): Promise<FuzzingRunSummary[]> =>
    validateFuzzingRunSummaryList(
      unpack<unknown>(await api.get('/fuzz/runs', { params: { page, size } }))
    ),

  getRun: async (runId: number): Promise<FuzzingRun> =>
    validateFuzzingRun(unpack<unknown>(await api.get(`/fuzz/runs/${runId}`))),

  getRunFindings: async (runId: number): Promise<FuzzingFinding[]> =>
    validateFuzzingFindingList(unpack<unknown>(await api.get(`/fuzz/runs/${runId}/findings`))),

  deleteRun: async (runId: number): Promise<void> =>
    unpack<void>(await api.delete(`/fuzz/runs/${runId}`)),

  getFinding: async (findingId: number): Promise<FuzzingFinding> =>
    validateFuzzingFinding(unpack<unknown>(await api.get(`/fuzz/findings/${findingId}`)))
}

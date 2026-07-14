export type RunPersistenceStatus = 'SAVED' | 'NOT_REQUESTED' | 'FAILED' | 'OUTCOME_UNKNOWN'

export interface RunPersistence {
  status: RunPersistenceStatus
  runId?: number
  reasonCode?: 'RUN_HISTORY_SAVE_FAILED' | 'RUN_HISTORY_SAVE_OUTCOME_UNKNOWN' | string
}

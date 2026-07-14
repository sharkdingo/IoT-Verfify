export type AsyncTaskStatus = 'PENDING' | 'RUNNING' | 'COMPLETED' | 'FAILED' | 'CANCELLED'

export type TaskCancellationOutcome =
  | 'ACCEPTED'
  | 'ALREADY_CANCELLED'
  | 'ALREADY_COMPLETED'
  | 'ALREADY_FAILED'
  | 'NO_LONGER_CANCELLABLE'

export interface TaskCancellationResult {
  taskId: number
  cancellationAccepted: boolean
  cancellationOutcome: TaskCancellationOutcome
  taskStatus: AsyncTaskStatus
  executionMayStillBeStopping: boolean
}

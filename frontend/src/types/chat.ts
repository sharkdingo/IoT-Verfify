// src/types/chat.ts

// Matches backend ChatSessionResponseDto.
export interface ChatSession {
    id: string
    userId: number
    title: string | null
    createdAt?: string
    updatedAt: string
    active: boolean
}

export interface ChatSessionActivity {
    sessionId: string
    active: boolean
}

export type ChatConfirmationKind = 'DESTRUCTIVE' | 'DEFAULT_TEMPLATE_RESET' | 'SCENE_REPLACEMENT'
export type ChatConfirmationAction = 'CONFIRM' | 'CANCEL'

export interface ChatConfirmationCommand {
    action: ChatConfirmationAction
    kind: ChatConfirmationKind
}

export interface ChatPendingConfirmation {
    sessionId: string
    kinds: ChatConfirmationKind[]
}

// Matches backend ChatMessageResponseDto.
export interface ChatMessage {
    id?: number
    sessionId?: string
    role: 'user' | 'assistant'
    content: string
    turnId?: string
    createdAt?: string
    // Persisted by the backend for history and populated live while streaming.
    executionTrace?: StreamProgress[]
    executionElapsedSeconds?: number
    executionStatus?: 'COMPLETED' | 'AWAITING_CONFIRMATION' | 'PARTIAL' | 'STOPPED' | 'DISCONNECTED' | 'FAILED'
}

export interface ChatHistoryPage {
    messages: ChatMessage[]
    nextBeforeId: number | null
    hasMore: boolean
}

export type StreamRefreshTarget =
    | 'device_list'
    | 'environment_list'
    | 'rule_list'
    | 'spec_list'
    | 'template_list'
    | 'run_history'
    | 'board_state'

export interface StreamCommand {
    type: 'REFRESH_DATA'
    payload: { target: StreamRefreshTarget }
}

type StreamProgressBase = {
    toolName?: string | null
    round?: number | null
    successfulSteps?: number | null
    failedSteps?: number | null
    unconfirmedSteps?: number | null
    detail?: string | null
}

type ToolResultOutcome =
    | 'USABLE'
    | 'PARTIAL'
    | 'FAILED'
    | 'RESULT_UNAVAILABLE'
    | 'CONFIRMATION_REQUIRED'

type ExecutionGuardOutcome = 'NO_PROGRESS' | 'EMERGENCY_LIMIT'

export type StreamProgress = StreamProgressBase & (
    | {
        stage: 'CONTEXT_READY' | 'TASK_RESUMED' | 'PLANNING' | 'REASONING' | 'TOOL_EXECUTION' | 'WRITING_RESPONSE'
        outcome?: null
      }
    | { stage: 'TOOL_RESULT'; outcome: ToolResultOutcome }
    | { stage: 'EXECUTION_GUARD'; outcome: ExecutionGuardOutcome }
)

export type ChatLogoutPreparation = 'ready' | 'outcome-unknown' | 'reconciliation-failed'

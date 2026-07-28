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

export type ChatExecutionStatus =
    | 'COMPLETED'
    | 'AWAITING_CONFIRMATION'
    | 'PARTIAL'
    | 'STOPPED'
    | 'DISCONNECTED'
    | 'FAILED'

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
    executionStatus?: ChatExecutionStatus
}

export interface PersistedChatMessage extends ChatMessage {
    id: number
    sessionId: string
    turnId: string
    createdAt: string
}

export interface ChatHistoryPage {
    messages: PersistedChatMessage[]
    nextBeforeId: number | null
    hasMore: boolean
}

/**
 * Every board state an assistant `REFRESH_DATA` command can name.
 *
 * Single source of truth: the SSE frame validator (`api/chat.ts`) and the board's target table
 * (`views/board/assistantRefresh.ts`) both derive from this, because they used to repeat the same
 * seven strings independently — adding a target meant editing three lists, and missing one silently
 * either rejected a valid frame or skipped the refresh it asked for.
 */
export const STREAM_REFRESH_TARGETS = [
    'device_list',
    'environment_list',
    'rule_list',
    'spec_list',
    'template_list',
    'run_history',
    'board_state'
] as const

export type StreamRefreshTarget = typeof STREAM_REFRESH_TARGETS[number]

export interface StreamCommand {
    type: 'REFRESH_DATA'
    payload: { target: StreamRefreshTarget }
}

export interface StreamTerminal {
    turnId: string
    executionStatus: ChatExecutionStatus
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

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
    role: 'user' | 'assistant' | 'tool'
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

export interface StreamCommand {
    type: string;
    payload?: Record<string, any>;
}

export interface StreamProgress {
    stage: 'CONTEXT_READY' | 'TASK_RESUMED' | 'PLANNING' | 'REASONING' | 'TOOL_EXECUTION' | 'TOOL_RESULT' | 'EXECUTION_GUARD' | 'WRITING_RESPONSE'
    toolName?: string | null
    round?: number | null
    outcome?: 'USABLE' | 'FAILED' | 'RESULT_UNAVAILABLE' | 'CONFIRMATION_REQUIRED' | 'NO_PROGRESS' | 'EMERGENCY_LIMIT' | null
    successfulSteps?: number | null
    failedSteps?: number | null
    unconfirmedSteps?: number | null
    detail?: string | null
}

export type ChatLogoutPreparation = 'ready' | 'outcome-unknown' | 'reconciliation-failed'

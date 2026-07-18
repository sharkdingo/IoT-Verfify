// src/types/chat.ts

// Matches backend ChatSessionResponseDto.
export interface ChatSession {
    id: string
    userId: number
    title: string | null
    createdAt?: string
    updatedAt: string
}

export interface ChatSessionActivity {
    sessionId: string
    active: boolean
}

// Matches backend ChatMessageResponseDto.
export interface ChatMessage {
    id?: number
    sessionId?: string
    role: 'user' | 'assistant' | 'tool'
    content: string
    createdAt?: string
    // Persisted by the backend for history and populated live while streaming.
    executionTrace?: StreamProgress[]
    executionElapsedSeconds?: number
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

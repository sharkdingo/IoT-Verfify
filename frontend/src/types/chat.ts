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
}

export interface StreamCommand {
    type: string;
    payload?: Record<string, any>;
}

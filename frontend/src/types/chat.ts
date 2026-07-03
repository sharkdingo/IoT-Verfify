// src/types/chat.ts

// Matches backend ChatSessionResponseDto.
export interface ChatSession {
    id: string
    userId: number
    title: string
    createdAt?: string
    updatedAt: string
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
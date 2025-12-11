// src/types/chat.ts

// 定义类型
export interface ChatSession {
    id: string
    userId: string
    title: string
    updatedAt: string
}

export interface ChatMessage {
    id?: number
    role: 'user' | 'assistant' | 'tool'
    content: string
}

export interface StreamCommand {
    type: string;
    payload?: Record<string, any>;
}
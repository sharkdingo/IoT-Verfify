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
    role: 'user' | 'assistant'
    content: string
}
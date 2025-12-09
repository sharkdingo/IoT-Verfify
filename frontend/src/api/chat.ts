// src/api/chat.ts
// 注意：请确认您的 http 封装文件路径是否正确，之前建议是 '@/utils/http'
import api from '@/api/http'
import { ChatMessage, ChatSession } from "@/types/chat"
// --- 1. 定义后端的 Result 包装结构 ---
export interface Result<T> {
    code: number;    // 200 成功, 500 失败
    message: string; // 错误信息
    data: T;         // 真正的数据
}

/**
 * 获取会话列表
 * 返回值类型变为: Promise<Result<ChatSession[]>>
 */
export const getSessionList = (userId: string) => {
    return api.get<any, Result<ChatSession[]>>('/chat/sessions', {
        params: { userId }
    })
}

/**
 * 创建新会话
 * 返回值类型变为: Promise<Result<ChatSession>>
 */
export const createSession = (userId: string) => {
    return api.post<any, Result<ChatSession>>('/chat/sessions', null, {
        params: { userId }
    })
}

/**
 * 获取会话历史记录
 * 返回值类型变为: Promise<Result<ChatMessage[]>>
 */
export const getSessionHistory = (sessionId: string) => {
    return api.get<any, Result<ChatMessage[]>>(`/chat/sessions/${sessionId}/messages`)
}

/**
 * 删除会话
 * 返回值类型变为: Promise<Result<void>>
 */
export const deleteSession = (sessionId: string) => {
    return api.delete<any, Result<void>>(`/chat/sessions/${sessionId}`)
}

/**
 * 发送流式消息
 * 注意：流式接口后端返回的是 SseEmitter，不是 Result JSON，所以这里逻辑不需要针对 Result 修改
 * 但必须保留 data: 前缀的解析逻辑
 */
export const sendStreamChat = async (
    sessionId: string,
    content: string,
    callbacks: {
        onMessage: (text: string) => void
        onError?: (err: any) => void
        onFinish?: () => void
    }
) => {
    try {
        // 使用 fetch 是因为 axios 不支持流式读取
        const response = await fetch('http://localhost:8080/api/chat/completions', {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json',
            },
            body: JSON.stringify({ sessionId, content })
        })

        if (!response.ok) {
            // 如果后端报错（如 500），尝试读取错误信息
            const errText = await response.text();
            throw new Error(errText || response.statusText);
        }

        if (!response.body) throw new Error('No response body')

        const reader = response.body.getReader()
        const decoder = new TextDecoder('utf-8')
        let buffer = ''

        while (true) {
            const { done, value } = await reader.read()
            if (done) break

            const chunk = decoder.decode(value, { stream: true })
            buffer += chunk

            const lines = buffer.split('\n')
            buffer = lines.pop() || ''

            for (const line of lines) {
                const trimmed = line.trim()
                if (!trimmed) continue

                // 解析 data: 前缀
                if (trimmed.startsWith('data:')) {
                    const data = trimmed.slice(5)
                    if (data.trim() !== '[DONE]') {
                        callbacks.onMessage(data)
                    }
                }
            }
        }

        if (callbacks.onFinish) callbacks.onFinish()

    } catch (error) {
        console.error('Stream Error:', error)
        if (callbacks.onError) callbacks.onError(error)
    }
}
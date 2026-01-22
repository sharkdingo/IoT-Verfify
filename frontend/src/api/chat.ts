// src/api/chat.ts - Chat API
import api from '@/api/http'
import { ChatMessage, ChatSession, StreamCommand } from "@/types/chat"
import { useAuth } from '@/stores/auth'

// 辅助函数：解包Result（后端返回 { code, message, data }）
const unpack = <T>(response: any): T => {
  return response.data.data;
};

/**
 * 获取会话列表（使用 JWT token 中的 userId）
 */
export const getSessionList = async (): Promise<ChatSession[]> => {
  const response = await api.get<any>('/chat/sessions');
  return unpack<ChatSession[]>(response);
}

/**
 * 创建新会话（使用 JWT token 中的 userId）
 */
export const createSession = async (): Promise<ChatSession> => {
  const response = await api.post<any>('/chat/sessions', null);
  return unpack<ChatSession>(response);
}

/**
 * 获取会话历史记录
 */
export const getSessionHistory = async (sessionId: string): Promise<ChatMessage[]> => {
  const response = await api.get<any>(`/chat/sessions/${sessionId}/messages`);
  return unpack<ChatMessage[]>(response);
}

/**
 * 删除会话
 */
export const deleteSession = async (sessionId: string): Promise<void> => {
  await api.delete(`/chat/sessions/${sessionId}`);
}

/**
 * 发送流式消息（添加Authorization header）
 */
export const sendStreamChat = async (
    sessionId: string,
    content: string,
    callbacks: {
        onMessage: (text: string) => void
        onCommand?: (cmd: StreamCommand) => void;
        onError?: (err: any) => void
        onFinish?: () => void
    },
    controller?: AbortController
) => {
    try {
        const { getToken } = useAuth();
        const token = getToken();
        const API_BASE = import.meta.env.VITE_API_BASE_URL || 'http://localhost:8080';
        
        const headers: Record<string, string> = {
            'Content-Type': 'application/json'
        };
        
        if (token) {
            headers['Authorization'] = `Bearer ${token}`;
        }
        
        const response = await fetch(`${API_BASE}/api/chat/completions`, {
            method: 'POST',
            headers,
            body: JSON.stringify({ sessionId, content }),
            signal: controller?.signal
        });

        if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
        }
        
        if (!response.body) {
            throw new Error('No response body');
        }

        const reader = response.body.getReader();
        const decoder = new TextDecoder('utf-8');
        let buffer = '';
        let hasReceivedContent = false;

        while (true) {
            const { done, value } = await reader.read();
            if (done) break;
            buffer += decoder.decode(value, { stream: true });
            const lines = buffer.split('\n');
            buffer = lines.pop() || '';

            for (const line of lines) {
                if (line.trim().startsWith('data:')) {
                    const dataStr = line.replace(/^data:\s?/, '');
                    if (dataStr.trim() === '[DONE]') continue;

                    try {
                        const json = JSON.parse(dataStr);
                        if (json.content) {
                            hasReceivedContent = true;
                            callbacks.onMessage(json.content);
                        }
                        if (json.command && callbacks.onCommand) {
                            callbacks.onCommand(json.command);
                        }
                    } catch (e) {
                        // 如果不是有效的 JSON，直接作为文本处理
                        if (dataStr.trim() && !dataStr.startsWith('[ERROR]')) {
                            hasReceivedContent = true;
                            callbacks.onMessage(dataStr);
                        }
                    }
                }
            }
        }

        // 只有在没有收到任何内容时才视为失败
        if (!hasReceivedContent) {
            throw new Error('No content received from server');
        }

        if (callbacks.onFinish) callbacks.onFinish();

    } catch (error: any) {
        if (error.name === 'AbortError') {
            if (callbacks.onFinish) callbacks.onFinish();
            return;
        }
        console.error('[Chat] 流式请求错误:', error.message);
        if (callbacks.onError) callbacks.onError(error);
        throw error;
    }
}

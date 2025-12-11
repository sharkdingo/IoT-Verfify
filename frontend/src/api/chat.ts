// src/api/chat.ts
// 注意：请确认您的 http 封装文件路径是否正确，之前建议是 '@/utils/http'
import api from '@/api/http'
import { ChatMessage, ChatSession, StreamCommand } from "@/types/chat"
// --- 定义后端的 Result 包装结构 ---
export interface Result<T> {
    code: number;    // 200 成功
    message: string; // 错误信息
    data: T;         // 真正的数据
}

// ==========================================
// 核心修改点：
// 因为 http.ts 没有拦截器，所以 api.get 返回的是 AxiosResponse。
// 我们需要用 async/await 手动返回 response.data，
// 这样组件里收到的就是干净的 { code, msg, data } 了。
// ==========================================

/**
 * 获取会话列表
 */
export const getSessionList = async (userId: string) => {
    const response = await api.get<Result<ChatSession[]>>('/chat/sessions', {
        params: { userId }
    })
    return response.data; // <--- 这里手动解包
}

/**
 * 创建新会话
 */
export const createSession = async (userId: string) => {
    const response = await api.post<Result<ChatSession>>('/chat/sessions', null, {
        params: { userId }
    })
    return response.data; // <--- 这里手动解包
}

/**
 * 获取会话历史记录
 */
export const getSessionHistory = async (sessionId: string) => {
    const response = await api.get<Result<ChatMessage[]>>(`/chat/sessions/${sessionId}/messages`)
    return response.data; // <--- 这里手动解包
}

/**
 * 删除会话
 */
export const deleteSession = async (sessionId: string) => {
    const response = await api.delete<Result<void>>(`/chat/sessions/${sessionId}`)
    return response.data; // <--- 这里手动解包
}

/**
 * 发送流式消息
 * (这个函数使用原生 fetch，不受 axios 影响，保持原样即可，但我加上了 controller 支持以防万一)
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
        const response = await fetch('http://localhost:8080/api/chat/completions', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ sessionId, content }),
            signal: controller?.signal
        })

        if (!response.ok) throw new Error(response.statusText);
        if (!response.body) throw new Error('No response body');

        const reader = response.body.getReader();
        const decoder = new TextDecoder('utf-8');
        let buffer = '';

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

                    // --- 核心修改：尝试解析 JSON ---
                    try {
                        // 后端发来的是 {"content": "标题\n表格"}
                        const json = JSON.parse(dataStr);
                        if (json.content) {
                            // 成功取回带换行的文本！
                            callbacks.onMessage(json.content);
                        }
                        if (json.command && callbacks.onCommand) {
                            callbacks.onCommand(json.command);
                        }
                    } catch (e) {
                        // 兼容旧逻辑或纯文本错误信息
                        callbacks.onMessage(dataStr);
                    }
                }
            }
        }

        if (callbacks.onFinish) callbacks.onFinish();

    } catch (error: any) {
        if (error.name === 'AbortError') {
            if (callbacks.onFinish) callbacks.onFinish();
            return;
        }
        console.error('Stream Error:', error);
        if (callbacks.onError) callbacks.onError(error);
    }
}
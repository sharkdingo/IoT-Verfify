// src/api/chat.ts - Chat API
import api from '@/api/http'
import { ChatMessage, ChatSession, ChatSessionActivity, StreamCommand } from "@/types/chat"
import { useAuth } from '@/stores/auth'

export type ChatStreamErrorKind =
    | 'HTTP_ERROR'
    | 'SERVER_FRAME'
    | 'MISSING_BODY'
    | 'EMPTY_STREAM'
    | 'INVALID_FRAME'
    | 'UNKNOWN'

export class ChatStreamError extends Error {
    readonly serverFrame: boolean
    readonly status?: number
    readonly kind: ChatStreamErrorKind
    readonly detail?: string

    constructor(message: string, options: {
        serverFrame?: boolean
        status?: number
        kind?: ChatStreamErrorKind
        detail?: string
    } = {}) {
        super(message)
        this.name = 'ChatStreamError'
        this.serverFrame = options.serverFrame ?? false
        this.status = options.status
        this.kind = options.kind ?? (this.serverFrame ? 'SERVER_FRAME' : 'UNKNOWN')
        this.detail = options.detail
    }
}

const unpack = <T>(response: any): T => {
  return response.data.data;
};

export const getSessionList = async (): Promise<ChatSession[]> => {
  const response = await api.get<any>('/chat/sessions');
  return unpack<ChatSession[]>(response);
}

export const createSession = async (signal?: AbortSignal): Promise<ChatSession> => {
  const response = await api.post<any>('/chat/sessions', null, { signal });
  return unpack<ChatSession>(response);
}

export const getSessionHistory = async (sessionId: string, signal?: AbortSignal): Promise<ChatMessage[]> => {
  const response = await api.get<any>(`/chat/sessions/${sessionId}/messages`, { signal });
  return unpack<ChatMessage[]>(response);
}

export const deleteSession = async (sessionId: string): Promise<void> => {
  await api.delete(`/chat/sessions/${sessionId}`);
}

export const getSessionActivity = async (sessionId: string): Promise<ChatSessionActivity> => {
  const response = await api.get<any>(`/chat/sessions/${sessionId}/activity`);
  const activity = unpack<ChatSessionActivity>(response);
  if (!activity || activity.sessionId !== sessionId || typeof activity.active !== 'boolean') {
    throw new Error('Chat session activity response is incomplete');
  }
  return activity;
}

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
        const { getToken, logout } = useAuth();
        const token = getToken();
        const API_BASE = import.meta.env.VITE_API_BASE_URL || '';

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
            if (response.status === 401 || response.status === 403) {
                logout();
            }
            const detail = await readErrorDetail(response);
            throw new ChatStreamError(`HTTP ${response.status}: ${detail}`, {
                kind: 'HTTP_ERROR',
                status: response.status,
                detail
            });
        }

        if (!response.body) {
            throw new ChatStreamError('No response body', { kind: 'MISSING_BODY' });
        }

        const reader = response.body.getReader();
        const decoder = new TextDecoder('utf-8');
        let buffer = '';
        let hasReceivedFrame = false;

        const serverErrorMessage = (content: string) => {
            const trimmed = content.trimStart();
            if (!trimmed.startsWith('[ERROR]')) return '';
            return trimmed.replace(/^\[ERROR\]\s*/, '').trim() || trimmed;
        };

        const handlePayload = (dataStr: string) => {
            const trimmed = dataStr.trim();
            if (!trimmed || trimmed === '[DONE]') return;

            hasReceivedFrame = true;

            if (trimmed.startsWith('{')) {
                let json: any;
                try {
                    json = JSON.parse(dataStr);
                } catch {
                    throw new ChatStreamError('Invalid server stream frame', { kind: 'INVALID_FRAME' });
                }
                const content = typeof json.content === 'string' ? json.content : '';
                const errorMessage = content ? serverErrorMessage(content) : '';
                if (errorMessage) {
                    throw new ChatStreamError(errorMessage, { kind: 'SERVER_FRAME', serverFrame: true });
                }
                if (json.command && callbacks.onCommand) {
                    callbacks.onCommand(json.command);
                }
                if (content) {
                    callbacks.onMessage(content);
                }
                return;
            }

            const errorMessage = serverErrorMessage(dataStr);
            if (errorMessage) {
                throw new ChatStreamError(errorMessage, { kind: 'SERVER_FRAME', serverFrame: true });
            }

            try {
                callbacks.onMessage(dataStr);
            } catch (error) {
                throw error;
            }
        };

        const handleEvent = (rawEvent: string) => {
            const dataLines = rawEvent
                .split(/\r?\n/)
                .map(line => line.trimEnd())
                .filter(line => line.trimStart().startsWith('data:'))
                .map(line => line.replace(/^\s*data:\s?/, ''));

            if (dataLines.length > 0) {
                handlePayload(dataLines.join('\n'));
            }
        };

        const drainEvents = () => {
            while (true) {
                const match = buffer.match(/\r?\n\r?\n/);
                if (!match || match.index === undefined) break;
                const eventText = buffer.slice(0, match.index);
                buffer = buffer.slice(match.index + match[0].length);
                handleEvent(eventText);
            }
        };

        while (true) {
            const { done, value } = await reader.read();
            if (done) {
                buffer += decoder.decode();
                break;
            }
            buffer += decoder.decode(value, { stream: true });
            drainEvents();
        }

        drainEvents();
        if (buffer.trim()) {
            handleEvent(buffer);
        }

        if (!hasReceivedFrame) {
            throw new ChatStreamError('No content received from server', { kind: 'EMPTY_STREAM' });
        }

        if (callbacks.onFinish) callbacks.onFinish();

    } catch (error: any) {
        if (error.name === 'AbortError') {
            return;
        }
        console.error('[Chat] Streaming request error:', error.message);
        if (callbacks.onError) callbacks.onError(error);
        throw error;
    }
}

const readErrorDetail = async (response: Response) => {
    const fallback = response.statusText || 'Request failed';
    try {
        const body = await response.text();
        if (!body) return fallback;
        try {
            const json = JSON.parse(body);
            return json?.message || json?.error || fallback;
        } catch {
            return body.slice(0, 200);
        }
    } catch {
        return fallback;
    }
};

// src/api/chat.ts - Chat API
import api from '@/api/http'
import type {
    ChatConfirmationCommand,
    ChatHistoryPage,
    ChatMessage,
    ChatPendingConfirmation,
    ChatSession,
    ChatSessionActivity,
    StreamCommand,
    StreamProgress
} from "@/types/chat"
import { useAuth } from '@/stores/auth'
import { router } from '@/router'

export const CHAT_ACTIVITY_TIMEOUT_MS = 2500

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
    readonly reasonCode?: string

    constructor(message: string, options: {
        serverFrame?: boolean
        status?: number
        kind?: ChatStreamErrorKind
        detail?: string
        reasonCode?: string
    } = {}) {
        super(message)
        this.name = 'ChatStreamError'
        this.serverFrame = options.serverFrame ?? false
        this.status = options.status
        this.kind = options.kind ?? (this.serverFrame ? 'SERVER_FRAME' : 'UNKNOWN')
        this.detail = options.detail
        this.reasonCode = options.reasonCode
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

export const getSessionHistory = async (
    sessionId: string,
    options: AbortSignal | { signal?: AbortSignal; beforeId?: number | null; limit?: number } = {}
): Promise<ChatHistoryPage> => {
  const normalized: { signal?: AbortSignal; beforeId?: number | null; limit?: number } =
      typeof AbortSignal !== 'undefined' && options instanceof AbortSignal
          ? { signal: options }
          : options as { signal?: AbortSignal; beforeId?: number | null; limit?: number };
  const params: Record<string, number> = {};
  if (normalized.beforeId != null) params.beforeId = normalized.beforeId;
  if (normalized.limit != null) params.limit = normalized.limit;
  const config: { signal?: AbortSignal; params?: Record<string, number> } = { signal: normalized.signal };
  if (Object.keys(params).length > 0) config.params = params;
  const response = await api.get<any>(`/chat/sessions/${encodeURIComponent(sessionId)}/messages`, config);
  const raw = unpack<ChatHistoryPage | ChatMessage[]>(response);
  if (Array.isArray(raw)) {
    return { messages: raw, nextBeforeId: null, hasMore: false };
  }
  if (!raw || !Array.isArray(raw.messages)
      || (raw.nextBeforeId !== null && typeof raw.nextBeforeId !== 'number')
      || typeof raw.hasMore !== 'boolean') {
    throw new Error('Chat history response is incomplete');
  }
  return raw;
}

export const requestSessionStop = async (sessionId: string): Promise<void> => {
  await api.post(`/chat/sessions/${sessionId}/stop`, null, { timeout: CHAT_ACTIVITY_TIMEOUT_MS });
}

export const deleteSession = async (sessionId: string): Promise<void> => {
  await api.delete(`/chat/sessions/${sessionId}`);
}

export const getSessionActivity = async (
    sessionId: string,
    options: { timeoutMs?: number; signal?: AbortSignal } = {}
): Promise<ChatSessionActivity> => {
  const response = await api.get<any>(`/chat/sessions/${sessionId}/activity`, {
    timeout: options.timeoutMs ?? CHAT_ACTIVITY_TIMEOUT_MS,
    signal: options.signal
  });
  const activity = unpack<ChatSessionActivity>(response);
  if (!activity || activity.sessionId !== sessionId || typeof activity.active !== 'boolean') {
    throw new Error('Chat session activity response is incomplete');
  }
  return activity;
}

export const getPendingConfirmation = async (
    sessionId: string,
    signal?: AbortSignal
): Promise<ChatPendingConfirmation> => {
  const response = await api.get<any>(`/chat/sessions/${sessionId}/confirmation`, { signal });
  const pending = unpack<ChatPendingConfirmation>(response);
  if (!pending || pending.sessionId !== sessionId || !Array.isArray(pending.kinds)) {
    throw new Error('Chat pending-confirmation response is incomplete');
  }
  return pending;
}

export const sendStreamChat = async (
    sessionId: string,
    content: string,
    callbacks: {
        onMessage: (text: string) => void
        onCommand?: (cmd: StreamCommand) => void;
        onProgress?: (progress: StreamProgress) => void;
        onAccepted?: () => void;
        onError?: (err: any) => void
        onFinish?: () => void
    },
    controller?: AbortController,
    turnId?: string,
    confirmation?: ChatConfirmationCommand
) => {
    try {
        const { getToken, logoutIfTokenMatches } = useAuth();
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
            body: JSON.stringify({
                sessionId,
                content,
                ...(turnId ? { turnId } : {}),
                ...(confirmation ? { confirmation } : {})
            }),
            signal: controller?.signal
        });

        if (!response.ok) {
            if (response.status === 401) {
                if (logoutIfTokenMatches(token)) {
                    const currentRoute = router.currentRoute.value;
                    if (currentRoute.path !== '/') {
                        const query: Record<string, string> = { mode: 'login' };
                        if (currentRoute.fullPath && currentRoute.fullPath !== '/') {
                            query.redirect = currentRoute.fullPath;
                        }
                        await router.push({ path: '/', query });
                    }
                }
            }
            const detail = await readErrorDetail(response);
            throw new ChatStreamError(`HTTP ${response.status}: ${detail.message}`, {
                kind: 'HTTP_ERROR',
                status: response.status,
                detail: detail.message,
                reasonCode: detail.reasonCode
            });
        }

        // A successful HTTP response means the backend claimed the chat slot and
        // persisted the request, even if a proxy/browser cannot expose the body.
        callbacks.onAccepted?.();

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
                if (json.progress && callbacks.onProgress) {
                    callbacks.onProgress(json.progress as StreamProgress);
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
        if (!body) return { message: fallback };
        try {
            const json = JSON.parse(body);
            return {
                message: json?.message || json?.error || fallback,
                reasonCode: typeof json?.data?.reasonCode === 'string' ? json.data.reasonCode : undefined
            };
        } catch {
            return { message: body.slice(0, 200) };
        }
    } catch {
        return { message: fallback };
    }
};

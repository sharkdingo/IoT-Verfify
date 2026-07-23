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

const CHAT_EXECUTION_STATUSES = new Set<string>([
  'COMPLETED',
  'AWAITING_CONFIRMATION',
  'PARTIAL',
  'STOPPED',
  'DISCONNECTED',
  'FAILED'
] satisfies Array<NonNullable<ChatMessage['executionStatus']>>);

const CHAT_ROLES = new Set<ChatMessage['role']>(['user', 'assistant']);
const STREAM_PROGRESS_STAGES = new Set<StreamProgress['stage']>([
  'CONTEXT_READY',
  'TASK_RESUMED',
  'PLANNING',
  'REASONING',
  'TOOL_EXECUTION',
  'TOOL_RESULT',
  'EXECUTION_GUARD',
  'WRITING_RESPONSE'
]);
const STREAM_PROGRESS_OUTCOMES = new Set<NonNullable<StreamProgress['outcome']>>([
  'USABLE',
  'PARTIAL',
  'FAILED',
  'RESULT_UNAVAILABLE',
  'CONFIRMATION_REQUIRED',
  'NO_PROGRESS',
  'EMERGENCY_LIMIT'
]);

const isRecord = (value: unknown): value is Record<string, unknown> =>
  Boolean(value) && typeof value === 'object' && !Array.isArray(value);

const isOptionalString = (value: unknown) =>
  value === undefined || value === null || typeof value === 'string';

const isOptionalNonNegativeInteger = (value: unknown) =>
  value === undefined || value === null
    || (Number.isSafeInteger(value) && Number(value) >= 0);

const TOOL_RESULT_OUTCOMES: ReadonlySet<NonNullable<StreamProgress['outcome']>> = new Set([
  'USABLE',
  'PARTIAL',
  'FAILED',
  'RESULT_UNAVAILABLE',
  'CONFIRMATION_REQUIRED'
]);
const EXECUTION_GUARD_OUTCOMES: ReadonlySet<NonNullable<StreamProgress['outcome']>> = new Set([
  'NO_PROGRESS',
  'EMERGENCY_LIMIT'
]);
const STREAM_REFRESH_TARGETS: ReadonlySet<string> = new Set([
  'device_list',
  'environment_list',
  'rule_list',
  'spec_list',
  'template_list',
  'run_history',
  'board_state'
]);

const isStreamProgress = (value: unknown): value is StreamProgress => {
  if (!isRecord(value)
      || typeof value.stage !== 'string'
      || !STREAM_PROGRESS_STAGES.has(value.stage as StreamProgress['stage'])
      || !isOptionalString(value.toolName)
      || !isOptionalString(value.detail)
      || !isOptionalNonNegativeInteger(value.round)
      || !isOptionalNonNegativeInteger(value.successfulSteps)
      || !isOptionalNonNegativeInteger(value.failedSteps)
      || !isOptionalNonNegativeInteger(value.unconfirmedSteps)) {
    return false;
  }
  const outcome = value.outcome;
  if (outcome !== undefined && outcome !== null
      && (typeof outcome !== 'string'
        || !STREAM_PROGRESS_OUTCOMES.has(outcome as NonNullable<StreamProgress['outcome']>))) {
    return false;
  }
  if (value.stage === 'TOOL_RESULT') {
    return typeof outcome === 'string'
      && TOOL_RESULT_OUTCOMES.has(outcome as NonNullable<StreamProgress['outcome']>);
  }
  if (value.stage === 'EXECUTION_GUARD') {
    return typeof outcome === 'string'
      && EXECUTION_GUARD_OUTCOMES.has(outcome as NonNullable<StreamProgress['outcome']>);
  }
  return outcome === undefined || outcome === null;
};

const hasCompletedToolEvidence = (trace: unknown): boolean => {
  if (!Array.isArray(trace) || trace.length === 0) return false;
  let hasUsableResult = false;
  for (const progress of trace) {
    if (!isStreamProgress(progress) || progress.stage === 'EXECUTION_GUARD') return false;
    if (progress.stage === 'TOOL_RESULT') {
      if (progress.outcome !== 'USABLE') return false;
      hasUsableResult = true;
    }
  }
  return hasUsableResult;
};

const validateStreamProgress = (value: unknown, context: string): StreamProgress => {
  if (!isStreamProgress(value)) throw new Error(`${context} is incomplete`);
  return value;
};

const validateStreamCommand = (value: unknown): StreamCommand => {
  if (!isRecord(value)
      || value.type !== 'REFRESH_DATA'
      || !isRecord(value.payload)
      || Object.keys(value.payload).length !== 1
      || typeof value.payload.target !== 'string'
      || !STREAM_REFRESH_TARGETS.has(value.payload.target)) {
    throw new Error('Chat stream command is incomplete');
  }
  return value as unknown as StreamCommand;
};

const validateChatHistoryMessages = (value: unknown, expectedSessionId: string): ChatMessage[] => {
  if (!Array.isArray(value)) throw new Error('Chat history messages are incomplete');
  value.forEach((candidate, index) => {
    if (!isRecord(candidate)
        || typeof candidate.role !== 'string'
        || !CHAT_ROLES.has(candidate.role as ChatMessage['role'])
        || typeof candidate.content !== 'string'
        || candidate.sessionId !== expectedSessionId
        || typeof candidate.turnId !== 'string'
        || !candidate.turnId.trim()
        || !isOptionalString(candidate.createdAt)
        || (candidate.id !== undefined && candidate.id !== null
          && (!Number.isSafeInteger(candidate.id) || Number(candidate.id) <= 0))
        || !isOptionalNonNegativeInteger(candidate.executionElapsedSeconds)
        || (candidate.executionTrace !== undefined && candidate.executionTrace !== null
          && (!Array.isArray(candidate.executionTrace)
            || candidate.executionTrace.some(progress => !isStreamProgress(progress))))) {
      throw new Error(`Chat history message ${index} is incomplete`);
    }
    const status = candidate.executionStatus;
    if (status !== undefined && status !== null
        && (typeof status !== 'string'
            || !CHAT_EXECUTION_STATUSES.has(status))) {
      throw new Error(`Chat history message ${index} has an unknown execution status`);
    }
    if (status === 'COMPLETED' && !hasCompletedToolEvidence(candidate.executionTrace)) {
      throw new Error(`Chat history message ${index} has unproven completed status`);
    }
  });
  return value as ChatMessage[];
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
  const raw = unpack<unknown>(response);
  const nextBeforeId = isRecord(raw) ? raw.nextBeforeId : undefined;
  if (!isRecord(raw) || !Array.isArray(raw.messages)
      || (nextBeforeId !== null
        && (typeof nextBeforeId !== 'number'
          || !Number.isSafeInteger(nextBeforeId)
          || nextBeforeId <= 0))
      || typeof raw.hasMore !== 'boolean'
      || (raw.hasMore && nextBeforeId === null)) {
    throw new Error('Chat history response is incomplete');
  }
  return {
    messages: validateChatHistoryMessages(raw.messages, sessionId),
    nextBeforeId: nextBeforeId as number | null,
    hasMore: raw.hasMore
  };
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
        const effectiveTurnId = turnId?.trim() || globalThis.crypto.randomUUID();

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
                turnId: effectiveTurnId,
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
            if (!trimmed) {
                throw new ChatStreamError('Invalid server stream frame', { kind: 'INVALID_FRAME' });
            }

            let json: unknown;
            try {
                json = JSON.parse(dataStr);
            } catch {
                throw new ChatStreamError('Invalid server stream frame', { kind: 'INVALID_FRAME' });
            }
            if (!isRecord(json)) {
                throw new ChatStreamError('Invalid server stream frame', { kind: 'INVALID_FRAME' });
            }

            const allowedKeys = new Set(['content', 'command', 'progress']);
            if (Object.keys(json).some(key => !allowedKeys.has(key))) {
                throw new ChatStreamError('Invalid server stream frame', { kind: 'INVALID_FRAME' });
            }
            if (json.content !== undefined && json.content !== null
                && typeof json.content !== 'string') {
                throw new ChatStreamError('Invalid server stream frame', { kind: 'INVALID_FRAME' });
            }

            const content = typeof json.content === 'string' ? json.content : '';
            let command: StreamCommand | undefined;
            let progress: StreamProgress | undefined;
            try {
                if (json.command !== undefined && json.command !== null) {
                    command = validateStreamCommand(json.command);
                }
                if (json.progress !== undefined && json.progress !== null) {
                    progress = validateStreamProgress(json.progress, 'Chat stream progress');
                }
            } catch {
                throw new ChatStreamError('Invalid server stream frame', { kind: 'INVALID_FRAME' });
            }

            if (!content && !command && !progress) {
                throw new ChatStreamError('Invalid server stream frame', { kind: 'INVALID_FRAME' });
            }
            const errorMessage = content ? serverErrorMessage(content) : '';
            if (errorMessage) {
                throw new ChatStreamError(errorMessage, { kind: 'SERVER_FRAME', serverFrame: true });
            }

            // Only semantically valid StreamResponseDto objects count as progress.
            hasReceivedFrame = true;
            if (command) callbacks.onCommand?.(command);
            if (progress) callbacks.onProgress?.(progress);
            if (content) callbacks.onMessage(content);
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

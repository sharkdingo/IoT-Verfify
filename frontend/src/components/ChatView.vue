<script setup lang="ts">
import { defineAsyncComponent, nextTick, onMounted, onUnmounted, ref, watch, computed } from 'vue';
import { useI18n } from 'vue-i18n';
import {
  AudioOutlined,
  CloseOutlined, DeleteOutlined,
  MessageOutlined, PlusOutlined, RobotOutlined, SendOutlined,
  UserOutlined, StopOutlined,
  MenuFoldOutlined, MenuUnfoldOutlined,
  CopyOutlined, ThunderboltOutlined, SafetyCertificateOutlined, CheckOutlined,
  CodeOutlined, ExperimentOutlined, DownOutlined
} from '@ant-design/icons-vue';

import 'element-plus/es/components/message/style/css';
import 'element-plus/es/components/message-box/style/css';

import type {
  ChatConfirmationAction,
  ChatConfirmationCommand,
  ChatConfirmationKind,
  ChatLogoutPreparation,
  ChatMessage,
  ChatHistoryPage,
  ChatSession,
  StreamCommand,
  StreamProgress,
  StreamTerminal
} from '@/types/chat';
import {
  ChatStreamError,
  createSession,
  deleteSession,
  getSessionActivity,
  getPendingConfirmation,
  getSessionHistory,
  getSessionList,
  hasCompletedToolEvidence,
  markSessionTerminalSeen,
  requestSessionStop,
  sendStreamChat
} from '@/api/chat';
import { useChatStore } from '@/stores/chat';
import { useAuth } from '@/stores/auth';
import { localizedTextOrFallback } from '@/utils/userMessage';
import { REQUEST_LIMITS } from '@/constants/requestLimits';
import { confirmDestructive, notifyBlocked, notifyError, notifyInfo, notifySuccess } from '@/utils/feedback'

type BoardChatContext = {
  deviceCount?: number;
  ruleCount?: number;
  specCount?: number;
  templateCount?: number;
  devices?: Array<{ label?: string; templateName?: string }>;
  rules?: Array<{ name?: string; description?: string }>;
  specs?: Array<{ name?: string; formulaPreview?: string }>;
  templates?: string[];
};

const props = withDefaults(defineProps<{
  boardMode?: boolean;
  getBoardContext?: () => BoardChatContext | null;
  interactionLocked?: boolean;
  prepareInteraction?: () => boolean;
  executeCommand?: (command: StreamCommand) => Promise<boolean>;
}>(), {
  boardMode: false,
  interactionLocked: false
});
const { t, locale } = useI18n();
const ChatMarkdown = defineAsyncComponent(() => import('@/components/ChatMarkdown.vue'));

// 使用全局状态
const chatStore = useChatStore();
const visible = computed(() => chatStore.state.visible);
const { state: authState } = useAuth();
const authenticatedUserId = computed(() => authState.user?.userId ?? null);
let chatAuthEpoch = 0;
let userSessionNavigationEpoch = 0;

/**
 * Legacy protocol residue, kept as a no-op safety net for persisted history.
 *
 * The backend no longer emits this prefix (nor the `CallEnd|>` marker stripped in `copyFullMessage`,
 * `applyHistoryPage`, and the chunk handler) — both strings have zero hits in `backend/src/main`.
 * Progress is a typed SSE frame now. Old rows in `chat_message` may still contain them, so the
 * stripping stays; do not add new callers, and drop all of it once history is known to be clean.
 */
const loadingRegex = /^(正在执行指令|Executing command)[.\s\n]*/;
const boardContext = ref<BoardChatContext | null>(null);

const refreshBoardContext = () => {
  boardContext.value = props.getBoardContext?.() ?? null;
};

const joinNames = (items: Array<string | undefined | null> | undefined, fallback: string, limit = 4) => {
  const names = Array.from(new Set(
      (items ?? [])
          .map(item => (item ?? '').trim())
          .filter(Boolean)
  )).slice(0, limit);
  return names.length > 0 ? names.join(t('app.chat.presetTasks.listSeparator')) : fallback;
};

const presetTasks = computed(() => [
  ...(props.boardMode && boardContext.value
      ? (() => {
        const ctx = boardContext.value!;
        const p = (key: string, args?: Record<string, unknown>) =>
          t(`app.chat.presetTasks.${key}`, args ?? {});
        const deviceCount = ctx.deviceCount ?? 0;
        const ruleCount = ctx.ruleCount ?? 0;
        const specCount = ctx.specCount ?? 0;
        const templateCount = ctx.templateCount ?? 0;
        const deviceNames = joinNames(
            ctx.devices?.map(device => device.label || device.templateName), p('fallback.devices'));
        const templateNames = joinNames(ctx.templates, p('fallback.templates'), 5);
        const ruleNames = joinNames(
            ctx.rules?.map(rule => rule.name || rule.description), p('fallback.rules'), 3);
        const specNames = joinNames(
            ctx.specs?.map(spec => spec.name || spec.formulaPreview), p('fallback.specs'), 3);

        if (deviceCount === 0) {
          return [
            {
              icon: ThunderboltOutlined,
              title: p('empty.fromTemplates.title'),
              desc: p('empty.fromTemplates.desc', { count: templateCount }),
              text: p('empty.fromTemplates.text', { templates: templateNames })
            },
            {
              icon: ExperimentOutlined,
              title: p('empty.starterDevices.title'),
              desc: p('empty.starterDevices.desc'),
              text: p('empty.starterDevices.text', { templates: templateNames })
            },
            {
              icon: SafetyCertificateOutlined,
              title: p('empty.planGoals.title'),
              desc: p('empty.planGoals.desc'),
              text: p('empty.planGoals.text')
            },
            {
              icon: CodeOutlined,
              title: p('empty.setupSteps.title'),
              desc: p('empty.setupSteps.desc'),
              text: p('empty.setupSteps.text')
            }
          ];
        }

        return [
          {
            icon: ThunderboltOutlined,
            title: ruleCount === 0 ? p('scene.addRules.title') : p('scene.reviewRules.title'),
            desc: p('scene.rulesDesc', { devices: deviceCount, rules: ruleCount }),
            text: ruleCount === 0
                ? p('scene.addRules.text', { devices: deviceNames })
                : p('scene.reviewRules.text', { rules: ruleNames, devices: deviceNames })
          },
          {
            icon: ExperimentOutlined,
            title: deviceCount < 5 ? p('scene.addDevices.title') : p('scene.refineDevices.title'),
            desc: p('scene.devicesDesc', { devices: deviceNames }),
            text: deviceCount < 5
                ? p('scene.addDevices.text', { devices: deviceNames })
                : p('scene.refineDevices.text', { devices: deviceNames })
          },
          {
            icon: SafetyCertificateOutlined,
            title: specCount === 0 ? p('scene.generateSpecs.title') : p('scene.reviewSpecs.title'),
            desc: p('scene.specsDesc', { count: specCount }),
            text: specCount === 0
                ? p('scene.generateSpecs.text', { devices: deviceNames, rules: ruleCount })
                : p('scene.reviewSpecs.text', { specs: specNames })
          },
          {
            icon: CodeOutlined,
            title: p('scene.violationTest.title'),
            desc: p('scene.violationTest.desc'),
            text: p('scene.violationTest.text',
                { devices: deviceCount, rules: ruleCount, specs: specCount })
          }
        ];
      })()
      : [
        {
          icon: ThunderboltOutlined,
          title: t('app.chat.presetTasks.quickDevice.title'),
          desc: t('app.chat.presetTasks.quickDevice.desc'),
          text: t('app.chat.presetTasks.quickDevice.text')
        },
        {
          icon: SafetyCertificateOutlined,
          title: t('app.chat.presetTasks.verification.title'),
          desc: t('app.chat.presetTasks.verification.desc'),
          text: t('app.chat.presetTasks.verification.text')
        },
        {
          icon: ExperimentOutlined,
          title: t('app.chat.presetTasks.scenario.title'),
          desc: t('app.chat.presetTasks.scenario.desc'),
          text: t('app.chat.presetTasks.scenario.text')
        },
        {
          icon: CodeOutlined,
          title: t('app.chat.presetTasks.script.title'),
          desc: t('app.chat.presetTasks.script.desc'),
          text: t('app.chat.presetTasks.script.text')
        }
      ])
]);

// State - 使用全局状态，不重复定义
const isSidebarOpen = ref(false);
const isRecording = ref(false);
const sessions = ref<ChatSession[]>([]);
const terminalSeenRequests = new Map<string, number>();
const isLoadingSessions = ref(false);
const sessionListLoadFailed = ref(false);
const isCreatingSession = ref(false);
const isPreparingStreamSession = ref(false);
const currentSessionId = ref<string>('');
const messages = ref<ChatMessage[]>([]);
const pendingConfirmationKinds = ref<ChatConfirmationKind[]>([]);
const pendingConfirmationLoadFailed = ref(false);
const inputValue = ref('');
const isStreaming = ref(false);
const isSettlingStream = ref(false);
const isMonitoringRemoteExecution = ref(false);
const remoteActivityCheckFailed = ref(false);
const streamProgress = ref<StreamProgress | null>(null);
const streamProgressEvents = ref<StreamProgress[]>([]);
const streamElapsedSeconds = ref(0);
let streamElapsedTimer: ReturnType<typeof setInterval> | null = null;
let confirmationRequestEpoch = 0;
const reconciliationRequired = computed({
  get: () => chatStore.state.reconciliationRequired,
  set: (required: boolean) => chatStore.setReconciliationRequired(required)
});
const isRetryingReconciliation = ref(false);
const activeStreamSessionId = ref('');
const activeStreamTurnId = ref('');
const scopedAuthToken = ref<string | null>(authState.token);
let scopedAuthUserId = authenticatedUserId.value;
const activeStreamAuthToken = ref<string | null>(null);
const historyReplacementWithoutTerminalAllowed = ref(false);
const explicitStopRegistrationPending = ref(false);
const activeStreamRetryDraft = ref('');
const isLoadingHistory = ref(false);
const historyLoadFailed = ref(false);
const isLoadingOlderHistory = ref(false);
const historyHasMore = ref(false);
const historyNextBeforeId = ref<number | null>(null);
const hasAuthoritativeActiveSession = computed(() =>
    sessions.value.some(session => session.active));
const hasCurrentAuthoritativeActiveSession = computed(() =>
    Boolean(currentSessionId.value)
    && sessions.value.some(session => session.id === currentSessionId.value && session.active));
const isAssistantBusy = computed(() =>
    isStreaming.value || isSettlingStream.value || isMonitoringRemoteExecution.value
    || reconciliationRequired.value || hasCurrentAuthoritativeActiveSession.value);
const hasAnyAssistantWork = computed(() =>
    isStreaming.value || isSettlingStream.value || reconciliationRequired.value
    || hasAuthoritativeActiveSession.value || chatStore.state.activeCount > 0);
const isLoading = computed(() => isAssistantBusy.value || isLoadingHistory.value);
const TOOL_LABEL_KEYS: Record<string, string> = {
  edit_device: 'app.chat.toolLabels.editDevice',
  apply_fix: 'app.chat.toolLabels.applyFix',
  delete_verification_run: 'app.chat.toolLabels.deleteVerificationRun',
  dismiss_verify_task: 'app.chat.toolLabels.dismissVerifyTask',
  dismiss_simulate_task: 'app.chat.toolLabels.dismissSimulateTask',
  fuzz_model_async: 'app.chat.toolLabels.fuzzModelAsync',
  fuzz_task_status: 'app.chat.toolLabels.fuzzTaskStatus',
  cancel_fuzz_task: 'app.chat.toolLabels.cancelFuzzTask',
  list_fuzz_runs: 'app.chat.toolLabels.listFuzzRuns',
  get_fuzz_run: 'app.chat.toolLabels.getFuzzRun',
  get_fuzz_finding: 'app.chat.toolLabels.getFuzzFinding',
  delete_fuzz_run: 'app.chat.toolLabels.deleteFuzzRun',
  dismiss_fuzz_task: 'app.chat.toolLabels.dismissFuzzTask',
  add_device: 'app.chat.toolLabels.addDevice',
  delete_device: 'app.chat.toolLabels.deleteDevice',
  search_devices: 'app.chat.toolLabels.searchDevices',
  recommend_related_devices: 'app.chat.toolLabels.recommendRelatedDevices',
  manage_environment: 'app.chat.toolLabels.manageEnvironment',
  list_rules: 'app.chat.toolLabels.listRules',
  manage_rule: 'app.chat.toolLabels.manageRule',
  check_duplicate_rule: 'app.chat.toolLabels.checkDuplicateRule',
  check_rule_similarity: 'app.chat.toolLabels.checkRuleSimilarity',
  recommend_rules: 'app.chat.toolLabels.recommendRules',
  list_specs: 'app.chat.toolLabels.listSpecs',
  manage_spec: 'app.chat.toolLabels.manageSpec',
  recommend_specifications: 'app.chat.toolLabels.recommendSpecifications',
  recommend_scenario: 'app.chat.toolLabels.recommendScenario',
  apply_scenario: 'app.chat.toolLabels.applyScenario',
  list_templates: 'app.chat.toolLabels.listTemplates',
  add_template: 'app.chat.toolLabels.addTemplate',
  delete_template: 'app.chat.toolLabels.deleteTemplate',
  reset_default_templates: 'app.chat.toolLabels.resetDefaultTemplates',
  verify_model: 'app.chat.toolLabels.verifyModel',
  verify_model_async: 'app.chat.toolLabels.verifyModelAsync',
  verify_task_status: 'app.chat.toolLabels.verifyTaskStatus',
  cancel_verify_task: 'app.chat.toolLabels.cancelVerifyTask',
  list_traces: 'app.chat.toolLabels.listTraces',
  get_trace: 'app.chat.toolLabels.getTrace',
  delete_trace: 'app.chat.toolLabels.deleteTrace',
  fix_violation: 'app.chat.toolLabels.fixViolation',
  simulate_model: 'app.chat.toolLabels.simulateModel',
  simulate_model_async: 'app.chat.toolLabels.simulateModelAsync',
  simulate_task_status: 'app.chat.toolLabels.simulateTaskStatus',
  cancel_simulate_task: 'app.chat.toolLabels.cancelSimulateTask',
  list_simulation_traces: 'app.chat.toolLabels.listSimulationTraces',
  get_simulation_trace: 'app.chat.toolLabels.getSimulationTrace',
  delete_simulation_trace: 'app.chat.toolLabels.deleteSimulationTrace',
  list_async_tasks: 'app.chat.toolLabels.listAsyncTasks',
  list_verification_runs: 'app.chat.toolLabels.listVerificationRuns',
  get_verification_run: 'app.chat.toolLabels.getVerificationRun',
  manage_board_history: 'app.chat.toolLabels.manageBoardHistory',
  clear_board: 'app.chat.toolLabels.clearBoard',
  board_overview: 'app.chat.toolLabels.boardOverview'
};
const readableToolName = (progress: StreamProgress) => {
  const toolName = progress.toolName || '';
  const translationKey = TOOL_LABEL_KEYS[toolName];
  return translationKey ? t(translationKey) : (toolName || t('app.chat.progressUnknownTool')).replace(/_/g, ' ');
};
const progressEventTitle = (progress: StreamProgress) => {
  if (progress.stage === 'CONTEXT_READY') return t('app.chat.progressContextTitle');
  if (progress.stage === 'TASK_RESUMED') return t('app.chat.progressTaskResumedTitle');
  if (progress.stage === 'PLANNING') return t('app.chat.progressPlanningTitle');
  if (progress.stage === 'REASONING') return t('app.chat.progressReasoningTitle');
  if (progress.stage === 'TOOL_EXECUTION' || progress.stage === 'TOOL_RESULT') {
    return readableToolName(progress);
  }
  if (progress.stage === 'EXECUTION_GUARD') {
    return progress.outcome === 'NO_PROGRESS'
        ? t('app.chat.progressNoProgressTitle')
        : t('app.chat.progressEmergencyTitle');
  }
  return t('app.chat.progressWritingTitle');
};
const progressEventDetail = (progress: StreamProgress) => {
  const round = progress.round || 1;
  if (progress.stage === 'CONTEXT_READY') return t('app.chat.progressContextDetail');
  if (progress.stage === 'TASK_RESUMED') {
    return t('app.chat.progressTaskResumedDetail', {
      objective: progress.detail || t('app.chat.progressTaskResumedFallback')
    });
  }
  if (progress.stage === 'PLANNING') {
    return t('app.chat.progressPlanningDetail', { round });
  }
  if (progress.stage === 'REASONING') {
    // An empty detail means the model returned no summary this round. Say that, rather than
    // describing reasoning that did not happen — a canned "summarizing the goal…" line renamed
    // the absence of reasoning as reasoning.
    return progress.detail || t('app.chat.progressReasoningFallback');
  }
  if (progress.stage === 'TOOL_EXECUTION') {
    return t('app.chat.progressToolStartedDetail', {
      round,
      tool: progress.toolName || t('app.chat.progressUnknownTool')
    });
  }
  if (progress.stage === 'TOOL_RESULT') {
    if (progress.detail) return progress.detail;
    if (progress.outcome === 'FAILED') return t('app.chat.progressToolFailedDetail', { round });
    if (progress.outcome === 'PARTIAL') return t('app.chat.progressToolPartialDetail', { round });
    if (progress.outcome === 'RESULT_UNAVAILABLE') return t('app.chat.progressToolUnconfirmedDetail', { round });
    if (progress.outcome === 'CONFIRMATION_REQUIRED') return t('app.chat.progressToolNeedsConfirmationDetail', { round });
    return t('app.chat.progressToolSucceededDetail', { round });
  }
  if (progress.stage === 'EXECUTION_GUARD') {
    return progress.outcome === 'NO_PROGRESS'
        ? t('app.chat.progressNoProgressDetail')
        : t('app.chat.progressEmergencyDetail');
  }
  return t('app.chat.progressWritingDetail');
};
const progressEventStatus = (progress: StreamProgress) => {
  if (progress.stage === 'TOOL_EXECUTION') return t('app.chat.progressStatusStarted');
  if (progress.stage === 'TOOL_RESULT') {
    if (progress.outcome === 'FAILED') return t('app.chat.progressStatusFailed');
    if (progress.outcome === 'PARTIAL') return t('app.chat.progressStatusPartial');
    if (progress.outcome === 'RESULT_UNAVAILABLE') return t('app.chat.progressStatusUnconfirmed');
    if (progress.outcome === 'CONFIRMATION_REQUIRED') return t('app.chat.progressStatusConfirmation');
    return t('app.chat.progressStatusSucceeded');
  }
  if (progress.stage === 'TASK_RESUMED') return t('app.chat.progressStatusResumed');
  return null;
};
const executionTraceTotals = (trace: StreamProgress[]) => {
  const latest = [...trace].reverse().find(progress =>
      progress.successfulSteps != null
      || progress.failedSteps != null
      || progress.unconfirmedSteps != null);
  return {
    successful: latest?.successfulSteps ?? trace.filter(progress =>
        progress.stage === 'TOOL_RESULT' && progress.outcome === 'USABLE').length,
    failed: latest?.failedSteps ?? trace.filter(progress =>
        progress.stage === 'TOOL_RESULT' && progress.outcome === 'FAILED').length,
    unconfirmed: latest?.unconfirmedSteps ?? trace.filter(progress =>
        progress.stage === 'TOOL_RESULT'
        && (progress.outcome === 'RESULT_UNAVAILABLE'
            || progress.outcome === 'CONFIRMATION_REQUIRED')).length
  };
};
const traceHasToolResults = (trace: StreamProgress[]) =>
    trace.some(progress => progress.stage === 'TOOL_RESULT');
const traceHasToolActivity = (trace: StreamProgress[]) =>
    trace.some(progress => progress.stage === 'TOOL_EXECUTION' || progress.stage === 'TOOL_RESULT');
const executionTraceStatus = (
    trace: StreamProgress[],
    active: boolean,
    status?: ChatMessage['executionStatus'],
    settling = false
) => {
  if (active) return t('app.chat.executionTraceRunning');
  if (settling) return t('app.chat.executionTraceSettling');
  if (status === 'AWAITING_CONFIRMATION') {
    return executionTraceTotals(trace).successful > 0
        ? t('app.chat.executionTracePartialAwaitingConfirmation')
        : t('app.chat.executionTraceAwaitingConfirmation');
  }
  if (status === 'STOPPED') return t('app.chat.executionTraceStopped');
  if (status === 'DISCONNECTED') return t('app.chat.executionTraceDisconnected');
  const guard = [...trace].reverse().find(progress => progress.stage === 'EXECUTION_GUARD');
  if (guard) {
    return guard.outcome === 'NO_PROGRESS'
      ? t('app.chat.executionTraceStoppedNoProgress')
      : t('app.chat.executionTraceStoppedLimit');
  }
  if (status === 'PARTIAL') {
    return trace.length > 0 && !traceHasToolActivity(trace)
      ? t('app.chat.executionTraceNoTool')
      : t('app.chat.executionTracePartial');
  }
  if (status === 'FAILED') return t('app.chat.executionTraceFailed');
  if (status !== 'COMPLETED' || !hasCompletedToolEvidence(trace)) {
    return t('app.chat.executionTraceUnverified');
  }
  const lastResult = [...trace].reverse().find(progress => progress.stage === 'TOOL_RESULT');
  return lastResult?.outcome === 'CONFIRMATION_REQUIRED'
      ? t('app.chat.executionTraceWaiting')
      : t('app.chat.executionTraceCompleted');
};
const sessionExecutionStatus = (session: ChatSession) => {
  if (session.active) return t('app.chat.sessionActive');
  switch (session.latestExecutionStatus) {
    case 'COMPLETED': return t('app.chat.executionTraceCompleted');
    case 'AWAITING_CONFIRMATION': return t('app.chat.executionTraceAwaitingConfirmation');
    case 'PARTIAL': return t('app.chat.executionTracePartial');
    case 'STOPPED': return t('app.chat.executionTraceStopped');
    case 'DISCONNECTED': return t('app.chat.executionTraceDisconnected');
    case 'FAILED': return t('app.chat.executionTraceFailed');
    default: return '';
  }
};
const sessionStatusClass = (session: ChatSession) => ({
  'is-running': session.active,
  'is-unread': session.hasUnreadUpdate,
  'is-failed': !session.active && session.latestExecutionStatus === 'FAILED',
  'is-warning': !session.active && (session.latestExecutionStatus === 'PARTIAL'
    || session.latestExecutionStatus === 'STOPPED'
    || session.latestExecutionStatus === 'DISCONNECTED'
    || session.latestExecutionStatus === 'AWAITING_CONFIRMATION')
});
const sessionStatusTitle = (session: ChatSession) => session.hasUnreadUpdate
    ? t('app.chat.sessionUnreadUpdate', { status: sessionExecutionStatus(session) })
    : sessionExecutionStatus(session);
const progressEventClass = (progress: StreamProgress, active: boolean) => ({
  'is-success': progress.stage === 'TOOL_RESULT' && progress.outcome === 'USABLE',
  'is-warning': progress.stage === 'EXECUTION_GUARD'
      || progress.outcome === 'PARTIAL'
      || progress.outcome === 'RESULT_UNAVAILABLE'
      || progress.outcome === 'CONFIRMATION_REQUIRED',
  'is-error': progress.stage === 'TOOL_RESULT' && progress.outcome === 'FAILED',
  'is-reasoning': progress.stage === 'REASONING',
  'is-current': active && progress === streamProgressEvents.value[streamProgressEvents.value.length - 1]
});
const isCurrentProgressEvent = (progress: StreamProgress, active: boolean) =>
    active && progress === streamProgressEvents.value[streamProgressEvents.value.length - 1];
const appendStreamProgress = (progress: StreamProgress) => {
  streamProgress.value = progress;
  const previous = streamProgressEvents.value[streamProgressEvents.value.length - 1];
  if (previous
      && previous.stage === progress.stage
      && (previous.toolName ?? null) === (progress.toolName ?? null)
      && (previous.round ?? null) === (progress.round ?? null)
      && (previous.outcome ?? null) === (progress.outcome ?? null)
      && (previous.successfulSteps ?? null) === (progress.successfulSteps ?? null)
      && (previous.failedSteps ?? null) === (progress.failedSteps ?? null)
      && (previous.unconfirmedSteps ?? null) === (progress.unconfirmedSteps ?? null)
      && (previous.detail ?? null) === (progress.detail ?? null)) {
    return;
  }
  streamProgressEvents.value.push({ ...progress });
  nextTick(() => {
    const activeTrace = chatPanelRef.value?.querySelector<HTMLElement>(
        '[data-testid="chat-assistant-pending"] .chat-execution-events');
    if (activeTrace) activeTrace.scrollTop = activeTrace.scrollHeight;
    scrollToBottom(false);
  });
};
const isActiveAssistantMessage = (index: number) =>
    isStreaming.value && index === messages.value.length - 1;
const isSettlingAssistantMessage = (index: number) =>
    isSettlingStream.value
    && Boolean(activeStreamSessionId.value)
    && activeStreamSessionId.value === currentSessionId.value
    && index === messages.value.length - 1;
const messageExecutionTrace = (message: ChatMessage, index: number) =>
    isActiveAssistantMessage(index) ? streamProgressEvents.value : (message.executionTrace ?? []);
const messageExecutionElapsed = (message: ChatMessage, index: number) =>
    isActiveAssistantMessage(index) ? streamElapsedSeconds.value : (message.executionElapsedSeconds ?? 0);
/**
 * Turns whose reasoning panel the user collapsed by hand, keyed by `turnId`.
 *
 * Reasoning used to shut the instant the turn ended, so anyone who was not watching the stream
 * never read it. The newest turn now stays open once it completes — but a deliberate collapse is
 * remembered, because re-expanding what the user just closed is worse than hiding it.
 */
const collapsedExecutionTraces = ref(new Set<string>());

/**
 * Identity a collapse is remembered under.
 *
 * `turnId` is optional on `ChatMessage`, and a row without one could record no collapse at all — so
 * `:open` re-expanded the panel on the next render, discarding the user's deliberate close. Only the
 * last message can be collapsed here, so its index is a stable enough fallback key.
 */
const executionTraceKey = (msg: ChatMessage, index: number) => msg.turnId ?? `index:${index}`;

const isExecutionTraceOpen = (msg: ChatMessage, index: number) => {
  if (isActiveAssistantMessage(index)) return true;
  if (index !== messages.value.length - 1) return false;
  return !collapsedExecutionTraces.value.has(executionTraceKey(msg, index));
};

const handleExecutionTraceToggle = (event: Event, active: boolean, msg?: ChatMessage, index?: number) => {
  const target = event.currentTarget as HTMLDetailsElement | null;
  if (msg && typeof index === 'number' && !active) {
    const key = executionTraceKey(msg, index);
    const collapsed = new Set(collapsedExecutionTraces.value);
    if (target?.open) collapsed.delete(key);
    else collapsed.add(key);
    collapsedExecutionTraces.value = collapsed;
  }
  return handleExecutionTraceScroll(event, active);
};

const handleExecutionTraceScroll = (event: Event, active: boolean) => {
  const details = event.currentTarget as HTMLDetailsElement | null;
  if (!details?.open || active) return;
  nextTick(() => {
    const events = details.querySelector<HTMLElement>('.chat-execution-events');
    if (events) events.scrollTop = 0;
  });
};
watch(hasAnyAssistantWork, busy => chatStore.setStreaming(busy), { immediate: true });
const scrollRef = ref<HTMLElement | null>(null);
const chatPanelRef = ref<HTMLElement | null>(null);
const abortController = ref<AbortController | null>(null);
const historyAbortController = ref<AbortController | null>(null);
let streamRequestEpoch = 0;
let historyRequestEpoch = 0;
let sessionListRequestEpoch = 0;
let settlementPromise: Promise<ChatLogoutPreparation> | null = null;
let settlementAbortController: AbortController | null = null;
let settlementDetachedTransport: AbortController | null = null;
let reconciliationPromise: Promise<boolean> | null = null;
let activityMonitorEpoch = 0;
let activityMonitorAbortController: AbortController | null = null;
let activeSessionsMonitorEpoch = 0;
let activeSessionsPollTimer: ReturnType<typeof setTimeout> | null = null;
let activeSessionsPollInFlight = false;
let chatViewMounted = false;
let sessionCompletionObservationsInitialized = false;
const chatPosition = ref<{ left: number; top: number; width: number; height: number } | null>(null);
const panelInteraction = ref<{
  mode: 'drag' | 'resize';
  pointerId: number;
  target: HTMLElement;
  startX: number;
  startY: number;
  left: number;
  top: number;
  width: number;
  height: number;
} | null>(null);

const CHAT_MIN_WIDTH = 320;
const CHAT_MIN_HEIGHT = 360;
const CHAT_ABSOLUTE_MIN_HEIGHT = 260;
const CHAT_DEFAULT_WIDTH = 760;
const CHAT_DEFAULT_HEIGHT = 640;
const CHAT_DEFAULT_VERTICAL_SLACK = 96;
const CHAT_COMPACT_WIDTH = 960;

const isCompactChatWidth = (width: number) => width < CHAT_COMPACT_WIDTH;

const canAdjustChatPanel = () => typeof window !== 'undefined' && window.innerWidth > 720;

const getChatMinimumHeight = (availableHeight: number) => Math.min(
    CHAT_MIN_HEIGHT,
    Math.max(CHAT_ABSOLUTE_MIN_HEIGHT, availableHeight - CHAT_DEFAULT_VERTICAL_SLACK * 2)
);

const getChatViewportInsets = () => {
  const boardToolRail = props.boardMode && window.innerWidth < 1280 ? 128 : 12;
  return {
    left: 12,
    right: boardToolRail,
    top: props.boardMode ? 76 : 12,
    bottom: 12
  };
};

const clampChatGeometry = (left: number, top: number, width: number, height: number) => {
  const insets = getChatViewportInsets();
  const availableWidth = Math.max(240, window.innerWidth - insets.left - insets.right);
  const availableHeight = Math.max(260, window.innerHeight - insets.top - insets.bottom);
  const minWidth = Math.min(CHAT_MIN_WIDTH, availableWidth);
  const minHeight = Math.min(getChatMinimumHeight(availableHeight), availableHeight);
  const nextWidth = Math.min(Math.max(width, minWidth), availableWidth);
  const nextHeight = Math.min(Math.max(height, minHeight), availableHeight);
  const minLeft = insets.left;
  const maxLeft = Math.max(minLeft, window.innerWidth - insets.right - nextWidth);
  const minTop = insets.top;
  const maxTop = Math.max(minTop, window.innerHeight - insets.bottom - nextHeight);
  return {
    left: Math.min(Math.max(minLeft, left), maxLeft),
    top: Math.min(Math.max(minTop, top), maxTop),
    width: nextWidth,
    height: nextHeight
  };
};

const createDefaultChatGeometry = () => {
  const insets = getChatViewportInsets();
  const availableWidth = Math.max(240, window.innerWidth - insets.left - insets.right);
  const availableHeight = Math.max(260, window.innerHeight - insets.top - insets.bottom);
  const width = Math.min(CHAT_DEFAULT_WIDTH, availableWidth);
  // A floating window needs visible room to move and grow. Taking every available vertical pixel
  // at common 720px desktop heights made a draggable/resizable panel appear inert.
  const height = Math.min(
      CHAT_DEFAULT_HEIGHT,
      Math.max(getChatMinimumHeight(availableHeight), availableHeight - CHAT_DEFAULT_VERTICAL_SLACK)
  );
  const left = Math.max(insets.left, window.innerWidth - insets.right - width);
  const top = Math.max(insets.top, insets.top + 12);
  return clampChatGeometry(left, top, width, height);
};

const chatPanelStyle = computed<Record<string, string>>(() => {
  const position = chatPosition.value;
  if (typeof window !== 'undefined' && window.innerWidth <= 720) return {} as Record<string, string>;
  if (!position) return {} as Record<string, string>;
  return {
    left: `${position.left}px`,
    top: `${position.top}px`,
    right: 'auto',
    bottom: 'auto',
    width: `${position.width}px`,
    height: `${position.height}px`
  };
});

const isChatPanelCompact = computed(() => {
  if (typeof window === 'undefined') return false;
  const width = chatPosition.value?.width ?? window.innerWidth;
  return isCompactChatWidth(width);
});

watch(isChatPanelCompact, (compact, wasCompact) => {
  if (compact && !wasCompact) {
    isSidebarOpen.value = false;
  }
});

const removePanelInteractionListeners = () => {
  window.removeEventListener('pointermove', onPanelInteractionMove);
  window.removeEventListener('pointerup', stopPanelInteraction);
  window.removeEventListener('pointercancel', stopPanelInteraction);
};

const stopPanelInteraction = (event?: PointerEvent) => {
  const state = panelInteraction.value;
  if (state && event?.pointerId !== undefined && event.pointerId !== state.pointerId) return;

  panelInteraction.value = null;
  removePanelInteractionListeners();
  if (!state) return;

  state.target.removeEventListener('lostpointercapture', onPanelLostPointerCapture);
  try {
    state.target.releasePointerCapture?.(state.pointerId);
  } catch {
    // The browser may already have released capture while the window was resizing or losing focus.
  }
};

const onPanelLostPointerCapture = (event: PointerEvent) => {
  stopPanelInteraction(event);
};

const onPanelInteractionMove = (event: PointerEvent) => {
  const state = panelInteraction.value;
  if (!state || event.pointerId !== state.pointerId) return;
  if (event.pointerType === 'mouse' && event.buttons === 0) {
    stopPanelInteraction(event);
    return;
  }

  if (state.mode === 'drag') {
    chatPosition.value = clampChatGeometry(
        state.left + event.clientX - state.startX,
        state.top + event.clientY - state.startY,
        state.width,
        state.height
    );
    return;
  }

  const insets = getChatViewportInsets();
  const maxWidth = window.innerWidth - insets.right - state.left;
  const maxHeight = window.innerHeight - insets.bottom - state.top;
  chatPosition.value = clampChatGeometry(
      state.left,
      state.top,
      Math.min(state.width + event.clientX - state.startX, maxWidth),
      Math.min(state.height + event.clientY - state.startY, maxHeight)
  );
};

const startPanelInteraction = (event: PointerEvent, mode: 'drag' | 'resize') => {
  if (event.button !== 0 || event.isPrimary === false || !canAdjustChatPanel()
      || panelInteraction.value) return;
  const panel = chatPanelRef.value;
  if (!panel) return;

  event.preventDefault();
  const target = event.currentTarget as HTMLElement;
  const rect = panel.getBoundingClientRect();
  const geometry = clampChatGeometry(rect.left, rect.top, rect.width, rect.height);
  chatPosition.value = geometry;
  panelInteraction.value = {
    mode,
    pointerId: event.pointerId,
    target,
    startX: event.clientX,
    startY: event.clientY,
    left: geometry.left,
    top: geometry.top,
    width: geometry.width,
    height: geometry.height
  };

  try {
    target.setPointerCapture?.(event.pointerId);
  } catch {
    // Pointer capture is optional; window listeners retain the fallback path.
  }
  target.addEventListener('lostpointercapture', onPanelLostPointerCapture);
  window.addEventListener('pointermove', onPanelInteractionMove);
  window.addEventListener('pointerup', stopPanelInteraction);
  window.addEventListener('pointercancel', stopPanelInteraction);
};

const startPanelDrag = (event: PointerEvent) => {
  const target = event.target as HTMLElement | null;
  if (target?.closest('button, a, input, textarea, select, [role="button"], .chat-resize-handle')) return;
  startPanelInteraction(event, 'drag');
};

const startPanelResize = (event: PointerEvent) => {
  event.stopPropagation();
  startPanelInteraction(event, 'resize');
};

const clampExistingChatPosition = () => {
  const position = chatPosition.value;
  chatPosition.value = position
      ? clampChatGeometry(position.left, position.top, position.width, position.height)
      : createDefaultChatGeometry();
  if (isCompactChatWidth(chatPosition.value.width)) {
    isSidebarOpen.value = false;
  }
};

const handleChatViewportResize = () => {
  stopPanelInteraction();
  clampExistingChatPosition();
};

const handlePanelWindowBlur = () => stopPanelInteraction();

// ================= 文本处理辅助函数 =================

const convertLatexDelimiters = (text: string) => {
  const pattern = /(```[\S\s]*?```|`.*?`)|\\\[([\S\s]*?[^\\])\\]|\\\((.*?)\\\)/g;
  return text.replace(pattern, (match, codeBlock, squareBracket, roundBracket) => {
    if (codeBlock !== undefined) return codeBlock;
    if (squareBracket !== undefined) return `$$${squareBracket}$$`;
    if (roundBracket !== undefined) return `$${roundBracket}$`;
    return match;
  });
};

const getRawContentWithoutThinking = (content: string) => {
  if (!content) return '';
  const match = content.match(loadingRegex);
  if (match) {
    const prefixLength = match[0].length;
    // 如果只有提示语，为了避免空内容，暂时返回提示语（或可返回空字符串让界面显示 Loading）
    if (content.length <= prefixLength) return content;
    return content.substring(prefixLength);
  }
  return content;
};

/**
 * 最终渲染内容的预处理
 */
const getProcessedContent = (content: string) => {
  if (!content) return '';
  // 1. 去除 Thinking 前缀
  let text = getRawContentWithoutThinking(content);
  // 2. 标准化 LaTeX
  return convertLatexDelimiters(text);
};

const copyFullMessage = async (content: string) => {
  try {
    const cleanContent = content.replace('CallEnd|>', '');
    await navigator.clipboard.writeText(cleanContent);
    notifySuccess(t('app.chat.copied'));
  } catch (err) {
    notifyError(t('app.chat.copyFailed'));
  }
};

// ================= 交互逻辑 =================

const formatStreamError = (error: unknown) => {
  if (error instanceof ChatStreamError) {
    switch (error.kind) {
      case 'MISSING_BODY':
        return t('app.chat.missingResponseBody');
      case 'INCOMPLETE_STREAM':
        return t('app.chat.incompleteResponseStream');
      case 'INVALID_FRAME':
        return t('app.chat.invalidResponseStream');
      case 'HTTP_ERROR':
        if (error.status === 403) return t('app.chat.authorizationFailed');
        if (error.status === 401) return t('app.chat.authenticationExpired');
        if (error.reasonCode === 'CHAT_HISTORY_LIMIT_REACHED') {
          return t('app.chat.historyLimitReached');
        }
        if (error.reasonCode === 'USER_CHAT_OPERATION_BUSY') {
          return Number.isSafeInteger(error.limit) && (error.limit ?? 0) > 0
              ? t('app.chat.assistantOperationBusy', { limit: error.limit })
              : t('app.chat.assistantOperationBusyUnknown');
        }
        if (error.status === 429) return t('app.chat.assistantOperationBusyUnknown');
        return t('app.chat.httpRequestFailed', { status: error.status ?? '?' });
      case 'SERVER_FRAME':
        return localizedTextOrFallback(error.message, t('app.chat.serverStreamError'), locale.value);
      default:
        break;
    }
  }
  if (error instanceof TypeError) return t('app.chat.networkError');
  const message = error instanceof Error ? error.message : String(error || '');
  return localizedTextOrFallback(message, t('app.chat.requestFailed'), locale.value);
};

/**
 * The live recognizer, held so teardown can stop it.
 *
 * A function-local instance keeps the microphone open and keeps writing into `inputValue` after the
 * component is gone (logout, or navigating off the board), because nothing can reach it to abort.
 */
let activeRecognition: any = null;

const stopListening = () => {
  if (!activeRecognition) return;
  const recognition = activeRecognition;
  activeRecognition = null;
  // `abort` discards pending results rather than delivering them into a torn-down component; only
  // fall back to `stop` when the engine has no `abort`. Chaining these with `??` ran both, because
  // `abort()` returns undefined.
  try {
    if (typeof recognition.abort === 'function') recognition.abort();
    else recognition.stop?.();
  } catch { /* already ended */ }
  isRecording.value = false;
};

const startListening = () => {
  const SpeechRecognition = (window as any).SpeechRecognition || (window as any).webkitSpeechRecognition;
  if (!SpeechRecognition) {
    notifyBlocked(t('app.chat.speechUnsupported'));
    return;
  }
  if (isRecording.value) return;

  try {
    const recognition = new SpeechRecognition();
    recognition.lang = locale.value === 'zh-CN' ? 'zh-CN' : 'en-US';
    recognition.interimResults = false;
    recognition.maxAlternatives = 1;

    recognition.onstart = () => { isRecording.value = true; notifyInfo(t('app.chat.startSpeaking')); };
    recognition.onend = () => { activeRecognition = null; isRecording.value = false; };
    recognition.onerror = () => {
      activeRecognition = null;
      isRecording.value = false;
      notifyError(t('app.chat.speechError'));
    };
    recognition.onresult = (event: any) => {
      // A result that arrives after teardown has no field to write into.
      if (activeRecognition !== recognition) return;
      const transcript = event.results[0][0].transcript;
      if (transcript) inputValue.value += transcript;
    };
    activeRecognition = recognition;
    recognition.start();
  } catch (e) {
    activeRecognition = null;
    notifyError(t('app.chat.speechStartFailed'));
    isRecording.value = false;
  }
};



// 监听 visible 变化，执行相应逻辑
watch(visible, (newVal) => {
  if (!newVal) {
    stopPanelInteraction();
    return;
  }
  void initSessions().then(() => nextTick(() => acknowledgeCurrentVisibleHistory()));
  refreshBoardContext();
  const nextGeometry = chatPosition.value
      ? clampChatGeometry(
          chatPosition.value.left,
          chatPosition.value.top,
          chatPosition.value.width,
          chatPosition.value.height
      )
      : createDefaultChatGeometry();
  chatPosition.value = nextGeometry;
  isSidebarOpen.value = !props.boardMode && !isCompactChatWidth(nextGeometry.width) && window.innerWidth >= 1120;
  nextTick(clampExistingChatPosition);
});

watch(sessions, currentSessions => {
  chatStore.setActiveCount(currentSessions.filter(session => session.active).length);
  chatStore.setUnreadCount(currentSessions.filter(session => session.hasUnreadUpdate).length);
}, { deep: true });

const invokeSystemCommand = async (command: StreamCommand): Promise<boolean> => {
  if (!props.executeCommand) {
    console.warn('[Chat] No system-command executor is available');
    return false;
  }
  try {
    return await props.executeCommand(command);
  } catch (error) {
    console.error('[Chat] System command failed:', error);
    return false;
  }
};

const markReconciliationRequired = () => {
  if (!reconciliationRequired.value) {
    notifyError(t('app.chat.reconciliationFailed'));
  }
  reconciliationRequired.value = true;
};

const reconcileAuthoritativeState = async (
    announceSuccess = false
): Promise<boolean> => {
  if (reconciliationPromise) return reconciliationPromise;
  const reconciliationAuthEpoch = chatAuthEpoch;
  isRetryingReconciliation.value = true;
  let ownedReconciliation!: Promise<boolean>;
  ownedReconciliation = (async () => {
    try {
      const refreshed = await invokeSystemCommand({
        type: 'REFRESH_DATA',
        payload: { target: 'board_state' }
      });
      if (reconciliationAuthEpoch !== chatAuthEpoch) return false;
      if (!refreshed) {
        markReconciliationRequired();
        return false;
      }
      reconciliationRequired.value = false;
      if (announceSuccess) notifySuccess(t('app.chat.reconciliationSucceeded'));
      return true;
    } finally {
      if (reconciliationPromise === ownedReconciliation) {
        if (reconciliationAuthEpoch === chatAuthEpoch) {
          isRetryingReconciliation.value = false;
        }
        reconciliationPromise = null;
      }
    }
  })();
  reconciliationPromise = ownedReconciliation;
  return ownedReconciliation;
};

const executeStreamCommand = async (command: StreamCommand): Promise<boolean> => {
  const completed = await invokeSystemCommand(command);
  if (completed) {
    if (command.payload.assistantSummary || command.payload.assistantAction) {
      notifyInfo(command.payload.assistantSummary
        ?? t(`app.chat.assistantActions.${command.payload.assistantAction}`));
    }
    return true;
  }
  if (command.type === 'REFRESH_DATA' && command.payload?.target !== 'board_state') {
    const reconciled = await reconcileAuthoritativeState();
    if (reconciled) {
      notifyBlocked(t('app.chat.targetRefreshRecovered'));
      if (command.payload.assistantSummary || command.payload.assistantAction) {
        notifyInfo(command.payload.assistantSummary
          ?? t(`app.chat.assistantActions.${command.payload.assistantAction}`));
      }
      return true;
    }
  } else if (command.type === 'REFRESH_DATA') {
    markReconciliationRequired();
  }
  return false;
};

const retryAuthoritativeReconciliation = async () => {
  if (activeStreamSessionId.value) {
    const result = await settleActiveRequest(false);
    if (result === 'ready') notifySuccess(t('app.chat.reconciliationSucceeded'));
    return;
  }
  await reconcileAuthoritativeState(true);
};

const updateSessionActivity = (sessionId: string, active: boolean) => {
  if (!sessions.value.some(session => session.id === sessionId)) return;
  // Keep API snapshots immutable. A caller may reuse a response object while a background
  // poll or an account switch is still in flight; mutating it would leak activity into another
  // conversation or test fixture.
  sessions.value = sessions.value.map(session => session.id === sessionId
    ? { ...session, active }
    : session);
};

const isHttpNotFound = (error: any) => error?.response?.status === 404;

const clearAuthoritativelyDeletedSession = (sessionId: string) => {
  sessionListRequestEpoch += 1;
  sessions.value = sessions.value.filter(session => session.id !== sessionId);

  if (activeStreamSessionId.value === sessionId) {
    stopSessionActivityMonitor();
    activeStreamSessionId.value = '';
    activeStreamTurnId.value = '';
    activeStreamAuthToken.value = null;
    historyReplacementWithoutTerminalAllowed.value = false;
    explicitStopRegistrationPending.value = false;
    activeStreamRetryDraft.value = '';
  }

  if (currentSessionId.value !== sessionId) return;
  historyRequestEpoch += 1;
  historyAbortController.value?.abort();
  historyAbortController.value = null;
  confirmationRequestEpoch += 1;
  isLoadingHistory.value = false;
  historyLoadFailed.value = false;
  currentSessionId.value = '';
  messages.value = [];
  historyHasMore.value = false;
  historyNextBeforeId.value = null;
  pendingConfirmationKinds.value = [];
  pendingConfirmationLoadFailed.value = false;
};

const reportAuthoritativeSessionDeletion = (sessionId: string) => {
  clearAuthoritativelyDeletedSession(sessionId);
  notifyBlocked(t('app.chat.sessionRemovedExternally'));
};

const refreshPendingConfirmation = async (sessionId = currentSessionId.value, signal?: AbortSignal) => {
  const requestEpoch = ++confirmationRequestEpoch;
  if (!sessionId) {
    pendingConfirmationKinds.value = [];
    pendingConfirmationLoadFailed.value = false;
    return;
  }
  try {
    const pending = await getPendingConfirmation(sessionId, signal);
    if (requestEpoch === confirmationRequestEpoch && currentSessionId.value === sessionId) {
      pendingConfirmationKinds.value = pending.kinds;
      pendingConfirmationLoadFailed.value = false;
    }
  } catch (error: any) {
    if (signal?.aborted || error?.name === 'CanceledError' || error?.code === 'ERR_CANCELED') return;
    if (requestEpoch === confirmationRequestEpoch && currentSessionId.value === sessionId) {
      pendingConfirmationLoadFailed.value = true;
    }
    console.warn('[Chat] Could not refresh pending confirmation state:', error);
  }
};

const waitForActivityPoll = (signal: AbortSignal) => new Promise<void>(resolve => {
  const timer = window.setTimeout(done, 1000);
  function done() {
    window.clearTimeout(timer);
    signal.removeEventListener('abort', done);
    resolve();
  }
  if (signal.aborted) {
    done();
    return;
  }
  signal.addEventListener('abort', done, { once: true });
});

const stopSessionActivityMonitor = () => {
  activityMonitorEpoch += 1;
  activityMonitorAbortController?.abort();
  activityMonitorAbortController = null;
  isMonitoringRemoteExecution.value = false;
  remoteActivityCheckFailed.value = false;
};

const monitorSessionActivity = (sessionId: string, knownActive = false) => {
  if (!sessionId || (isStreaming.value && activeStreamSessionId.value === sessionId)) return;
  stopSessionActivityMonitor();
  const monitorEpoch = ++activityMonitorEpoch;
  const controller = new AbortController();
  activityMonitorAbortController = controller;
  if (knownActive) {
    activeStreamSessionId.value = sessionId;
    activeStreamTurnId.value = '';
    activeStreamAuthToken.value = scopedAuthToken.value;
    historyReplacementWithoutTerminalAllowed.value = true;
    activeStreamRetryDraft.value = '';
    isMonitoringRemoteExecution.value = true;
    updateSessionActivity(sessionId, true);
  }

  void (async () => {
    let consecutiveFailures = 0;
    while (!controller.signal.aborted && monitorEpoch === activityMonitorEpoch) {
      try {
        const activity = await getSessionActivity(sessionId, { signal: controller.signal });
        if (controller.signal.aborted || monitorEpoch !== activityMonitorEpoch) return;
        updateSessionActivity(sessionId, activity.active);
        if (!activity.active) {
          if (isMonitoringRemoteExecution.value && activeStreamSessionId.value === sessionId) {
            await settleActiveRequest(false);
          }
          return;
        }
        if (currentSessionId.value !== sessionId) return;
        consecutiveFailures = 0;
        remoteActivityCheckFailed.value = false;
        activeStreamSessionId.value = sessionId;
        activeStreamTurnId.value = '';
        activeStreamAuthToken.value = scopedAuthToken.value;
        historyReplacementWithoutTerminalAllowed.value = true;
        activeStreamRetryDraft.value = '';
        isMonitoringRemoteExecution.value = true;
      } catch (error: any) {
        if (controller.signal.aborted || monitorEpoch !== activityMonitorEpoch) return;
        if (error?.response?.status === 404) {
          updateSessionActivity(sessionId, false);
          if (activeStreamSessionId.value === sessionId) await settleActiveRequest(false);
          return;
        }
        consecutiveFailures += 1;
        if (consecutiveFailures >= 3) remoteActivityCheckFailed.value = true;
        console.warn('[Chat] Could not refresh authoritative session activity:', error);
      }
      await waitForActivityPoll(controller.signal);
    }
  })();
};

const stopActiveSessionsMonitor = () => {
  activeSessionsMonitorEpoch += 1;
  if (activeSessionsPollTimer) {
    clearTimeout(activeSessionsPollTimer);
    activeSessionsPollTimer = null;
  }
};

const scheduleActiveSessionsPoll = () => {
  if (!chatViewMounted || activeSessionsPollTimer) return;
  activeSessionsPollTimer = setTimeout(() => {
    activeSessionsPollTimer = null;
    void pollActiveSessions();
  }, hasAuthoritativeActiveSession.value ? 1000 : 5000);
};

type SessionCompletionObservation = Pick<ChatSession, 'active' | 'latestTerminalMessageId'>;

const captureSessionCompletionObservations = (availableSessions: ChatSession[]) => new Map(
    availableSessions.map(session => [session.id, {
      active: session.active,
      latestTerminalMessageId: session.latestTerminalMessageId
    }]));

const completedBackgroundSessions = (
    previous: Map<string, SessionCompletionObservation>,
    nextSessions: ChatSession[],
    compareTerminalMessages: boolean
) => nextSessions.filter(session => {
  const prior = previous.get(session.id);
  const observedNewTerminal = compareTerminalMessages
      && session.latestTerminalMessageId !== null
      && session.latestTerminalMessageId !== prior?.latestTerminalMessageId;
  const observedActiveSettlement = prior?.active === true && !session.active;
  return (observedNewTerminal || observedActiveSettlement)
      && session.id !== activeStreamSessionId.value;
});

const reconcileCompletedBackgroundSessions = async (
    completedSessions: ChatSession[],
    authEpoch: number
) => {
  if (completedSessions.length === 0) return;
  const reconciled = await reconcileAuthoritativeState();
  if (!chatViewMounted || authEpoch !== chatAuthEpoch) return;
  completedSessions.forEach(session => {
    notifyInfo(t(reconciled
      ? 'app.chat.backgroundSessionCompleted'
      : 'app.chat.backgroundSessionCompletedSyncPending', {
      title: session.title || t('app.chat.newChat')
    }));
  });
};

const pollActiveSessions = async () => {
  if (isLoadingSessions.value) {
    scheduleActiveSessionsPoll();
    return;
  }
  if (activeSessionsPollInFlight) return;
  activeSessionsPollInFlight = true;
  const pollEpoch = activeSessionsMonitorEpoch;
  const authEpoch = chatAuthEpoch;
  const sessionListEpoch = sessionListRequestEpoch;
  const previous = captureSessionCompletionObservations(sessions.value);
  try {
    const res = await getSessionList();
    if (authEpoch !== chatAuthEpoch || pollEpoch !== activeSessionsMonitorEpoch
        || sessionListEpoch !== sessionListRequestEpoch
        || !Array.isArray(res)) return;
    const ownedSessions = authenticatedUserId.value === null
        ? res
        : res.filter(session => session.userId === authenticatedUserId.value);
    sessions.value = ownedSessions;
    await reconcileCompletedBackgroundSessions(
        completedBackgroundSessions(previous, ownedSessions, true), authEpoch);
  } catch (error) {
    if (authEpoch === chatAuthEpoch && pollEpoch === activeSessionsMonitorEpoch
        && sessionListEpoch === sessionListRequestEpoch) {
      console.warn('[Chat] Could not refresh active chat sessions:', error);
    }
  } finally {
    activeSessionsPollInFlight = false;
    // A stale request can finish after a monitor stop/restart. Re-arm from current state so the
    // replacement monitor is not lost merely because its first timer fired while this request ran.
    if (chatViewMounted) scheduleActiveSessionsPoll();
  }
};

watch(hasAuthoritativeActiveSession, () => {
  stopActiveSessionsMonitor();
  scheduleActiveSessionsPoll();
}, { immediate: true });

const reattachAuthoritativeActiveSession = (availableSessions: ChatSession[]) => {
  const activeSession = availableSessions.find(session =>
    session.id === currentSessionId.value && session.active)
      ?? (!currentSessionId.value ? availableSessions.find(session => session.active) : undefined);
  if (!activeSession) return;

  if (currentSessionId.value === activeSession.id) {
    monitorSessionActivity(activeSession.id, true);
    return;
  }
  void handleSelectSession(activeSession.id, true);
};

const initSessions = async (reattachActive = true): Promise<boolean> => {
  const requestEpoch = ++sessionListRequestEpoch;
  const authEpoch = chatAuthEpoch;
  const previous = captureSessionCompletionObservations(sessions.value);
  const compareTerminalMessages = sessionCompletionObservationsInitialized;
  isLoadingSessions.value = true;
  sessionListLoadFailed.value = false;
  try {
    const res = await getSessionList();
    if (!Array.isArray(res)) throw new Error('Session list response is not an array');
    const ownedSessions = authenticatedUserId.value === null
        ? res
        : res.filter(session => session.userId === authenticatedUserId.value);
    if (requestEpoch === sessionListRequestEpoch) {
      sessionCompletionObservationsInitialized = true;
      sessions.value = ownedSessions;
      if (reattachActive && !isStreaming.value && !activeStreamSessionId.value) {
        reattachAuthoritativeActiveSession(ownedSessions);
      }
      await reconcileCompletedBackgroundSessions(
          completedBackgroundSessions(previous, ownedSessions, compareTerminalMessages), authEpoch);
      return true;
    }
    return false;
  } catch (e) {
    if (requestEpoch === sessionListRequestEpoch) sessionListLoadFailed.value = true;
    console.error('加载会话列表失败:', e);
    return false;
  } finally {
    if (requestEpoch === sessionListRequestEpoch) isLoadingSessions.value = false;
  }
};

const handleCreateSession = async (signal?: AbortSignal, notifyOnFailure = true) => {
  const authEpoch = chatAuthEpoch;
  try {
    const session = await createSession(signal);
    if (authEpoch !== chatAuthEpoch) return '';
    if (session && session.id) {
      sessionListRequestEpoch += 1;
      isLoadingSessions.value = false;
      sessionListLoadFailed.value = false;
      sessions.value = [session, ...sessions.value.filter(item => item.id !== session.id)];
      return session.id;
    }
    throw new Error('Chat session response is incomplete');
  } catch (e) {
    if (authEpoch !== chatAuthEpoch) return '';
    console.error('创建会话失败:', e);
    if (notifyOnFailure) notifyError(t('app.chat.createSessionFailed'));
    return null;
  }
};

const onNewChatClick = async () => {
  if (isCreatingSession.value || isPreparingStreamSession.value || isSettlingStream.value) return;
  const navigationEpoch = ++userSessionNavigationEpoch;
  isCreatingSession.value = true;
  try {
    const newId = await handleCreateSession();
    if (!newId) return;
    // A session click made while creation was in flight is the user's newer navigation intent.
    if (navigationEpoch !== userSessionNavigationEpoch) return;
    await handleSelectSession(newId);
    // 新建对话后自动收起侧边栏（移动端友好）
    if (window.innerWidth < 960 || isChatPanelCompact.value) isSidebarOpen.value = false;
  } finally {
    isCreatingSession.value = false;
  }
};

const handleUserSelectSession = (sessionId: string, knownActive = false) => {
  userSessionNavigationEpoch += 1;
  return handleSelectSession(sessionId, knownActive);
};

const handleDelete = async (sessionId: string) => {
  const confirmed = await confirmDestructive({
    title: t('app.chat.deleteSessionTitle'),
    message: t('app.chat.deleteSessionMessage'),
    confirmText: t('app.delete')
  });
  if (!confirmed) return;

  try {
    await deleteSession(sessionId);
    clearAuthoritativelyDeletedSession(sessionId);
    notifySuccess(t('app.chat.sessionDeleted'));
  } catch (error: any) {
    const reasonCode = error?.response?.data?.data?.reasonCode;
    notifyError(reasonCode === 'CHAT_SESSION_BUSY'
        ? t('app.chat.sessionStillRunning')
        : t('app.chat.deleteFailed'));
  }
};

const handleSelectSession = async (sessionId: string, knownActive = false) => {
  if (isPreparingStreamSession.value || isSettlingStream.value) return;
  if (currentSessionId.value === sessionId && !historyLoadFailed.value) {
    void acknowledgeCurrentVisibleHistory();
    if (!isAssistantBusy.value) {
      monitorSessionActivity(sessionId, knownActive);
      void refreshPendingConfirmation(sessionId);
    }
    return;
  }

  // Navigation detaches the live transport only. The durable execution remains owned by its
  // session and is reflected by the sidebar activity indicator until the server settles it.
  detachCurrentExecutionForNavigation();
  historyRequestEpoch += 1;
  historyAbortController.value?.abort();

  currentSessionId.value = sessionId;
  messages.value = [];
  historyHasMore.value = false;
  historyNextBeforeId.value = null;
  pendingConfirmationKinds.value = [];
  pendingConfirmationLoadFailed.value = false;
  historyLoadFailed.value = false;
  isLoadingHistory.value = true;
  const requestEpoch = ++historyRequestEpoch;
  const controller = new AbortController();
  historyAbortController.value = controller;
  if (knownActive) monitorSessionActivity(sessionId, true);

  // 移动端体验优化：选中后收起侧边栏
  if (window.innerWidth < 960 || isChatPanelCompact.value) isSidebarOpen.value = false;

  try {
    const historyPage = await getSessionHistory(sessionId, controller.signal);
    if (requestEpoch !== historyRequestEpoch || currentSessionId.value !== sessionId) return;
    applyHistoryPage(historyPage, false);
    historyLoadFailed.value = false;
    await refreshPendingConfirmation(sessionId, controller.signal);
    scrollToBottom(true);
    if (!knownActive) monitorSessionActivity(sessionId);
  } catch (e: any) {
    if (requestEpoch !== historyRequestEpoch) return;
    if (e?.name !== 'CanceledError' && e?.code !== 'ERR_CANCELED') {
      historyLoadFailed.value = true;
      notifyError(t('app.chat.networkError'));
    }
  } finally {
    if (requestEpoch === historyRequestEpoch) {
      isLoadingHistory.value = false;
      if (historyAbortController.value === controller) historyAbortController.value = null;
    }
  }
};

const acknowledgeVisibleTerminal = async (sessionId: string, history: ChatMessage[]) => {
  if (!visible.value || document.hidden || currentSessionId.value !== sessionId) return;
  const terminal = [...history].reverse().find(message =>
    message.role === 'assistant'
    && Number.isSafeInteger(message.id)
    && (message.id ?? 0) > 0
    && Boolean(message.executionStatus));
  if (!terminal?.id || !terminal.executionStatus) return;
  const terminalMessageId = terminal.id;
  if ((terminalSeenRequests.get(sessionId) ?? 0) >= terminalMessageId) return;

  const authEpoch = chatAuthEpoch;
  terminalSeenRequests.set(sessionId, terminalMessageId);
  try {
    await markSessionTerminalSeen(sessionId, terminalMessageId);
    if (authEpoch !== chatAuthEpoch) return;
    if (sessions.value.some(session => session.id === sessionId && session.hasUnreadUpdate)) {
      await initSessions(false);
    }
  } catch (error) {
    if (terminalSeenRequests.get(sessionId) === terminalMessageId) {
      terminalSeenRequests.delete(sessionId);
    }
    console.warn(`Could not acknowledge visible assistant result for session ${sessionId}:`, error);
  }
};

const acknowledgeCurrentVisibleHistory = () => {
  const sessionId = currentSessionId.value;
  if (sessionId) void acknowledgeVisibleTerminal(sessionId, messages.value);
};

const applyHistoryPage = (page: ChatHistoryPage, prepend: boolean) => {
  const cleaned = page.messages.map(m => ({
      ...m,
      content: m.content ? m.content.replace('CallEnd|>', '') : ''
    }));
  if (prepend) {
    const existingIds = new Set(messages.value.map(message => message.id).filter(id => id != null));
    messages.value = [...cleaned.filter(message => message.id == null || !existingIds.has(message.id)), ...messages.value];
  } else {
    messages.value = cleaned;
    const sessionId = currentSessionId.value;
    if (sessionId) void nextTick(() => acknowledgeVisibleTerminal(sessionId, cleaned));
  }
  historyHasMore.value = page.hasMore && page.nextBeforeId != null;
  historyNextBeforeId.value = page.nextBeforeId;
};

const loadOlderHistory = async () => {
  const sessionId = currentSessionId.value;
  const beforeId = historyNextBeforeId.value;
  if (!sessionId || beforeId == null || !historyHasMore.value || isLoadingOlderHistory.value) return;
  isLoadingOlderHistory.value = true;
  const viewport = scrollRef.value;
  const previousHeight = viewport?.scrollHeight ?? 0;
  const previousTop = viewport?.scrollTop ?? 0;
  try {
    const page = await getSessionHistory(sessionId, { beforeId, limit: 50 });
    if (currentSessionId.value !== sessionId) return;
    applyHistoryPage(page, true);
    await nextTick();
    if (viewport) viewport.scrollTop = viewport.scrollHeight - previousHeight + previousTop;
  } catch (error) {
    console.warn('[Chat] Failed to load older history:', error);
    notifyBlocked(t('app.chat.historyLoadOlderFailed'));
  } finally {
    isLoadingOlderHistory.value = false;
  }
};

const markActiveAssistantAsResponseStopped = () => {
  const lastMessage = messages.value[messages.value.length - 1];
  const notice = t('app.chat.responseStoppedReconcile');
  if (lastMessage?.role === 'assistant') {
    lastMessage.content = lastMessage.content?.trim()
        ? `${lastMessage.content}\n\n> ${notice}`
        : notice;
  } else {
    messages.value.push({ role: 'assistant', content: notice });
  }
  scrollToBottom(false);
};

const hasTerminalAssistantRecord = (history: ChatMessage[], turnId?: string) => {
  if (turnId) {
    return history.some(message =>
      message.role === 'assistant'
      && message.turnId === turnId
      && Boolean(message.executionStatus));
  }
  for (let index = history.length - 1; index >= 0; index -= 1) {
    const message = history[index];
    if (message.role === 'assistant' && message.executionStatus) return true;
    if (message.role === 'user') return false;
  }
  return false;
};

const restoreRetryDraftIfTurnWasNotAdmitted = (history: ChatMessage[], turnId: string) => {
  if (!activeStreamRetryDraft.value || !turnId) return;
  const userTurnWasPersisted = history.some(message =>
    message.role === 'user' && message.turnId === turnId);
  if (!userTurnWasPersisted && !inputValue.value) {
    inputValue.value = activeStreamRetryDraft.value;
  }
};

const detachActiveTransport = (showCancelledMessage = false) => {
  if (streamElapsedTimer) {
    clearInterval(streamElapsedTimer);
    streamElapsedTimer = null;
  }
  const controller = abortController.value;
  if (!controller) return null;
  streamRequestEpoch += 1;
  if (abortController.value === controller) abortController.value = null;
  isStreaming.value = false;
  if (showCancelledMessage) {
    markActiveAssistantAsResponseStopped();
  }
  return controller;
};

const abortActiveTransport = (showCancelledMessage = false) => {
  detachActiveTransport(showCancelledMessage)?.abort();
};

const detachCurrentExecutionForNavigation = () => {
  const detachedSessionId = activeStreamSessionId.value;
  stopSessionActivityMonitor();
  abortActiveTransport(false);
  isStreaming.value = false;
  streamProgress.value = null;
  streamProgressEvents.value = [];
  streamElapsedSeconds.value = 0;
  if (detachedSessionId) updateSessionActivity(detachedSessionId, true);
  activeStreamSessionId.value = '';
  activeStreamTurnId.value = '';
  activeStreamAuthToken.value = null;
  historyReplacementWithoutTerminalAllowed.value = false;
  explicitStopRegistrationPending.value = false;
  activeStreamRetryDraft.value = '';
};

const requestOwnedSessionStop = (sessionId: string, turnId?: string): Promise<void> => {
  const authToken = activeStreamAuthToken.value || scopedAuthToken.value;
  return authToken
      ? requestSessionStop(sessionId, turnId, authToken)
      : requestSessionStop(sessionId, turnId);
};

const resetChatForAuthSubjectChange = (previousAuthToken: string | null) => {
  const sessionId = activeStreamSessionId.value;
  const activeSessionIds = Array.from(new Set([
    ...sessions.value.filter(session => session.active).map(session => session.id),
    ...(sessionId ? [sessionId] : [])
  ]));
  const stopAlreadyPending = explicitStopRegistrationPending.value && Boolean(settlementPromise);
  if (previousAuthToken) {
    const turnId = activeStreamTurnId.value;
    const ownerToken = activeStreamAuthToken.value || previousAuthToken;
    activeSessionIds.forEach(activeSessionId => {
      if (activeSessionId === sessionId && stopAlreadyPending) return;
      void requestSessionStop(
          activeSessionId,
          activeSessionId === sessionId ? turnId || undefined : undefined,
          ownerToken
      ).catch(error => {
        console.warn(`[Chat] Failed to stop session ${activeSessionId} during an account change:`, error);
      });
    });
  }
  settlementDetachedTransport?.abort();
  settlementDetachedTransport = null;
  chatAuthEpoch += 1;
  streamRequestEpoch += 1;
  sessionListRequestEpoch += 1;
  historyRequestEpoch += 1;
  confirmationRequestEpoch += 1;
  abortActiveTransport(false);
  stopSessionActivityMonitor();
  stopActiveSessionsMonitor();
  settlementAbortController?.abort();
  settlementAbortController = null;
  settlementPromise = null;
  reconciliationPromise = null;
  historyAbortController.value?.abort();
  historyAbortController.value = null;

  sessions.value = [];
  sessionCompletionObservationsInitialized = false;
  terminalSeenRequests.clear();
  currentSessionId.value = '';
  messages.value = [];
  // The fallback key is positional (`index:<n>`), so a collapse recorded for one account's last row
  // would apply to an unrelated message at the same index after the subject changes.
  collapsedExecutionTraces.value = new Set();
  inputValue.value = '';
  pendingConfirmationKinds.value = [];
  pendingConfirmationLoadFailed.value = false;
  activeStreamSessionId.value = '';
  activeStreamTurnId.value = '';
  activeStreamAuthToken.value = null;
  historyReplacementWithoutTerminalAllowed.value = false;
  explicitStopRegistrationPending.value = false;
  activeStreamRetryDraft.value = '';
  isStreaming.value = false;
  isSettlingStream.value = false;
  isMonitoringRemoteExecution.value = false;
  reconciliationRequired.value = false;
  isRetryingReconciliation.value = false;
  isLoadingSessions.value = false;
  sessionListLoadFailed.value = false;
  isCreatingSession.value = false;
  isPreparingStreamSession.value = false;
  isLoadingHistory.value = false;
  historyLoadFailed.value = false;
  isLoadingOlderHistory.value = false;
  historyHasMore.value = false;
  historyNextBeforeId.value = null;
  streamProgress.value = null;
  streamProgressEvents.value = [];
  streamElapsedSeconds.value = 0;
  boardContext.value = null;
  chatStore.setActiveCount(0);
  chatStore.setStreaming(false);
};

const waitForSessionIdle = async (sessionId: string, signal?: AbortSignal): Promise<boolean> => {
  const deadline = Date.now() + 10_000;
  let consecutiveFailures = 0;
  while (Date.now() < deadline) {
    try {
      const activity = await getSessionActivity(sessionId, { signal });
      if (!activity.active) return true;
      consecutiveFailures = 0;
    } catch (error: any) {
      if (error?.response?.status === 404) return true;
      consecutiveFailures += 1;
      if (consecutiveFailures >= 3) throw error;
    }
    await new Promise(resolve => window.setTimeout(resolve, 500));
  }
  return false;
};

const settleActiveRequest = (
    showCancelledMessage = false
): Promise<ChatLogoutPreparation> => {
  if (settlementPromise) return settlementPromise;
  const sessionId = activeStreamSessionId.value || currentSessionId.value;
  const turnId = activeStreamTurnId.value;
  const wasMonitoringRemoteExecution = isMonitoringRemoteExecution.value
      && activeStreamSessionId.value === sessionId;
  const stopRequested = showCancelledMessage && Boolean(activeStreamSessionId.value || currentSessionId.value);
  if (stopRequested) explicitStopRegistrationPending.value = true;
  const mustRegisterExplicitStop = explicitStopRegistrationPending.value;
  if (stopRequested || wasMonitoringRemoteExecution) {
    historyReplacementWithoutTerminalAllowed.value = true;
  }
  const replaceHistoryWithoutTerminal = historyReplacementWithoutTerminalAllowed.value;
  if (!abortController.value && !activeStreamSessionId.value) {
    if (!reconciliationRequired.value) return Promise.resolve('ready');
    return reconcileAuthoritativeState().then(
        reconciled => reconciled ? 'ready' : 'reconciliation-failed');
  }
  if (wasMonitoringRemoteExecution) stopSessionActivityMonitor();

  let detachedController: AbortController | null = null;
  if (stopRequested && sessionId) {
    // Invalidate the original send flow before the stop endpoint closes SSE; otherwise it
    // can race into its normal-completion reconciliation path.
    detachedController = detachActiveTransport(showCancelledMessage);
    settlementDetachedTransport = detachedController;
  } else {
    abortActiveTransport(showCancelledMessage && Boolean(sessionId));
  }
  if (!sessionId) {
    if (turnId) {
      messages.value = messages.value.filter(message => message.turnId !== turnId);
      if (activeStreamRetryDraft.value && !inputValue.value) {
        inputValue.value = activeStreamRetryDraft.value;
      }
      activeStreamTurnId.value = '';
      activeStreamAuthToken.value = null;
      historyReplacementWithoutTerminalAllowed.value = false;
      explicitStopRegistrationPending.value = false;
      activeStreamRetryDraft.value = '';
    }
    return initSessions(false).then(() => 'ready');
  }
  isSettlingStream.value = true;
  const settlementAuthEpoch = chatAuthEpoch;
  const settlementContextIsCurrent = () => settlementAuthEpoch === chatAuthEpoch;
  const controller = new AbortController();
  settlementAbortController = controller;
  let ownedSettlement!: Promise<ChatLogoutPreparation>;
  ownedSettlement = (async () => {
    let outcome: ChatLogoutPreparation = 'ready';
    let retainActiveSession = false;
    try {
      if (mustRegisterExplicitStop) {
        try {
          await requestOwnedSessionStop(sessionId, turnId || undefined);
          if (!settlementContextIsCurrent()) return 'ready';
          explicitStopRegistrationPending.value = false;
        } catch (error) {
          if (!settlementContextIsCurrent()) return 'ready';
          if (isHttpNotFound(error)) {
            explicitStopRegistrationPending.value = false;
            reportAuthoritativeSessionDeletion(sessionId);
            return 'ready';
          }
          outcome = 'outcome-unknown';
          retainActiveSession = true;
          reconciliationRequired.value = true;
          console.warn('[Chat] Failed to register explicit stop before aborting transport:', error);
          notifyBlocked(t('app.chat.stopOutcomeUnknown'));
          return outcome;
        } finally {
          detachedController?.abort();
          if (settlementDetachedTransport === detachedController) {
            settlementDetachedTransport = null;
          }
        }
      }
      try {
        const idle = await waitForSessionIdle(sessionId, controller.signal);
        if (!settlementContextIsCurrent()) return 'ready';
        if (!idle) {
          retainActiveSession = true;
          if (wasMonitoringRemoteExecution) {
            monitorSessionActivity(sessionId, true);
            notifyBlocked(t('app.chat.sessionStillRunningRetry'));
            return 'reconciliation-failed';
          }
          reconciliationRequired.value = true;
          notifyBlocked(t('app.chat.sessionStillRunningRetry'));
          return 'reconciliation-failed';
        }
      } catch (error) {
        if (!settlementContextIsCurrent()) return 'ready';
        if (controller.signal.aborted) return 'reconciliation-failed';
        outcome = 'outcome-unknown';
        retainActiveSession = true;
        reconciliationRequired.value = true;
        console.error('[Chat] Failed to confirm that the stopped request is idle:', error);
      }

      const reconciled = await reconcileAuthoritativeState();
      if (!settlementContextIsCurrent()) return 'ready';

      try {
        if (currentSessionId.value === sessionId) {
          historyRequestEpoch += 1;
          historyAbortController.value?.abort();
          historyAbortController.value = null;
          isLoadingHistory.value = false;
          const settlementHistoryEpoch = historyRequestEpoch;
          const history = await getSessionHistory(sessionId, controller.signal);
          if (!settlementContextIsCurrent()) return 'ready';
          if (settlementHistoryEpoch !== historyRequestEpoch
              || currentSessionId.value !== sessionId) {
            return reconciled ? outcome : 'reconciliation-failed';
          }
          const hasTerminal = hasTerminalAssistantRecord(history.messages, turnId);
          if (hasTerminal || replaceHistoryWithoutTerminal) {
            applyHistoryPage(history, false);
            historyLoadFailed.value = false;
            if (replaceHistoryWithoutTerminal && !hasTerminal) {
              restoreRetryDraftIfTurnWasNotAdmitted(history.messages, turnId);
              notifyBlocked(t('app.chat.incompleteStreamHistoryRestored'));
            }
          } else {
            notifyBlocked(t('app.chat.historyTerminalRecordMissing'));
            retainActiveSession = true;
            reconciliationRequired.value = true;
            return 'reconciliation-failed';
          }
        }
        await initSessions(false);
        if (!settlementContextIsCurrent()) return 'ready';
        await refreshPendingConfirmation(sessionId);
        if (!settlementContextIsCurrent()) return 'ready';
      } catch (error) {
        if (!settlementContextIsCurrent()) return 'ready';
        if (isHttpNotFound(error)) {
          reportAuthoritativeSessionDeletion(sessionId);
          return reconciled ? 'ready' : 'reconciliation-failed';
        }
        console.error('[Chat] Failed to reload chat history after settlement:', error);
        notifyBlocked(t('app.chat.historyReloadAfterSettleFailed'));
        retainActiveSession = true;
        reconciliationRequired.value = true;
        return 'reconciliation-failed';
      }
      if (!reconciled) return 'reconciliation-failed';
      if (outcome === 'outcome-unknown') {
        reconciliationRequired.value = true;
        notifyBlocked(t('app.chat.stopOutcomeUnknown'));
      }
      return outcome;
    } finally {
      const ownsSettlement = settlementPromise === ownedSettlement;
      const contextIsCurrent = settlementContextIsCurrent();
      if (ownsSettlement && contextIsCurrent) {
        if (!retainActiveSession && activeStreamSessionId.value === sessionId) {
          activeStreamSessionId.value = '';
          activeStreamTurnId.value = '';
          activeStreamAuthToken.value = null;
          historyReplacementWithoutTerminalAllowed.value = false;
          explicitStopRegistrationPending.value = false;
          activeStreamRetryDraft.value = '';
          updateSessionActivity(sessionId, false);
        }
        isSettlingStream.value = false;
      }
      if (settlementAbortController === controller) settlementAbortController = null;
      if (ownsSettlement) settlementPromise = null;
      if (ownsSettlement && contextIsCurrent
          && !retainActiveSession && !activeStreamSessionId.value) {
        reattachAuthoritativeActiveSession(sessions.value);
      }
    }
  })();
  settlementPromise = ownedSettlement;
  return ownedSettlement;
};

const handleStop = async () => {
  await settleActiveRequest(true);
};

const prepareForLogout = async (): Promise<ChatLogoutPreparation> => {
  let outcome: ChatLogoutPreparation = await initSessions(false)
      ? 'ready'
      : 'outcome-unknown';
  const attachedSessionId = activeStreamSessionId.value;
  const backgroundSessionIds = Array.from(new Set(
      sessions.value
          .filter(session => session.active && session.id !== attachedSessionId)
          .map(session => session.id)));
  const stopConfirmedSessionIds: string[] = [];
  const ownerToken = activeStreamAuthToken.value || scopedAuthToken.value;

  for (const sessionId of backgroundSessionIds) {
    try {
      await (ownerToken
          ? requestSessionStop(sessionId, undefined, ownerToken)
          : requestSessionStop(sessionId));
      stopConfirmedSessionIds.push(sessionId);
    } catch (error) {
      if (isHttpNotFound(error)) continue;
      console.warn(`[Chat] Failed to stop background session ${sessionId} before logout:`, error);
      outcome = 'outcome-unknown';
    }
  }

  if (attachedSessionId) {
    const attachedOutcome = await settleActiveRequest(true);
    if (attachedOutcome === 'reconciliation-failed') return attachedOutcome;
    if (attachedOutcome === 'outcome-unknown') outcome = attachedOutcome;
  }

  for (const sessionId of stopConfirmedSessionIds) {
    try {
      if (!await waitForSessionIdle(sessionId)) return 'reconciliation-failed';
      updateSessionActivity(sessionId, false);
    } catch (error) {
      console.warn(`[Chat] Could not confirm background session ${sessionId} stopped before logout:`, error);
      outcome = 'outcome-unknown';
    }
  }

  if (backgroundSessionIds.length > 0 || reconciliationRequired.value) {
    if (!await reconcileAuthoritativeState()) return 'reconciliation-failed';
    await initSessions(false);
  }
  return outcome;
};

defineExpose({ prepareForLogout });

const handleDocumentVisibilityChange = () => {
  if (document.hidden) {
    stopPanelInteraction();
    return;
  }
  if (!document.hidden && visible.value) void initSessions();
};

const handlePanelWindowFocus = () => {
  if (visible.value) void initSessions();
};

watch(authenticatedUserId, (nextUserId, previousUserId) => {
  if (nextUserId === previousUserId) return;
  const previousAuthToken = scopedAuthToken.value;
  resetChatForAuthSubjectChange(previousAuthToken);
  scopedAuthToken.value = authState.token;
  scopedAuthUserId = nextUserId;
  if (nextUserId !== null && visible.value) {
    refreshBoardContext();
    void initSessions();
  }
}, { flush: 'sync' });

watch(() => authState.token, nextToken => {
  if (authenticatedUserId.value !== scopedAuthUserId) return;
  scopedAuthToken.value = nextToken;
  if (activeStreamAuthToken.value) activeStreamAuthToken.value = nextToken;
}, { flush: 'post' });

onMounted(() => {
  chatViewMounted = true;
  if (visible.value) {
    refreshBoardContext();
    void initSessions();
    nextTick(clampExistingChatPosition);
  }
  scheduleActiveSessionsPoll();
  window.addEventListener('resize', handleChatViewportResize);
  window.addEventListener('blur', handlePanelWindowBlur);
  window.addEventListener('focus', handlePanelWindowFocus);
  document.addEventListener('visibilitychange', handleDocumentVisibilityChange);
});

onUnmounted(() => {
  chatViewMounted = false;
  abortActiveTransport(false);
  stopListening();
  stopSessionActivityMonitor();
  stopActiveSessionsMonitor();
  settlementAbortController?.abort();
  settlementAbortController = null;
  settlementDetachedTransport?.abort();
  settlementDetachedTransport = null;
  chatStore.setStreaming(false);
  if (streamElapsedTimer) clearInterval(streamElapsedTimer);
  streamElapsedTimer = null;
  historyRequestEpoch += 1;
  historyAbortController.value?.abort();
  historyAbortController.value = null;
  isLoadingHistory.value = false;
  stopPanelInteraction();
  window.removeEventListener('resize', handleChatViewportResize);
  window.removeEventListener('blur', handlePanelWindowBlur);
  window.removeEventListener('focus', handlePanelWindowFocus);
  document.removeEventListener('visibilitychange', handleDocumentVisibilityChange);
});

const submitChatTurn = async (content: string, confirmation?: ChatConfirmationCommand) => {
  if (props.interactionLocked) {
    notifyBlocked(t('app.chat.boardInteractionLocked'));
    return;
  }
  if (!content || isLoading.value) return;
  if (content.length > REQUEST_LIMITS.chatContentCharacters) {
    notifyBlocked(t('app.chat.contentTooLong', {
      limit: REQUEST_LIMITS.chatContentCharacters.toLocaleString()
    }));
    return;
  }
  if (props.prepareInteraction?.() === false || props.interactionLocked) {
    notifyBlocked(t('app.chat.boardInteractionLocked'));
    return;
  }
  const requestAuthEpoch = chatAuthEpoch;
  const turnId = typeof globalThis.crypto?.randomUUID === 'function'
      ? globalThis.crypto.randomUUID()
      : `chat-${Date.now().toString(36)}-${Math.random().toString(36).slice(2)}`;

  if (!confirmation) inputValue.value = '';
  messages.value.push({ role: 'user', content, turnId });
  scrollToBottom(true);

  isStreaming.value = true;
  const requestEpoch = ++streamRequestEpoch;
  const requestContextIsCurrent = () =>
      requestAuthEpoch === chatAuthEpoch && requestEpoch === streamRequestEpoch;
  const controller = new AbortController();
  abortController.value = controller;
  activeStreamTurnId.value = turnId;
  historyReplacementWithoutTerminalAllowed.value = false;
  explicitStopRegistrationPending.value = false;
  activeStreamRetryDraft.value = confirmation ? '' : content;

  // 用于跟踪是否收到了任何内容
  let hasReceivedContent = false;
  let streamErrorHandled = false;
  let requestAccepted = false;
  let requestDispatched = false;
  let acceptedStreamFailed = false;
  // The streaming row is owned by `turnId`, not by its position. "Load older messages" prepends a
  // page, which shifts every index: an index-owned row would send subsequent chunks, the terminal
  // status, and the execution trace into an unrelated archived message.
  const activeAssistantMessage = () =>
      messages.value.find(message => message.role === 'assistant' && message.turnId === turnId);
  streamProgressEvents.value = [];
  appendStreamProgress({ stage: 'CONTEXT_READY' });
  streamElapsedSeconds.value = 0;
  const streamStartedAt = Date.now();
  if (streamElapsedTimer) clearInterval(streamElapsedTimer);
  streamElapsedTimer = setInterval(() => {
    streamElapsedSeconds.value = Math.floor((Date.now() - streamStartedAt) / 1000);
  }, 1000);
  let commandExecutionChain: Promise<void> = Promise.resolve();
  const queueCommandExecution = (command: StreamCommand) => {
    commandExecutionChain = commandExecutionChain.then(async () => {
      await executeStreamCommand(command);
    });
  };

  try {
    let targetSessionId = currentSessionId.value;
    // 自动创建新会话
    if (!targetSessionId) {
      isPreparingStreamSession.value = true;
      try {
        const newId = await handleCreateSession(controller.signal, false);
        if (requestEpoch !== streamRequestEpoch) return;
        if (!newId) throw new Error(t('app.chat.createSessionFailed'));
        targetSessionId = newId;
        currentSessionId.value = targetSessionId;
      } finally {
        isPreparingStreamSession.value = false;
      }
    }
    activeStreamSessionId.value = targetSessionId;
    updateSessionActivity(targetSessionId, true);

    // 先插入一条空的 AI 消息占位
    messages.value.push({
      role: 'assistant',
      content: '',
      turnId,
      executionTrace: [...streamProgressEvents.value]
    });
    scrollToBottom(true);

    const renderStreamError = (error: unknown) => {
      if (requestEpoch !== streamRequestEpoch) return;
      streamErrorHandled = true;
      const msg = activeAssistantMessage();
      if (!msg) return;

      const prefix = error instanceof ChatStreamError && error.serverFrame
          ? t('app.chat.serverError')
          : t('app.chat.requestFailed');
      const errorText = `${prefix}: ${formatStreamError(error)}`;
      if (hasReceivedContent && msg.content) {
        msg.content += `\n\n> ${errorText}`;
      } else {
        msg.content = errorText;
        hasReceivedContent = true;
      }
      scrollToBottom(false);
    };

    // sendStreamChat reads the current token synchronously before dispatch. Capture
    // the same value here after any asynchronous session creation has completed.
    activeStreamAuthToken.value = authState.token;
    requestDispatched = true;
    await sendStreamChat(
        targetSessionId,
        content,
        {
          onMessage: (chunk) => {
            if (requestEpoch !== streamRequestEpoch) return;
            const cleanChunk = chunk.replace('CallEnd|>', '');
            if (!cleanChunk) return;

            hasReceivedContent = true;
            const msg = activeAssistantMessage();
            if (!msg) return;
            // 直接追加，渲染器会自动处理 Markdown 格式
            msg.content += cleanChunk;
            scrollToBottom(false);
          },
          onAccepted: () => {
            if (requestEpoch !== streamRequestEpoch) return;
            requestAccepted = true;
            if (confirmation) pendingConfirmationKinds.value = [];
          },
          onCommand: (cmd: StreamCommand) => {
            if (requestEpoch !== streamRequestEpoch) return;
            queueCommandExecution(cmd);
          },
          onProgress: (progress: StreamProgress) => {
            if (requestEpoch !== streamRequestEpoch) return;
            appendStreamProgress(progress);
            const msg = activeAssistantMessage();
            if (msg) msg.executionTrace = [...streamProgressEvents.value];
          },
          onError: (err: any) => {
            if (requestEpoch !== streamRequestEpoch) return;
            if (requestAccepted) {
              acceptedStreamFailed = true;
              historyReplacementWithoutTerminalAllowed.value = true;
            }
            renderStreamError(err);
            console.error('[Chat] 流式错误:', err);
          },
          onFinish: (terminal: StreamTerminal) => {
            if (requestEpoch !== streamRequestEpoch) return;
            const msg = activeAssistantMessage();
            if (msg) msg.executionStatus = terminal.executionStatus;
            // Refresh title/time only after the server stream actually completed.
            void initSessions();
          }
        },
        controller,
        turnId,
        confirmation
    );
    requestAccepted = true;
  } catch (error) {
    if (requestEpoch !== streamRequestEpoch) return;
    const definitelyRejected = error instanceof ChatStreamError && error.kind === 'HTTP_ERROR';
    if (requestDispatched && !requestAccepted && !definitelyRejected) {
      requestAccepted = true;
    }
    if (requestAccepted) {
      acceptedStreamFailed = true;
      historyReplacementWithoutTerminalAllowed.value = true;
    }
    console.error('[Chat] 发送消息失败:', error);
    if (!requestAccepted) {
      messages.value = messages.value.filter(message => message.turnId !== turnId);
      if (!confirmation && !inputValue.value) inputValue.value = content;
      if (activeStreamTurnId.value === turnId) {
        activeStreamTurnId.value = '';
        historyReplacementWithoutTerminalAllowed.value = false;
        explicitStopRegistrationPending.value = false;
        activeStreamRetryDraft.value = '';
      }
      notifyError(t('app.chat.sendFailedWithReason', { reason: formatStreamError(error) }));
    } else if (!streamErrorHandled && !hasReceivedContent) {
      notifyError(t('app.chat.sendFailedWithReason', {
        reason: error instanceof Error ? error.message : String(error)
      }));
    }
  } finally {
    if (requestEpoch === streamRequestEpoch) {
      await commandExecutionChain;
      if (requestEpoch !== streamRequestEpoch || !requestContextIsCurrent()) return;
      isStreaming.value = false;
      streamProgress.value = null;
      const completedMessage = activeAssistantMessage();
      if (completedMessage) {
        completedMessage.executionTrace = [...streamProgressEvents.value];
        completedMessage.executionElapsedSeconds = streamElapsedSeconds.value;
      }
      if (streamElapsedTimer) {
        clearInterval(streamElapsedTimer);
        streamElapsedTimer = null;
      }
      if (abortController.value === controller) abortController.value = null;
      const completedSessionId = activeStreamSessionId.value;
      const completedTurnId = activeStreamTurnId.value;
      if (completedSessionId) {
        isSettlingStream.value = true;
        let retainActiveSession = false;
        try {
          if (!requestAccepted) {
            await initSessions();
            if (!requestContextIsCurrent()) return;
            await refreshPendingConfirmation(completedSessionId);
            if (!requestContextIsCurrent()) return;
          } else {
            const idle = await waitForSessionIdle(completedSessionId);
            if (!requestContextIsCurrent()) return;
            if (!idle) {
              retainActiveSession = true;
              reconciliationRequired.value = true;
              notifyBlocked(t('app.chat.sessionStillRunningRetry'));
            } else {
              if (acceptedStreamFailed) {
                await reconcileAuthoritativeState();
                if (!requestContextIsCurrent()) return;
              }
              if (currentSessionId.value === completedSessionId) {
                try {
                  const history = await getSessionHistory(completedSessionId);
                  if (!requestContextIsCurrent()) return;
                  const hasTerminal = hasTerminalAssistantRecord(history.messages, completedTurnId);
                  if (acceptedStreamFailed || hasTerminal) {
                    applyHistoryPage(history, false);
                    if (acceptedStreamFailed && !hasTerminal) {
                      restoreRetryDraftIfTurnWasNotAdmitted(history.messages, completedTurnId);
                      notifyBlocked(t('app.chat.incompleteStreamHistoryRestored'));
                    }
                  } else {
                    notifyBlocked(t('app.chat.historyTerminalRecordMissing'));
                    retainActiveSession = true;
                    reconciliationRequired.value = true;
                  }
                  await initSessions();
                  if (!requestContextIsCurrent()) return;
                  await refreshPendingConfirmation(completedSessionId);
                  if (!requestContextIsCurrent()) return;
                } catch (error) {
                  if (!requestContextIsCurrent()) return;
                  if (isHttpNotFound(error)) {
                    const reconciledDeletedSession = await reconcileAuthoritativeState();
                    if (!requestContextIsCurrent()) return;
                    reportAuthoritativeSessionDeletion(completedSessionId);
                    if (!reconciledDeletedSession) reconciliationRequired.value = true;
                  } else {
                    console.error('[Chat] Failed to reload authoritative history after stream completion:', error);
                    notifyBlocked(t('app.chat.historyReloadAfterSettleFailed'));
                    retainActiveSession = true;
                    reconciliationRequired.value = true;
                  }
                }
              }
            }
          }
        } catch (error) {
          if (!requestContextIsCurrent()) return;
          console.error('[Chat] Failed to confirm normal stream completion:', error);
          retainActiveSession = true;
          reconciliationRequired.value = true;
          const reconciled = await reconcileAuthoritativeState();
          if (!requestContextIsCurrent()) return;
          reconciliationRequired.value = true;
          if (reconciled) {
            notifyBlocked(t('app.chat.stopOutcomeUnknown'));
          }
        } finally {
          if (requestContextIsCurrent()
              && !retainActiveSession && activeStreamSessionId.value === completedSessionId) {
            activeStreamSessionId.value = '';
            activeStreamTurnId.value = '';
            activeStreamAuthToken.value = null;
            historyReplacementWithoutTerminalAllowed.value = false;
            explicitStopRegistrationPending.value = false;
            activeStreamRetryDraft.value = '';
            updateSessionActivity(completedSessionId, false);
          }
          if (requestContextIsCurrent()) isSettlingStream.value = false;
          if (requestContextIsCurrent()
              && !retainActiveSession && !activeStreamSessionId.value) {
            reattachAuthoritativeActiveSession(sessions.value);
          }
        }
      }
    }
  }
};

const handleSend = async () => {
  await submitChatTurn(inputValue.value.trim());
};

const confirmationKindLabel = (kind: ChatConfirmationKind) =>
    t(`app.chat.confirmationKinds.${kind}`);

const handleProtectedConfirmation = async (
    kind: ChatConfirmationKind,
    action: ChatConfirmationAction
) => {
  if (isLoading.value || props.interactionLocked) return;
  const content = action === 'CONFIRM'
      ? t('app.chat.protectedConfirmationAccepted', { action: confirmationKindLabel(kind) })
      : t('app.chat.protectedConfirmationCancelled', { action: confirmationKindLabel(kind) });
  await submitChatTurn(content, { kind, action });
};

const retryPendingConfirmation = () => {
  if (!currentSessionId.value || isLoading.value) return;
  void refreshPendingConfirmation(currentSessionId.value);
};

const handleTaskClick = (text: string) => {
  if (props.interactionLocked) {
    notifyBlocked(t('app.chat.boardInteractionLocked'));
    return;
  }
  refreshBoardContext();
  inputValue.value = text;
  // 可选：聚焦输入框 (如果 textarea 组件有 ref)
  // const textarea = document.querySelector('.modern-textarea') as HTMLTextAreaElement;
  // if (textarea) textarea.focus();
};

const scrollToBottom = (force = false) => {
  nextTick(() => {
    if (!scrollRef.value) return;
    const { scrollTop, scrollHeight, clientHeight } = scrollRef.value;
    // 只有当用户确实在底部，或者强制滚动时，才自动滚动。防止用户回看历史时被强制拉回底部。
    const isNearBottom = scrollHeight - scrollTop - clientHeight < 150;
    if (force || isNearBottom) scrollRef.value.scrollTop = scrollHeight;
  });
};
</script>

<template>
  <div :class="['global-chat-wrapper', { 'global-chat-wrapper--board': props.boardMode }]">

    <transition name="panel-zoom">
      <div
        ref="chatPanelRef"
        v-show="visible"
        data-testid="chat-panel"
        :class="[
          'chat-panel',
          {
            dragging: panelInteraction?.mode === 'drag',
            resizing: panelInteraction?.mode === 'resize',
            'chat-panel--compact': isChatPanelCompact,
            'chat-panel--sidebar-open': isSidebarOpen
          }
        ]"
        :style="chatPanelStyle"
        role="dialog"
        aria-modal="false"
        :aria-label="t('app.aiAssistant')"
      >

        <div :class="['sidebar', { collapsed: !isSidebarOpen }]">
          <div class="sidebar-header">
            <button type="button" class="new-chat-btn"
              :disabled="isSettlingStream || isCreatingSession || isPreparingStreamSession"
              @click="onNewChatClick">
              <PlusOutlined/> <span class="btn-label">{{ t('app.chat.newChat') }}</span>
            </button>
          </div>

          <div class="session-list">
            <div
              v-if="isLoadingSessions && sessions.length === 0"
              class="session-list-state"
              data-testid="chat-session-list-loading"
              role="status"
              aria-live="polite"
            >
              <span>{{ t('app.chat.loadingSessions') }}</span>
              <div class="typing-indicator" aria-hidden="true"><span></span><span></span><span></span></div>
            </div>
            <button
              v-else-if="sessionListLoadFailed && sessions.length === 0"
              type="button"
              class="session-list-state session-list-retry"
              data-testid="chat-session-list-retry"
              @click="initSessions()"
            >
              <span>{{ t('app.chat.loadSessionsFailed') }}</span>
              <span class="session-list-retry__action">{{ t('app.chat.retryLoadSessions') }}</span>
            </button>
            <div
              v-else-if="sessions.length === 0"
              class="session-list-state"
              data-testid="chat-session-list-empty"
            >
              {{ t('app.chat.noSessions') }}
            </div>
            <div
                v-for="session in sessions"
                :key="session.id"
                :class="['session-item', { active: currentSessionId === session.id }]"
            >
              <button
                type="button"
                class="session-select-button"
                :data-testid="`chat-session-${session.id}`"
                :disabled="isSettlingStream || isPreparingStreamSession"
                @click="handleUserSelectSession(session.id, session.active)"
              >
                <MessageOutlined class="item-icon"/>
                <span class="session-copy">
                  <span class="item-title">{{ session.title || t('app.chat.newChat') }}</span>
                  <span
                    v-if="sessionExecutionStatus(session)"
                    class="session-status"
                    :class="sessionStatusClass(session)"
                    :data-testid="session.active ? 'chat-session-active' : 'chat-session-status'"
                    :aria-label="sessionStatusTitle(session)"
                    :title="sessionStatusTitle(session)"
                  >
                    <span class="session-status-dot" aria-hidden="true"></span>
                    <span>{{ sessionExecutionStatus(session) }}</span>
                  </span>
                </span>
              </button>
              <button
                type="button"
                class="delete-btn-wrapper"
                :aria-label="t('app.delete')"
                :title="session.active ? t('app.chat.sessionStillRunning') : t('app.delete')"
                :disabled="isSettlingStream || isPreparingStreamSession || session.active"
                @click.stop="handleDelete(session.id)"
              >
                <DeleteOutlined class="delete-icon"/>
              </button>
            </div>
          </div>

          <div class="sidebar-footer">
            <!-- 移除深色模式切换功能 -->
          </div>
        </div>

        <button
          v-if="isChatPanelCompact && isSidebarOpen"
          type="button"
          class="sidebar-scrim"
          data-testid="chat-sidebar-scrim"
          :aria-label="t('app.collapse')"
          :title="t('app.collapse')"
          @click="isSidebarOpen = false"
        ></button>

        <div class="main-content">
          <div
            class="glass-header"
            data-testid="chat-drag-handle"
            @pointerdown="startPanelDrag"
          >
            <div class="header-left-group">
              <button
                type="button"
                class="control-icon-button sidebar-toggle"
                data-testid="chat-sidebar-toggle"
                :aria-label="isSidebarOpen ? t('app.collapse') : t('app.expand')"
                :title="isSidebarOpen ? t('app.collapse') : t('app.expand')"
                @click="isSidebarOpen = !isSidebarOpen"
              >
                <component :is="isSidebarOpen ? MenuFoldOutlined : MenuUnfoldOutlined" />
              </button>
              <div class="header-title">
                <RobotOutlined class="header-title-icon" />
                <span>{{ t('app.aiAssistant') }}</span>
              </div>
            </div>
            <div class="header-controls">
              <button
                type="button"
                class="control-icon-button control-icon-button--danger"
                data-testid="chat-close"
                :aria-label="t('app.close')"
                :title="t('app.close')"
                @click="chatStore.closeChat()"
              >
                <CloseOutlined />
              </button>
            </div>
          </div>

          <button
            type="button"
            class="chat-resize-handle"
            data-testid="chat-resize-handle"
            :aria-label="t('app.resize')"
            :title="t('app.resize')"
            @pointerdown="startPanelResize"
          />

          <div
            class="messages-viewport"
            ref="scrollRef"
          >
            <div
              v-if="messages.length > 0 && historyHasMore && !isLoadingHistory"
              class="history-pagination"
            >
              <button
                type="button"
                class="history-pagination__button"
                data-testid="chat-load-older"
                :disabled="isLoadingOlderHistory"
                @click="loadOlderHistory"
              >
                {{ isLoadingOlderHistory ? t('app.chat.loadingOlderHistory') : t('app.chat.loadOlderHistory') }}
              </button>
            </div>

            <div
              v-if="historyLoadFailed && currentSessionId"
              class="session-list-state session-list-retry"
              data-testid="chat-history-retry"
              role="alert"
            >
              <span>{{ t('app.chat.networkError') }}</span>
              <button type="button" class="history-pagination__button" @click="handleUserSelectSession(currentSessionId)">
                {{ t('app.retry') }}
              </button>
            </div>

            <div v-else-if="messages.length === 0" class="welcome-screen">
              <div class="brand-logo">
                <div class="logo-inner">
                  <img src="/AI.png" :alt="t('app.aiAssistant')" class="custom-logo-img" />
                </div>
              </div>
              <h3 class="welcome-title">{{ t('app.chat.welcomeTitle') }}</h3>
              <p class="welcome-subtitle">{{ t('app.chat.welcomeSubtitle') }}</p>

              <div class="task-grid">
                <button
                    type="button"
                    v-for="(task, index) in presetTasks"
                    :key="index"
                    class="task-card"
                    @click="handleTaskClick(task.text)"
                    :disabled="interactionLocked"
                    :style="{ animationDelay: `${index * 0.1}s` }"
                >
                  <div class="task-icon">
                    <component :is="task.icon" />
                  </div>
                  <div class="task-info">
                    <div class="task-title">{{ task.title }}</div>
                    <div class="task-desc">{{ task.desc }}</div>
                  </div>
                </button>
              </div>
            </div>

            <div v-if="isLoadingHistory" class="thinking-state" role="status" aria-live="polite">
              <span class="thinking-text">{{ t('app.chat.loadingConversation') }}</span>
              <div class="typing-indicator"><span></span><span></span><span></span></div>
            </div>
            <div v-else-if="isSettlingStream" class="thinking-state" role="status" aria-live="polite">
              <RobotOutlined class="thinking-avatar" />
              <span>{{ t('app.chat.waitingForServerToStop') }}</span>
              <div class="typing-indicator" aria-hidden="true"><span></span><span></span><span></span></div>
            </div>
            <div
              v-else-if="isMonitoringRemoteExecution"
              class="remote-execution-state"
              data-testid="chat-remote-execution"
              role="status"
              aria-live="polite"
            >
              <RobotOutlined class="thinking-avatar" />
              <div>
                <strong>{{ t('app.chat.remoteExecutionTitle') }}</strong>
                <p>{{ remoteActivityCheckFailed
                  ? t('app.chat.remoteExecutionActivityUnavailable')
                  : t('app.chat.remoteExecutionMessage') }}</p>
              </div>
              <div class="typing-indicator" aria-hidden="true"><span></span><span></span><span></span></div>
            </div>
            <div
              v-if="reconciliationRequired"
              class="reconciliation-state"
              data-testid="chat-reconciliation-required"
              role="alert"
            >
              <div>
                <strong>{{ t('app.chat.reconciliationRequiredTitle') }}</strong>
                <p>{{ t('app.chat.reconciliationRequiredMessage') }}</p>
              </div>
              <button
                type="button"
                class="reconciliation-retry"
                data-testid="chat-reconciliation-retry"
                :disabled="isRetryingReconciliation"
                @click="retryAuthoritativeReconciliation"
              >
                {{ isRetryingReconciliation
                  ? t('app.chat.reconciliationRetrying')
                  : t('app.chat.reconciliationRetry') }}
              </button>
            </div>

            <template v-for="(msg, index) in messages" :key="index">
              <div :class="['msg-row', msg.role === 'user' ? 'user-row' : 'ai-row']">
                <div class="avatar-container">
                  <UserOutlined v-if="msg.role === 'user'"/>
                  <RobotOutlined v-else/>
                </div>

                <div class="msg-content-wrapper">
                  <div v-if="msg.role === 'user'" class="msg-body user-msg-body">
                    {{ msg.content }}
                  </div>

                  <article
                    v-else
                    :class="[
                      'msg-body',
                      'vue-markdown-wrapper',
                      {
                        'assistant-pending-body': isStreaming && index === messages.length - 1,
                        'has-execution-trace': messageExecutionTrace(msg, index).length > 0
                      }
                    ]"
                    :aria-busy="isStreaming && index === messages.length - 1 ? 'true' : undefined"
                  >
                    <details
                      v-if="messageExecutionTrace(msg, index).length"
                      class="chat-execution-trace"
                      :open="isExecutionTraceOpen(msg, index)"
                      :data-testid="isActiveAssistantMessage(index) ? 'chat-assistant-pending' : undefined"
                      :role="isActiveAssistantMessage(index) ? 'status' : undefined"
                      :aria-live="isActiveAssistantMessage(index) ? 'polite' : undefined"
                      aria-atomic="false"
                      @toggle="handleExecutionTraceToggle($event, isActiveAssistantMessage(index), msg, index)"
                    >
                      <summary class="chat-execution-header">
                        <span class="chat-execution-chevron" aria-hidden="true">
                          <DownOutlined />
                        </span>
                        <div class="chat-execution-heading">
                          <span class="chat-execution-icon" aria-hidden="true"><CodeOutlined /></span>
                          <div>
                            <strong>{{ t('app.chat.executionTraceTitle') }}</strong>
                            <p>{{ t('app.chat.executionTraceSubtitle') }}</p>
                          </div>
                        </div>
                        <div class="chat-execution-meta">
                          <span
                            class="chat-execution-state"
                            :class="{
                              'is-running': isActiveAssistantMessage(index),
                              'is-stopped': !isActiveAssistantMessage(index)
                                && (messageExecutionTrace(msg, index).some(progress => progress.stage === 'EXECUTION_GUARD')
                                  || msg.executionStatus === 'PARTIAL'
                                  || msg.executionStatus === 'STOPPED'
                                  || msg.executionStatus === 'DISCONNECTED'),
                              'is-failed': !isActiveAssistantMessage(index)
                                && msg.executionStatus === 'FAILED'
                            }"
                          >
                            {{ executionTraceStatus(
                              messageExecutionTrace(msg, index),
                              isActiveAssistantMessage(index),
                              msg.executionStatus,
                              isSettlingAssistantMessage(index)
                            ) }}
                          </span>
                          <span>{{ t('app.chat.progressElapsed', { seconds: messageExecutionElapsed(msg, index) }) }}</span>
                        </div>
                      </summary>
                      <div
                        v-if="traceHasToolResults(messageExecutionTrace(msg, index))"
                        class="chat-execution-metrics"
                      >
                        <span class="is-success">
                          <strong>{{ executionTraceTotals(messageExecutionTrace(msg, index)).successful }}</strong>
                          {{ t('app.chat.executionMetricSucceeded') }}
                        </span>
                        <span class="is-error">
                          <strong>{{ executionTraceTotals(messageExecutionTrace(msg, index)).failed }}</strong>
                          {{ t('app.chat.executionMetricFailed') }}
                        </span>
                        <span class="is-warning">
                          <strong>{{ executionTraceTotals(messageExecutionTrace(msg, index)).unconfirmed }}</strong>
                          {{ t('app.chat.executionMetricUnconfirmed') }}
                        </span>
                      </div>
                      <ol class="chat-execution-events" data-testid="chat-execution-trace">
                        <li
                          v-for="(progress, progressIndex) in messageExecutionTrace(msg, index)"
                          :key="`${progress.stage}-${progress.round || 0}-${progress.toolName || ''}-${progressIndex}`"
                          :class="progressEventClass(progress, isActiveAssistantMessage(index))"
                          :aria-current="isCurrentProgressEvent(progress, isActiveAssistantMessage(index)) ? 'step' : undefined"
                        >
                          <span class="chat-execution-step" aria-hidden="true">{{ progressIndex + 1 }}</span>
                          <div class="chat-execution-event-copy">
                            <strong>{{ progressEventTitle(progress) }}</strong>
                            <!-- Reasoning keeps its line breaks: the backend preserves them
                                 precisely so a decomposition does not read as one run-on line. -->
                            <p :class="{ 'is-reasoning-copy': progress.stage === 'REASONING' }">{{ progressEventDetail(progress) }}</p>
                          </div>
                          <span
                            v-if="progressEventStatus(progress)"
                            class="chat-execution-outcome"
                          >
                            {{ progressEventStatus(progress) }}
                          </span>
                        </li>
                      </ol>
                    </details>
                    <div
                      v-else-if="msg.executionStatus"
                      class="chat-terminal-status"
                      data-testid="chat-terminal-status"
                    >
                      <span
                        class="chat-execution-state"
                        :class="{
                          'is-stopped': msg.executionStatus === 'PARTIAL'
                            || msg.executionStatus === 'STOPPED'
                            || msg.executionStatus === 'DISCONNECTED',
                          'is-failed': msg.executionStatus === 'FAILED'
                        }"
                      >
                        {{ executionTraceStatus([], false, msg.executionStatus) }}
                      </span>
                      <span>{{ t('app.chat.progressElapsed', { seconds: msg.executionElapsedSeconds ?? 0 }) }}</span>
                    </div>
                    <ChatMarkdown v-if="msg.content" :source="getProcessedContent(msg.content) || ''" />
                  </article>

                  <div v-if="msg.role === 'assistant' && msg.content && !isStreaming" class="msg-actions">
                    <button
                      type="button"
                      class="action-btn-small"
                      :aria-label="t('app.chat.copyAll')"
                      :title="t('app.chat.copyAll')"
                      @click="copyFullMessage(msg.content)"
                    >
                      <CopyOutlined />
                    </button>
                  </div>

                </div>
              </div>
            </template>
            <div class="scroll-spacer"></div>
          </div>

          <div class="input-floating-area">
            <div
              v-if="pendingConfirmationLoadFailed"
              class="protected-confirmation is-load-error"
              data-testid="chat-confirmation-load-error"
            >
              <div class="protected-confirmation__copy">
                <SafetyCertificateOutlined aria-hidden="true" />
                <span>{{ t('app.chat.confirmationLoadFailed') }}</span>
              </div>
              <div class="protected-confirmation__actions">
                <button
                  type="button"
                  class="protected-confirmation__button"
                  :disabled="interactionLocked || isLoading"
                  @click="retryPendingConfirmation"
                >
                  {{ t('app.retry') }}
                </button>
              </div>
            </div>
            <div
              v-for="kind in pendingConfirmationKinds"
              :key="kind"
              class="protected-confirmation"
              data-testid="chat-protected-confirmation"
            >
              <div class="protected-confirmation__copy">
                <SafetyCertificateOutlined aria-hidden="true" />
                <span>{{ t('app.chat.protectedConfirmationPrompt', {
                  action: confirmationKindLabel(kind)
                }) }}</span>
              </div>
              <div class="protected-confirmation__actions">
                <button
                  type="button"
                  class="protected-confirmation__button is-cancel"
                  :disabled="interactionLocked || isLoading"
                  @click="handleProtectedConfirmation(kind, 'CANCEL')"
                >
                  <CloseOutlined />
                  {{ t('app.cancel') }}
                </button>
                <button
                  type="button"
                  class="protected-confirmation__button is-confirm"
                  :disabled="interactionLocked || isLoading"
                  @click="handleProtectedConfirmation(kind, 'CONFIRM')"
                >
                  <CheckOutlined />
                  {{ t('app.confirm') }}
                </button>
              </div>
            </div>
            <div class="input-card">
              <textarea
                v-model="inputValue"
                data-testid="chat-input"
                :placeholder="t('app.chat.inputPlaceholder')"
                :aria-label="t('app.chat.messageInput')"
                :disabled="interactionLocked || isLoading || historyLoadFailed"
                rows="2"
                :maxlength="REQUEST_LIMITS.chatContentCharacters"
                @keydown.ctrl.enter="handleSend"
                class="modern-textarea"
              ></textarea>
              <div class="input-actions">
                <div class="left-tools">
                  <button
                    type="button"
                    :class="['tool-icon', { active: isRecording }]"
                    :aria-pressed="isRecording"
                    :aria-label="isRecording ? t('app.chat.stopVoiceInput') : t('app.chat.startVoiceInput')"
                    :title="isRecording ? t('app.chat.stopVoiceInput') : t('app.chat.startVoiceInput')"
                    @click="isRecording ? stopListening() : startListening()"
                    :disabled="interactionLocked || isLoading || historyLoadFailed"
                  >
                    <AudioOutlined/>
                  </button>
                </div>
                <div class="right-tools">
                  <button
                    v-if="isStreaming || isMonitoringRemoteExecution"
                    type="button"
                    class="action-btn stop"
                    data-testid="chat-stop"
                    :aria-label="t(isMonitoringRemoteExecution
                      ? 'app.chat.stopRemoteExecution'
                      : 'app.chat.stopResponse')"
                    :title="t(isMonitoringRemoteExecution
                      ? 'app.chat.stopRemoteExecution'
                      : 'app.chat.stopResponse')"
                    @click="handleStop"
                  ><StopOutlined/></button>
                  <button
                    v-else
                    type="button"
                    class="action-btn send"
                    data-testid="chat-send"
                    :aria-label="t('app.chat.sendMessage')"
                    @click="handleSend"
                    :disabled="interactionLocked || !inputValue.trim() || isLoading || historyLoadFailed"
                    :title="interactionLocked ? t('app.chat.boardInteractionLocked') : undefined"
                  ><SendOutlined/></button>
                </div>
              </div>
            </div>
          </div>
        </div>
      </div>
    </transition>
  </div>
</template>

<style scoped>
.global-chat-wrapper {
  position: fixed;
  inset: 0;
  z-index: var(--z-chat-panel);
  pointer-events: none;
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
  --chat-accent: #7c3aed;
  --chat-accent-strong: #6d28d9;
  --chat-success: #10b981;
  --chat-bg: color-mix(in srgb, var(--surface-overlay, rgba(255, 255, 255, 0.94)) 94%, transparent);
  --chat-sidebar-bg: color-mix(in srgb, var(--surface-panel, #ffffff) 92%, var(--surface-control, #f1f5f9));
  --chat-input-bg: var(--surface-elevated, #ffffff);
  --chat-control-bg: var(--surface-control, #f1f5f9);
  --chat-text: var(--text, #0f172a);
  --chat-muted: var(--text-muted, #64748b);
  --chat-border: var(--border, #e2e8f0);
  --chat-shadow: 0 24px 70px rgba(15, 23, 42, 0.24);
  --chat-user-bg: color-mix(in srgb, #7c3aed 12%, var(--surface-control, #f1f5f9));
  --chat-ai-bg: color-mix(in srgb, var(--surface-elevated, #ffffff) 86%, transparent);
  --chat-safe-left: 1rem;
  --chat-safe-right: 1rem;
}

:global(:root[data-theme='dark'] .global-chat-wrapper) {
  --chat-shadow: 0 28px 80px rgba(2, 6, 23, 0.54);
  --chat-user-bg: color-mix(in srgb, #8b5cf6 20%, var(--surface-control, #1e293b));
  --chat-ai-bg: color-mix(in srgb, var(--surface-elevated, #111827) 92%, transparent);
}

.global-chat-wrapper--board {
  --chat-safe-left: calc(20rem + 1rem);
  --chat-safe-right: calc(20rem + 1rem);
}

@media (min-width: 1280px) {
  .global-chat-wrapper--board {
    --chat-safe-right: calc(20rem + 8.25rem + 2rem);
  }
}

.chat-panel {
  position: fixed;
  top: calc(4rem + 0.85rem);
  right: var(--chat-safe-right);
  width: min(31rem, calc(100vw - var(--chat-safe-left) - var(--chat-safe-right)));
  height: min(42rem, calc(100dvh - 5.75rem));
  min-width: min(20rem, calc(100vw - 1.5rem));
  min-height: min(22rem, max(16.25rem, calc(100dvh - 17.5rem)));
  display: flex;
  pointer-events: auto;
  overflow: hidden;
  border: 1px solid var(--chat-border);
  border-radius: 1rem;
  background: var(--chat-bg);
  color: var(--chat-text);
  box-shadow: var(--chat-shadow);
  backdrop-filter: blur(18px);
  transition: top 0.28s ease, right 0.28s ease, bottom 0.28s ease, left 0.28s ease, width 0.28s ease, height 0.28s ease, border-radius 0.28s ease, box-shadow 0.28s ease;
}

.chat-panel.dragging,
.chat-panel.resizing {
  transition: none;
}

.panel-zoom-enter-active,
.panel-zoom-leave-active {
  transition: opacity 0.18s ease, transform 0.18s ease;
}

.panel-zoom-enter-from,
.panel-zoom-leave-to {
  opacity: 0;
  transform: translateY(0.5rem) scale(0.98);
}

.sidebar {
  width: clamp(12.5rem, 22%, 16rem);
  flex: 0 0 auto;
  display: flex;
  flex-direction: column;
  overflow: hidden;
  border-right: 1px solid var(--chat-border);
  background: var(--chat-sidebar-bg);
  white-space: nowrap;
  transition: width 0.22s ease, opacity 0.16s ease;
}

.sidebar.collapsed {
  width: 0;
  border-right: 0;
  opacity: 0;
}

.sidebar-header {
  padding: 0.75rem;
}

.new-chat-btn {
  width: 100%;
  min-height: 2.25rem;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 0.45rem;
  border: 1px solid color-mix(in srgb, var(--chat-accent) 40%, var(--chat-border));
  border-radius: 0.65rem;
  background: color-mix(in srgb, var(--chat-accent) 12%, transparent);
  color: var(--chat-text);
  cursor: pointer;
  font: inherit;
  font-size: 0.85rem;
  font-weight: 700;
  transition: background 0.16s ease, border-color 0.16s ease, transform 0.16s ease;
}

.new-chat-btn:hover {
  border-color: var(--chat-accent);
  background: color-mix(in srgb, var(--chat-accent) 18%, transparent);
}

.new-chat-btn:active {
  transform: translateY(1px);
}

.session-list {
  flex: 1;
  min-height: 0;
  overflow-y: auto;
  padding: 0 0.65rem 0.9rem;
}

.session-list-state {
  width: 100%;
  min-height: 5rem;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  gap: 0.5rem;
  border: 1px dashed color-mix(in srgb, var(--chat-border) 82%, transparent);
  border-radius: 0.65rem;
  background: color-mix(in srgb, var(--chat-control-bg) 42%, transparent);
  color: var(--chat-muted);
  padding: 0.75rem;
  font: inherit;
  font-size: 0.75rem;
  line-height: 1.45;
  text-align: center;
  white-space: normal;
}

.session-list-retry {
  cursor: pointer;
}

.session-list-retry:hover,
.session-list-retry:focus-visible {
  outline: none;
  border-color: color-mix(in srgb, var(--chat-accent) 54%, var(--chat-border));
  color: var(--chat-text);
}

.session-list-retry__action {
  color: var(--chat-accent);
  font-weight: 750;
}

.session-item {
  min-width: 0;
  display: flex;
  align-items: center;
  gap: 0.55rem;
  margin-bottom: 0.25rem;
  padding: 0.6rem 0.55rem;
  border: 1px solid transparent;
  border-radius: 0.6rem;
  color: var(--chat-muted);
  font-size: 0.82rem;
  transition: background 0.16s ease, border-color 0.16s ease, color 0.16s ease;
}

.session-item:hover,
.session-item:focus-within {
  outline: none;
  border-color: var(--chat-border);
  background: color-mix(in srgb, var(--chat-control-bg) 76%, transparent);
  color: var(--chat-text);
}

.session-select-button {
  min-width: 0;
  flex: 1;
  display: flex;
  align-items: center;
  gap: 0.55rem;
  padding: 0;
  border: 0;
  outline: 0;
  background: transparent;
  color: inherit;
  cursor: pointer;
  font: inherit;
  text-align: left;
}

.session-select-button:focus-visible {
  border-radius: 0.35rem;
  outline: 2px solid color-mix(in srgb, var(--chat-accent) 72%, transparent);
  outline-offset: 2px;
}

.session-item.active {
  border-color: color-mix(in srgb, var(--chat-accent) 46%, var(--chat-border));
  background: color-mix(in srgb, var(--chat-accent) 14%, var(--chat-control-bg));
  color: var(--chat-text);
}

.item-icon {
  flex: 0 0 auto;
  color: var(--chat-accent);
}

.item-title {
  display: block;
  min-width: 0;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.session-copy {
  min-width: 0;
  flex: 1;
  display: flex;
  flex-direction: column;
  gap: 0.15rem;
}

.session-status {
  min-width: 0;
  display: inline-flex;
  align-items: center;
  gap: 0.3rem;
  color: var(--chat-muted);
  font-size: 0.7rem;
  line-height: 1.25;
  white-space: normal;
}

.session-status-dot {
  width: 0.42rem;
  height: 0.42rem;
  flex: 0 0 auto;
  border-radius: 50%;
  background: currentColor;
}

.session-status.is-running {
  color: var(--chat-success);
}

.session-status.is-warning {
  color: #d97706;
}

.session-status.is-failed {
  color: #dc2626;
}

.session-status.is-unread {
  color: var(--chat-accent);
  font-weight: 750;
}

.session-status.is-running .session-status-dot {
  background: var(--chat-success);
  box-shadow: 0 0 0 0.2rem color-mix(in srgb, var(--chat-success) 18%, transparent);
}

.delete-btn-wrapper {
  width: 1.75rem;
  height: 1.75rem;
  flex: 0 0 auto;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  border: 0;
  border-radius: 0.45rem;
  background: transparent;
  color: var(--chat-muted);
  cursor: pointer;
  opacity: 0;
  transition: opacity 0.16s ease, background 0.16s ease, color 0.16s ease;
}

.session-item:hover .delete-btn-wrapper,
.session-item:focus-within .delete-btn-wrapper {
  opacity: 1;
}

.delete-btn-wrapper:hover {
  background: color-mix(in srgb, #ef4444 14%, transparent);
  color: #ef4444;
}

.sidebar-footer {
  display: none;
}

.main-content {
  flex: 1;
  min-width: 0;
  display: flex;
  flex-direction: column;
  position: relative;
  background: color-mix(in srgb, var(--chat-bg) 92%, transparent);
}

.chat-panel--compact .main-content {
  flex: 0 0 100%;
  width: 100%;
}

.chat-panel--compact .sidebar {
  position: absolute;
  inset: 0 auto 0 0;
  z-index: 20;
  width: clamp(13rem, 42%, 15.5rem);
  max-width: calc(100% - 4rem);
  border-right: 1px solid var(--chat-border);
  box-shadow: 16px 0 30px rgba(15, 23, 42, 0.22);
  transform: translateX(0);
  transition: transform 0.22s ease, opacity 0.16s ease;
}

.chat-panel--compact .sidebar.collapsed {
  width: clamp(13rem, 42%, 15.5rem);
  max-width: calc(100% - 4rem);
  border-right: 1px solid var(--chat-border);
  opacity: 0;
  pointer-events: none;
  transform: translateX(-102%);
}

.sidebar-scrim {
  position: absolute;
  inset: 0;
  z-index: 19;
  border: 0;
  background: color-mix(in srgb, var(--chat-bg) 48%, transparent);
  cursor: default;
}

.chat-panel--compact .sidebar-scrim {
  backdrop-filter: blur(1px);
}

.glass-header {
  flex: 0 0 auto;
  min-height: 3.25rem;
  display: flex;
  align-items: center;
  justify-content: space-between;
  flex-wrap: wrap;
  gap: 0.75rem;
  padding: 0.7rem 0.85rem;
  border-bottom: 1px solid var(--chat-border);
  background: color-mix(in srgb, var(--chat-bg) 88%, transparent);
  cursor: grab;
  touch-action: none;
  user-select: none;
}

.chat-panel.dragging .glass-header {
  cursor: grabbing;
}

.header-left-group {
  min-width: 0;
  display: flex;
  align-items: center;
  gap: 0.65rem;
}

.header-title {
  min-width: 0;
  display: flex;
  align-items: center;
  gap: 0.45rem;
  color: var(--chat-text);
  font-size: 0.95rem;
  font-weight: 800;
}

.header-title-icon {
  color: var(--chat-accent);
}

.header-controls {
  display: flex;
  align-items: center;
  gap: 0.35rem;
}

.control-icon-button {
  width: 2rem;
  height: 2rem;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  border: 1px solid transparent;
  border-radius: 0.6rem;
  background: transparent;
  color: var(--chat-muted);
  cursor: pointer;
  font: inherit;
  transition: background 0.16s ease, border-color 0.16s ease, color 0.16s ease;
}

.control-icon-button:hover,
.control-icon-button:focus-visible {
  outline: none;
  border-color: var(--chat-border);
  background: var(--chat-control-bg);
  color: var(--chat-text);
}

.control-icon-button--danger:hover,
.control-icon-button--danger:focus-visible {
  color: #ef4444;
}

.chat-resize-handle {
  position: absolute;
  right: 0;
  bottom: 0;
  z-index: 6;
  width: 2rem;
  height: 2rem;
  border: 0;
  border-radius: 0.35rem;
  background:
      linear-gradient(135deg, transparent 0 45%, color-mix(in srgb, var(--chat-muted) 64%, transparent) 46% 54%, transparent 55%),
      linear-gradient(135deg, transparent 0 62%, color-mix(in srgb, var(--chat-muted) 64%, transparent) 63% 71%, transparent 72%);
  cursor: nwse-resize;
  opacity: 0.65;
  touch-action: none;
}

.chat-resize-handle:hover,
.chat-resize-handle:focus-visible {
  outline: none;
  opacity: 1;
  background-color: color-mix(in srgb, var(--chat-control-bg) 70%, transparent);
}

.messages-viewport {
  flex: 1;
  min-height: 0;
  overflow-y: auto;
  padding: 0.9rem 1rem 1rem;
  scroll-behavior: smooth;
}

.scroll-spacer {
  height: 0.25rem;
  flex-shrink: 0;
}

.welcome-screen {
  min-height: 100%;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: flex-start;
  max-width: 46rem;
  margin: 0 auto;
  padding: 0.85rem 0.15rem 1rem;
  color: var(--chat-text);
  text-align: center;
}

.brand-logo {
  margin-bottom: 0.65rem;
}

.logo-inner {
  width: 3.25rem;
  height: 3.25rem;
  display: flex;
  align-items: center;
  justify-content: center;
  overflow: hidden;
  border: 1px solid color-mix(in srgb, var(--chat-accent) 34%, var(--chat-border));
  border-radius: 1rem;
  background: color-mix(in srgb, var(--chat-accent) 12%, var(--chat-control-bg));
  box-shadow: 0 12px 28px rgba(124, 58, 237, 0.18);
}

.custom-logo-img {
  width: 125%;
  height: 125%;
  object-fit: contain;
}

.welcome-title {
  margin: 0;
  color: var(--chat-text);
  font-size: 1.05rem;
  font-weight: 850;
}

.welcome-subtitle {
  max-width: 26rem;
  margin: 0.3rem 0 0.85rem;
  color: var(--chat-muted);
  font-size: 0.8rem;
  line-height: 1.5;
}

.task-grid {
  width: 100%;
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(min(16rem, 100%), 1fr));
  gap: 0.55rem;
}

.task-card {
  width: 100%;
  position: relative;
  overflow: hidden;
  display: flex;
  align-items: flex-start;
  gap: 0.6rem;
  border: 1px solid var(--chat-border);
  border-radius: 0.8rem;
  background: var(--chat-ai-bg);
  color: var(--chat-text);
  cursor: pointer;
  padding: 0.65rem;
  text-align: left;
  font: inherit;
  transition: border-color 0.16s ease, background 0.16s ease, transform 0.16s ease, box-shadow 0.16s ease;
}

.task-card:hover {
  border-color: color-mix(in srgb, var(--chat-accent) 62%, var(--chat-border));
  background: color-mix(in srgb, var(--chat-accent) 9%, var(--chat-ai-bg));
  box-shadow: 0 10px 24px rgba(15, 23, 42, 0.12);
  transform: translateY(-1px);
}

.task-card:disabled {
  cursor: not-allowed;
  opacity: 0.58;
}

.task-card:disabled:hover {
  border-color: var(--chat-border);
  background: var(--chat-ai-bg);
  box-shadow: none;
  transform: none;
}

.task-icon {
  width: 2rem;
  height: 2rem;
  flex: 0 0 auto;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  border-radius: 0.65rem;
  background: color-mix(in srgb, var(--chat-accent) 14%, var(--chat-control-bg));
  color: var(--chat-accent);
  font-size: 1rem;
}

.task-info {
  min-width: 0;
  flex: 1;
}

.task-title {
  color: var(--chat-text);
  font-size: 0.83rem;
  font-weight: 800;
}

.task-desc {
  margin-top: 0.15rem;
  color: var(--chat-muted);
  font-size: 0.7rem;
  line-height: 1.35;
}

.msg-row {
  width: 100%;
  max-width: 48rem;
  display: flex;
  gap: 0.65rem;
  margin: 0 auto 1rem;
}

.history-pagination {
  display: flex;
  justify-content: center;
  margin: 0 auto 0.8rem;
}

.history-pagination__button {
  border: 0;
  background: transparent;
  color: var(--chat-accent);
  cursor: pointer;
  font: inherit;
  font-size: 0.78rem;
  font-weight: 700;
  padding: 0.35rem 0.55rem;
}

.history-pagination__button:disabled {
  cursor: wait;
  opacity: 0.58;
}

.ai-row {
  flex-direction: row;
}

.user-row {
  flex-direction: row-reverse;
}

.avatar-container {
  width: 2rem;
  height: 2rem;
  flex: 0 0 auto;
  display: flex;
  align-items: center;
  justify-content: center;
  border-radius: 0.65rem;
  font-size: 0.85rem;
}

.ai-row .avatar-container {
  background: color-mix(in srgb, var(--chat-success) 16%, var(--chat-control-bg));
  color: var(--chat-success);
}

.user-row .avatar-container {
  background: color-mix(in srgb, var(--chat-accent) 16%, var(--chat-control-bg));
  color: var(--chat-accent);
}

.msg-content-wrapper {
  flex: 1;
  min-width: 0;
  display: flex;
  flex-direction: column;
}

.msg-body {
  min-width: 0;
  border: 1px solid var(--chat-border);
  border-radius: 0.9rem;
  padding: 0.7rem 0.85rem;
  color: var(--chat-text);
  font-size: 0.88rem;
  line-height: 1.6;
}

.user-msg-body {
  max-width: min(34rem, 100%);
  align-self: flex-end;
  border-color: color-mix(in srgb, var(--chat-accent) 32%, var(--chat-border));
  background: var(--chat-user-bg);
  white-space: pre-wrap;
  overflow-wrap: anywhere;
}

.vue-markdown-wrapper {
  max-width: 100%;
  background: var(--chat-ai-bg);
  overflow-wrap: anywhere;
}

.assistant-pending-body {
  width: fit-content;
  min-width: 8.5rem;
  max-width: 100%;
  align-self: flex-start;
  padding: 0.55rem 0.75rem;
  background: var(--chat-ai-bg);
}

.msg-body.has-execution-trace,
.assistant-pending-body.has-execution-trace {
  width: 100%;
  max-width: 100%;
  align-self: stretch;
}

.msg-actions {
  display: flex;
  gap: 0.35rem;
  margin-top: 0.25rem;
  opacity: 0;
  transition: opacity 0.16s ease;
}

.msg-row:hover .msg-actions,
.msg-row:focus-within .msg-actions {
  opacity: 1;
}

.action-btn-small {
  width: 1.75rem;
  height: 1.75rem;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  border: 1px solid transparent;
  border-radius: 0.45rem;
  background: transparent;
  color: var(--chat-muted);
  cursor: pointer;
}

.action-btn-small:hover,
.action-btn-small:focus-visible {
  outline: none;
  border-color: var(--chat-border);
  background: var(--chat-control-bg);
  color: var(--chat-text);
}

.thinking-state {
  display: flex;
  align-items: center;
  gap: 0.55rem;
  color: var(--chat-muted);
  font-size: 0.8rem;
}

.remote-execution-state {
  max-width: 48rem;
  margin: 0.75rem auto;
  padding: 0.7rem 0;
  display: grid;
  grid-template-columns: auto minmax(0, 1fr) auto;
  align-items: center;
  gap: 0.65rem;
  border-top: 1px solid color-mix(in srgb, var(--chat-accent) 42%, var(--chat-border));
  border-bottom: 1px solid color-mix(in srgb, var(--chat-accent) 42%, var(--chat-border));
  color: var(--chat-text);
  font-size: 0.8rem;
}

.remote-execution-state p {
  margin: 0.2rem 0 0;
  color: var(--chat-muted);
}

.reconciliation-state {
  max-width: 48rem;
  margin: 0.75rem auto;
  padding: 0.75rem;
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 0.75rem;
  border: 1px solid color-mix(in srgb, #ef4444 45%, var(--chat-border));
  border-radius: 0.65rem;
  background: color-mix(in srgb, #ef4444 8%, var(--chat-ai-bg));
  color: var(--chat-text);
  font-size: 0.8rem;
}

.chat-execution-trace {
  width: 100%;
  min-width: 0;
  color: var(--chat-text);
  font-size: 0.8rem;
  overflow-wrap: anywhere;
}

.chat-execution-header {
  display: grid;
  grid-template-columns: 1.75rem minmax(0, 1fr) auto;
  align-items: center;
  gap: 0.65rem;
  cursor: pointer;
  min-height: 3.15rem;
  padding: 0.2rem 0 0.65rem;
  list-style: none;
  border-bottom: 1px solid var(--chat-border);
}

.chat-execution-header::-webkit-details-marker {
  display: none;
}

.chat-execution-chevron {
  width: 1.75rem;
  height: 1.75rem;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  border: 1px solid var(--chat-border);
  border-radius: 0.4rem;
  color: var(--chat-muted);
  transition: transform 0.16s ease, color 0.16s ease, border-color 0.16s ease;
}

.chat-execution-trace[open] .chat-execution-chevron {
  transform: rotate(180deg);
  border-color: color-mix(in srgb, var(--chat-accent) 45%, var(--chat-border));
  color: var(--chat-accent);
}

.chat-execution-heading {
  min-width: 0;
  display: flex;
  align-items: center;
  gap: 0.55rem;
}

.chat-execution-heading > div {
  min-width: 0;
}

.chat-execution-icon {
  flex: 0 0 auto;
  width: 1.75rem;
  height: 1.75rem;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  border-radius: 0.4rem;
  background: color-mix(in srgb, var(--chat-accent) 11%, var(--chat-control-bg));
  color: var(--chat-accent);
}

.chat-execution-heading strong {
  display: block;
  font-size: 0.88rem;
  line-height: 1.3;
}

.chat-execution-heading p,
.chat-execution-event-copy p {
  margin: 0.12rem 0 0;
  color: var(--chat-muted);
  font-weight: 400;
  line-height: 1.45;
}

/* Reasoning is the one entry carrying an argument rather than a status, so it keeps the model's
   paragraph and list breaks and reads at full contrast instead of as muted metadata. */
.chat-execution-event-copy p.is-reasoning-copy {
  white-space: pre-wrap;
  color: var(--chat-text);
  line-height: 1.55;
}

.chat-execution-meta {
  display: flex;
  align-items: flex-end;
  flex-direction: column;
  gap: 0.2rem;
  color: var(--chat-muted);
  font-variant-numeric: tabular-nums;
  white-space: nowrap;
}

.chat-execution-state {
  padding: 0.1rem 0.4rem;
  border: 1px solid var(--chat-border);
  border-radius: 0.35rem;
  background: var(--chat-control-bg);
  color: var(--chat-muted);
  font-size: 0.72rem;
  font-weight: 700;
}

.chat-execution-state.is-running {
  border-color: color-mix(in srgb, var(--chat-accent) 48%, var(--chat-border));
  color: var(--chat-accent);
}

.chat-execution-state.is-stopped {
  border-color: color-mix(in srgb, #d97706 48%, var(--chat-border));
  color: #b45309;
}

.chat-execution-state.is-failed {
  border-color: color-mix(in srgb, #dc2626 48%, var(--chat-border));
  color: #dc2626;
}

.chat-terminal-status {
  display: flex;
  align-items: center;
  gap: 0.5rem;
  margin-bottom: 0.65rem;
  color: var(--chat-muted);
  font-size: 0.75rem;
}

.chat-execution-metrics {
  display: flex;
  flex-wrap: wrap;
  gap: 0.45rem;
  padding: 0.6rem 0;
  border-bottom: 1px solid var(--chat-border);
}

.chat-execution-metrics span {
  display: inline-flex;
  align-items: baseline;
  gap: 0.25rem;
  padding: 0.18rem 0.45rem;
  border-radius: 0.35rem;
  background: var(--chat-control-bg);
  color: var(--chat-muted);
}

.chat-execution-metrics strong {
  color: var(--chat-text);
  font-size: 0.85rem;
  font-variant-numeric: tabular-nums;
}

.chat-execution-metrics .is-success strong {
  color: var(--chat-success);
}

.chat-execution-metrics .is-warning strong {
  color: #d97706;
}

.chat-execution-metrics .is-error strong {
  color: #dc2626;
}

.chat-execution-events {
  max-height: min(22rem, 48vh);
  margin: 0;
  padding: 0;
  overflow-y: auto;
  list-style: none;
  scrollbar-width: thin;
}

.chat-execution-trace + .chat-markdown-stub,
.chat-execution-trace + :deep(.markdown-body) {
  margin-top: 0.75rem;
}

.chat-execution-events li {
  display: grid;
  grid-template-columns: 1.55rem minmax(0, 1fr) auto;
  align-items: center;
  gap: 0.65rem;
  min-height: 3.2rem;
  padding: 0.55rem 0.15rem;
  border-bottom: 1px solid color-mix(in srgb, var(--chat-border) 65%, transparent);
  color: var(--chat-muted);
  line-height: 1.45;
}

.chat-execution-events li:last-child {
  border-bottom: 0;
}

.chat-execution-events li.is-current {
  color: var(--chat-text);
  background: color-mix(in srgb, var(--chat-accent) 5%, transparent);
}

.chat-execution-step {
  width: 1.4rem;
  height: 1.4rem;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  border: 1px solid var(--chat-border);
  border-radius: 50%;
  background: var(--chat-control-bg);
  color: var(--chat-muted);
  font-size: 0.7rem;
  font-weight: 700;
  font-variant-numeric: tabular-nums;
}

.chat-execution-event-copy {
  min-width: 0;
}

.chat-execution-event-copy strong {
  display: block;
  color: var(--chat-text);
  font-size: 0.82rem;
  line-height: 1.35;
}

.chat-execution-outcome {
  justify-self: end;
  padding: 0.12rem 0.4rem;
  border: 1px solid var(--chat-border);
  border-radius: 0.35rem;
  background: var(--chat-control-bg);
  color: var(--chat-muted);
  font-size: 0.7rem;
  font-weight: 700;
  white-space: nowrap;
}

.chat-execution-events li.is-success .chat-execution-step,
.chat-execution-events li.is-success .chat-execution-outcome {
  border-color: color-mix(in srgb, var(--chat-success) 48%, var(--chat-border));
  color: var(--chat-success);
}

.chat-execution-events li.is-warning .chat-execution-step,
.chat-execution-events li.is-warning .chat-execution-outcome {
  border-color: color-mix(in srgb, #d97706 48%, var(--chat-border));
  color: #b45309;
}

.chat-execution-events li.is-error .chat-execution-step,
.chat-execution-events li.is-error .chat-execution-outcome {
  border-color: color-mix(in srgb, #dc2626 48%, var(--chat-border));
  color: #dc2626;
}

.chat-execution-events li.is-reasoning .chat-execution-step {
  border-color: color-mix(in srgb, var(--chat-accent) 48%, var(--chat-border));
  background: color-mix(in srgb, var(--chat-accent) 9%, var(--chat-control-bg));
  color: var(--chat-accent);
}

.reconciliation-state p {
  margin: 0.2rem 0 0;
  color: var(--chat-muted);
}

.reconciliation-retry {
  flex: 0 0 auto;
  min-height: 2rem;
  padding: 0.35rem 0.65rem;
  border: 1px solid var(--chat-accent);
  border-radius: 0.5rem;
  background: var(--chat-accent);
  color: #fff;
  cursor: pointer;
  font: inherit;
  font-weight: 700;
}

.reconciliation-retry:disabled {
  cursor: wait;
  opacity: 0.65;
}

.input-floating-area {
  position: relative;
  z-index: 2;
  flex: 0 0 auto;
  padding: 0.85rem 1rem 1rem;
  background: linear-gradient(to top, var(--chat-bg) 86%, transparent);
}

.protected-confirmation {
  max-width: 48rem;
  margin: 0 auto 0.55rem;
  display: flex;
  align-items: center;
  justify-content: space-between;
  flex-wrap: wrap;
  gap: 0.75rem;
  border: 1px solid color-mix(in srgb, #dc2626 45%, var(--chat-border));
  border-radius: 0.65rem;
  background: color-mix(in srgb, #fff1f2 88%, var(--chat-input-bg));
  color: color-mix(in srgb, #991b1b 84%, var(--chat-text));
  padding: 0.65rem 0.75rem;
  box-shadow: 0 10px 28px rgba(127, 29, 29, 0.14);
}

.protected-confirmation.is-load-error {
  border-color: color-mix(in srgb, #d97706 48%, var(--chat-border));
  background: color-mix(in srgb, #fffbeb 88%, var(--chat-input-bg));
  color: color-mix(in srgb, #92400e 84%, var(--chat-text));
}

.protected-confirmation__copy,
.protected-confirmation__actions,
.protected-confirmation__button {
  display: flex;
  align-items: center;
}

.protected-confirmation__copy {
  min-width: 0;
  gap: 0.5rem;
  font-size: 0.82rem;
  font-weight: 650;
}

.protected-confirmation__actions {
  flex-shrink: 0;
  gap: 0.4rem;
}

.protected-confirmation__button {
  gap: 0.3rem;
  border: 1px solid var(--chat-border);
  border-radius: 0.45rem;
  padding: 0.4rem 0.6rem;
  background: var(--chat-input-bg);
  color: var(--chat-text);
  font: inherit;
  font-size: 0.78rem;
  font-weight: 700;
  cursor: pointer;
}

.protected-confirmation__button.is-confirm {
  border-color: #b91c1c;
  background: #b91c1c;
  color: #fff;
}

.protected-confirmation__button:disabled {
  cursor: not-allowed;
  opacity: 0.55;
}

.input-card {
  max-width: 48rem;
  margin: 0 auto;
  display: flex;
  flex-direction: column;
  border: 1px solid var(--chat-border);
  border-radius: 0.9rem;
  background: var(--chat-input-bg);
  box-shadow: 0 14px 35px rgba(15, 23, 42, 0.16);
  padding: 0.65rem;
}

.input-card:focus-within {
  border-color: color-mix(in srgb, var(--chat-accent) 54%, var(--chat-border));
}

.modern-textarea {
  width: 100%;
  min-height: 2.7rem;
  max-height: min(8rem, 28vh);
  resize: vertical;
  border: 0;
  outline: none;
  background: transparent;
  color: var(--chat-text);
  font: inherit;
  font-size: 0.9rem;
  line-height: 1.45;
}

.modern-textarea::placeholder {
  color: color-mix(in srgb, var(--chat-muted) 78%, transparent);
}

.modern-textarea:disabled {
  cursor: not-allowed;
  opacity: 0.62;
}

.input-actions {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-top: 0.45rem;
}

.left-tools,
.right-tools {
  display: flex;
  align-items: center;
  gap: 0.4rem;
}

.tool-icon,
.action-btn {
  width: 2rem;
  height: 2rem;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  border: 1px solid transparent;
  border-radius: 0.6rem;
  background: transparent;
  color: var(--chat-muted);
  cursor: pointer;
  font: inherit;
  transition: background 0.16s ease, border-color 0.16s ease, color 0.16s ease, transform 0.16s ease;
}

.tool-icon:hover,
.tool-icon:focus-visible {
  outline: none;
  border-color: var(--chat-border);
  background: var(--chat-control-bg);
  color: var(--chat-text);
}

.tool-icon.active {
  color: #ef4444;
}

.action-btn.send {
  border-color: var(--chat-accent);
  background: var(--chat-accent);
  color: #fff;
}

.action-btn.send:hover:not(:disabled),
.action-btn.send:focus-visible:not(:disabled) {
  outline: none;
  background: var(--chat-accent-strong);
  transform: translateY(-1px);
}

.action-btn.send:disabled {
  border-color: var(--chat-border);
  background: var(--chat-control-bg);
  color: var(--chat-muted);
  cursor: default;
}

.action-btn.stop {
  border-color: color-mix(in srgb, #ef4444 44%, var(--chat-border));
  background: color-mix(in srgb, #ef4444 10%, transparent);
  color: #ef4444;
}

.typing-indicator span {
  display: inline-block;
  width: 0.36rem;
  height: 0.36rem;
  margin: 0 0.1rem;
  border-radius: 999px;
  background: var(--chat-muted);
  animation: typing 1.4s infinite ease-in-out both;
}

.typing-indicator span:nth-child(1) {
  animation-delay: -0.32s;
}

.typing-indicator span:nth-child(2) {
  animation-delay: -0.16s;
}

.vue-markdown-wrapper :deep(*) {
  animation: fade-in 0.24s ease-in-out;
}

.vue-markdown-wrapper :deep(table) {
  width: 100%;
  margin: 0.75rem 0;
  border-collapse: collapse;
  font-size: 0.82rem;
}

.vue-markdown-wrapper :deep(th),
.vue-markdown-wrapper :deep(td) {
  border: 1px solid var(--chat-border);
  padding: 0.45rem 0.6rem;
  text-align: left;
}

.vue-markdown-wrapper :deep(th) {
  background: var(--chat-control-bg);
  font-weight: 700;
}

.vue-markdown-wrapper :deep(p) {
  margin: 0 0 0.7rem;
  line-height: 1.6;
}

.vue-markdown-wrapper :deep(p:last-child) {
  margin-bottom: 0;
}

@keyframes fade-in {
  0% {
    opacity: 0;
    transform: translateY(0.2rem);
  }
  100% {
    opacity: 1;
    transform: translateY(0);
  }
}

@keyframes typing {
  0%, 80%, 100% {
    transform: scale(0);
  }
  40% {
    transform: scale(1);
  }
}

@media (max-width: 720px) {
  .global-chat-wrapper,
  .global-chat-wrapper--board {
    --chat-safe-left: 0.5rem;
    --chat-safe-right: 0.5rem;
  }

  .chat-panel {
    top: calc(3.5rem + 0.5rem);
    right: var(--chat-safe-right);
    bottom: 0.5rem;
    left: var(--chat-safe-left);
    width: auto;
    height: auto;
    border-radius: 0.9rem;
  }

  .control-icon-button,
  .tool-icon,
  .action-btn {
    min-width: 2.75rem;
    min-height: 2.75rem;
  }

  /* The mobile panel already has a fixed viewport geometry; a resize
   * affordance only consumes space and is not a useful touch interaction. */
  .chat-resize-handle {
    display: none;
  }

  .glass-header {
    cursor: default;
    touch-action: auto;
  }

  .sidebar {
    position: absolute;
    inset: 0 auto 0 0;
    z-index: 20;
    width: min(17rem, 82vw);
    box-shadow: 16px 0 30px rgba(15, 23, 42, 0.22);
  }

  .sidebar.collapsed {
    width: 0;
  }

  .task-grid {
    grid-template-columns: 1fr;
  }

  .messages-viewport {
    padding: 0.75rem;
  }

  .welcome-screen {
    align-items: stretch;
    text-align: left;
    padding-top: 0.25rem;
  }

  .brand-logo {
    display: none;
  }

  .welcome-subtitle {
    margin-bottom: 0.65rem;
  }

  .task-card {
    padding: 0.6rem;
  }

  .msg-row {
    gap: 0.5rem;
    margin-bottom: 0.75rem;
  }

  .avatar-container {
    width: 1.8rem;
    height: 1.8rem;
  }

  .msg-body {
    padding: 0.6rem 0.7rem;
    font-size: 0.84rem;
  }

  .chat-execution-header {
    grid-template-columns: 1.55rem minmax(0, 1fr);
    gap: 0.5rem;
  }

  .chat-execution-icon {
    display: none;
  }

  .chat-execution-meta {
    grid-column: 2;
    align-items: center;
    flex-direction: row;
    flex-wrap: wrap;
  }

  .chat-execution-events li {
    grid-template-columns: 1.4rem minmax(0, 1fr);
    align-items: start;
    gap: 0.5rem;
  }

  .chat-execution-outcome {
    grid-column: 2;
    justify-self: start;
  }

  .chat-execution-events {
    max-height: min(12rem, 24vh);
  }

  .input-floating-area {
    padding: 0.65rem 0.75rem 0.75rem;
  }
}

@media (pointer: coarse) {
  .control-icon-button,
  .tool-icon,
  .action-btn {
    min-width: 2.75rem;
    min-height: 2.75rem;
  }

  .chat-resize-handle {
    width: 2.75rem;
    height: 2.75rem;
  }
}

@media (max-height: 720px) {
  .chat-panel {
    top: calc(4rem + 0.5rem);
    height: min(38rem, calc(100dvh - 5rem));
  }

  .glass-header {
    min-height: 3rem;
    padding-block: 0.55rem;
  }

  .messages-viewport {
    padding-bottom: 0.75rem;
  }

  .brand-logo {
    display: none;
  }

  .welcome-screen {
    justify-content: flex-start;
    padding-top: 0.25rem;
  }

  .task-card {
    padding: 0.55rem;
  }

  .modern-textarea {
    min-height: 2.35rem;
  }
}
</style>

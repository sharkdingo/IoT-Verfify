<script setup lang="ts">
/* =================================================================================
 * 1. Imports & Setup
 * ================================================================================= */
import {ref, reactive, computed, defineAsyncComponent, nextTick, onMounted, onBeforeUnmount, watch, h, type Ref} from 'vue'
import { useRouter } from 'vue-router'
import { useI18n } from 'vue-i18n'
import { useChatStore } from '@/stores/chat'
import { useAuth } from '@/stores/auth'
import { authApi } from '@/api/auth'
import { ElMessage, ElMessageBox } from 'element-plus'
// Icons

// Types
import type {DeviceDialogMeta, DeviceTemplate, InternalVariable} from '../types/device'
import type { BoardLayoutDto, CanvasPan } from '../types/canvas'
import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { RuleForm, RuleSourceItemType } from '../types/rule'
import type { SpecCondition, Specification, SpecTemplateId } from '../types/spec'
import type {
  ModelGenerationIssue,
  Trace,
  TraceDevice,
  TraceTriggeredRule,
  TraceVariable,
  VerificationRequest,
  VerificationResult,
  VerificationRun,
  VerificationRunSummary,
  VerificationTask,
  VerificationTaskSummary
} from '@/types/verify'
import type { SimulationRequest, SimulationState, SimulationTask, SimulationTaskSummary, SimulationTraceSummary } from '@/types/simulation'
import type {
  AvailableFuzzingRunSummary,
  FuzzingExplorationMode,
  FuzzingFinding,
  FuzzingFindingSummary,
  FuzzingInputEvent,
  FuzzPaperDomainPreview,
  FuzzWorkloadPreview,
  FuzzingRequest,
  FuzzingRun,
  FuzzingRunSummary,
  FuzzingTask,
  FuzzingTaskSummary
} from '@/types/fuzzing'
import { isValidFuzzPaperDomainFingerprint } from '@/types/fuzzing'
import type { RunBoardComparison } from '@/types/modelSemantics'
import type { ModelEnvironmentVariable } from '@/types/model'
import type { InteractiveOperationStage, TaskCancellationResult, TaskProgressStage } from '@/types/task'
import type { FixApplyResult } from '@/types/fix'
import type { ChatLogoutPreparation } from '@/types/chat'
import type {
  PortableSceneCondition,
  PortableSceneDevice,
  PortableSceneEnvironmentVariable,
  PortableSceneFile,
  PortableSceneRule,
  PortableSceneSpecification,
  PortableSceneTemplate
} from '@/types/scene'
// Panel types removed

// Utils
import { getNodeIcon as resolveNodeIcon, validateManifest } from '../utils/device'
import { getVerificationOutcome, normalizeSpecResults } from '../utils/verificationResult'
import { createDeviceInstanceId, deviceLabelKey, getUniqueLabel } from '../utils/canvas/nodeCreate'
import { NODE_HEIGHT_RANGE, NODE_POSITION_ABS_MAX, NODE_WIDTH_RANGE } from '../utils/canvas/nodeLayout'
import {
  buildSpecificationSemanticKey,
  buildSpecFormula,
  isSameSpecification,
  isSpecRelatedToNode
} from '../utils/spec'
import { assertRuleHasTrigger, getLinkPoints, ruleSimilarityReasonKey } from '../utils/rule'
import {
  canOpenTracePlayback,
  deriveTraceContext,
  formatTraceSpec,
  isPlaybackDeviceAttacked,
  normalizePlaybackDeviceId,
  playbackDeviceChanged,
  playbackDeviceChangeDetails,
  playbackEnvironmentChangeDetails,
  playbackDeviceSecurityFacts,
  playbackDeviceSummaryParts,
  type PlaybackDeviceChange,
  type PlaybackEnvironmentChange
} from '@/utils/traceView'
import {
  buildSimulationRequestPayload,
  buildModelRunSignature,
  buildVerificationRequestPayload,
  normalizeModelRelation,
  normalizeNuSmvDeviceName
} from '@/utils/modelRequest'
import { isModelSemanticsConsistent } from '@/utils/modelSemantics'
import { analyzeBoardAttackSurface, getAttackSelectionIssue } from '@/utils/attackSurface'
import { localizedErrorMessage, localizedTextOrFallback } from '@/utils/userMessage'
import { RECOMMENDATION_RESPONSE_INCOMPLETE_CODE } from '@/utils/recommendationResponse'
import {
  FUZZ_RESPONSE_INCOMPLETE_CODE,
  assertFuzzingFindingBelongsToRun,
  getFuzzActiveTaskLimit,
  getFuzzStoredTaskLimit
} from '@/utils/fuzzingResponse'
import {
  FUZZ_INLINE_RESULT_RECOVERY_MAX_FAILURES,
  classifyTrackedFuzzRunError,
  clearStoredFuzzNotifications,
  fuzzNotificationStorageKeyForUser,
  fuzzRunRetryDelayMs,
  isTransientTaskHttpStatus
} from '@/utils/fuzzingRecovery'
import {
  createPagedRequestCoordinator,
  type PagedRequestToken
} from '@/utils/pagedRequestCoordinator'
import { generationIssueReasonKey } from '@/utils/generationIssue'
import {
  FUZZ_ITERATIONS_MAX,
  FUZZ_ITERATIONS_MIN,
  FUZZ_PATH_LENGTH_MAX,
  FUZZ_PATH_LENGTH_MIN,
  FUZZ_POPULATION_MAX,
  FUZZ_POPULATION_MIN,
  getFuzzingConfigurationIssue,
  isKnownFuzzingSpecificationSupported
} from '@/utils/fuzzingConfig'
import {
  RecommendationCandidateError,
  materializeRuleRecommendation,
  materializeSpecificationRecommendationConditions
} from '@/utils/recommendationMaterialization'
import {
  RUN_RESPONSE_INCOMPLETE_CODE,
  activeTaskProgressStage,
  validateCompletedVerificationTask
} from '@/utils/runResponse'
import {
  PRIVACY_OPTIONS,
  TRUST_OPTIONS,
  buildDeviceRuntimeConfig,
  createDeviceRuntimeDraft,
  findTemplateStatePrivacy,
  findTemplateStateTrust,
  getTemplateLocalVariables,
  getTemplateEnvironmentVariables,
  getTemplateWorkingStates,
  resetDeviceRuntimeDraft,
  templateVariableHasEnumValues,
  templateVariableUsesNumericBounds,
  validateDeviceRuntimeConfig,
  type DeviceRuntimeConfig
} from '@/utils/deviceRuntime'

// Config
import { defaultSpecTemplates, specTemplateDetails } from '../assets/config/specTemplates'

// API
import boardApi, {
  BOARD_RESPONSE_INCOMPLETE_CODE,
  type BoardReplacementPreview,
  type BoardReplacementStaleData,
  type DeviceLayout,
  type DeviceRecommendation,
  type EnvironmentVariablePatchResult,
  type EnvironmentVariableChange,
  type RecommendationAdjustmentItem,
  type RecommendationFilteredItem,
  type ScenarioRecommendationResponse,
  type SpecificationRecommendation
} from '@/api/board'
import simulationApi from '@/api/simulation'
import fuzzingApi from '@/api/fuzzing'
import rulesApi, { type RuleRecommendation } from '@/api/rules'

// Components
import CanvasBoard from '../components/CanvasBoard.vue'
import ControlCenter from '../components/ControlCenter.vue'
import SystemInspector from '../components/SystemInspector.vue'
import LanguageToggle from '@/components/common/LanguageToggle.vue'
import ThemeToggle from '@/components/common/ThemeToggle.vue'
import InfoTooltip from '@/components/common/InfoTooltip.vue'
import { useModalAccessibility } from '@/composables/useModalAccessibility'
import { useTheme } from '@/composables/useTheme'

const LogoutConfirmDialog = defineAsyncComponent(() => import('@/components/LogoutConfirmDialog.vue'))
const AccountDeleteDialog = defineAsyncComponent(() => import('@/components/AccountDeleteDialog.vue'))
const DeviceDialog = defineAsyncComponent(() => import('../components/DeviceDialog.vue'))
const RuleBuilderDialog = defineAsyncComponent(() => import('../components/RuleBuilderDialog.vue'))
const SimulationTimeline = defineAsyncComponent(() => import('../components/SimulationTimeline.vue'))
const FixResultDialog = defineAsyncComponent(() => import('../components/FixResultDialog.vue'))
const RecommendationProgressStatus = defineAsyncComponent(
  () => import('../components/RecommendationProgressStatus.vue')
)
const PlaybackChangePopover = defineAsyncComponent(() => import('../components/PlaybackChangePopover.vue'))
const FuzzingPanel = defineAsyncComponent(() => import('../components/FuzzingPanel.vue'))
const FuzzingResultDialog = defineAsyncComponent(() => import('../components/FuzzingResultDialog.vue'))
const TraceHistoryPanel = defineAsyncComponent(() => import('../components/TraceHistoryPanel.vue'))

const props = defineProps<{
  prepareChatForLogout?: () => Promise<ChatLogoutPreparation>
}>()

const { t, locale } = useI18n()
const router = useRouter()
const chatStore = useChatStore()
const { toggleChat } = chatStore
const { logout, getUser, getToken } = useAuth()
const { theme } = useTheme()

const showLogoutDialog = ref(false)
const showDeleteAccountDialog = ref(false)
const isLoggingOut = ref(false)
const isDeletingAccount = ref(false)
const currentUser = computed(() => getUser())

type FuzzUnreadNotification = {
  taskId: number
  kind: 'COMPLETED' | 'FAILED' | 'UNAVAILABLE'
  runId?: number
  outcome?: string
  createdAt: string
}

const unreadFuzzNotifications = ref<FuzzUnreadNotification[]>([])
const trackedFuzzTaskIds = ref<number[]>([])
const unreadFuzzNotificationCount = computed(() => unreadFuzzNotifications.value.length)
const unreadFailedFuzzCount = computed(() =>
  unreadFuzzNotifications.value.filter(item => item.kind === 'FAILED').length)

const handleLogout = () => {
  showLogoutDialog.value = true
}

const handleLogoutConfirm = async () => {
  if (isLoggingOut.value) return
  isLoggingOut.value = true
  let shouldLogout = false
  try {
    let chatPreparation: ChatLogoutPreparation = 'ready'
    try {
      chatPreparation = await props.prepareChatForLogout?.() ?? 'ready'
    } catch (error) {
      console.error('Failed to prepare the active assistant request for logout', error)
      chatPreparation = 'reconciliation-failed'
    }
    if (chatPreparation === 'reconciliation-failed') {
      ElMessage.error(t('app.chat.logoutReconcileFailed'))
      return
    }
    if (chatPreparation === 'outcome-unknown') {
      try {
        await ElMessageBox.confirm(
          t('app.chat.logoutOutcomeUnknownMessage'),
          t('app.chat.logoutOutcomeUnknownTitle'),
          {
            confirmButtonText: t('app.chat.logoutOutcomeUnknownConfirm'),
            cancelButtonText: t('app.cancel'),
            type: 'warning'
          }
        )
      } catch {
        return
      }
    }

    try {
      layoutSaveFeedbackSuppressed = true
      await flushPendingBoardLayout({
        silent: true,
        timeoutMs: LAYOUT_LOGOUT_FLUSH_TIMEOUT_MS
      })
    } catch {
      // A layout flush failure must not trap the user in the current login session.
    }
    try {
      // API failure does not prevent local logout after the user confirmed it.
      await authApi.logout()
    } catch {
      // Local logout remains authoritative for this browser session.
    }
    shouldLogout = true
  } finally {
    if (shouldLogout) {
      logout()
      showLogoutDialog.value = false
      router.push({ path: '/', query: { mode: 'login' } })
    }
    isLoggingOut.value = false
  }
}

const handleLogoutCancel = () => {
  showLogoutDialog.value = false
}

const handleOpenDeleteAccount = () => {
  if (isLoggingOut.value) return
  showLogoutDialog.value = false
  showDeleteAccountDialog.value = true
}

const handleDeleteAccountConfirm = async (payload: { password: string; confirmation: string }) => {
  if (isDeletingAccount.value) return
  isDeletingAccount.value = true
  const deletedAccountNotificationStorageKey = fuzzNotificationStorageKeyForUser(
    currentUser.value?.userId
  )
  try {
    await authApi.deleteAccount(payload)
    clearStoredFuzzNotifications(deletedAccountNotificationStorageKey)
    unreadFuzzNotifications.value = []
    trackedFuzzTaskIds.value = []
    logout()
    showDeleteAccountDialog.value = false
    ElMessage.success(t('app.deleteAccountSuccess'))
    router.push({ path: '/', query: { mode: 'register' } })
  } catch (error: any) {
    const message = localizedErrorMessage(error, t('app.deleteAccountFailed'), locale.value)
    ElMessage.error(message)
  } finally {
    isDeletingAccount.value = false
  }
}

/* =================================================================================
 * 2. Constants & Configuration
 * ================================================================================= */

// Panel constants removed

const NODE_GRID_COLS = 4
const DEFAULT_NODE_WIDTH = 176
const DEFAULT_NODE_HEIGHT = 128
const NODE_SPACING_X = 220
const NODE_SPACING_Y = 164

const MIN_ZOOM = 0.4
const MAX_ZOOM = 2
const ZOOM_STEP = 0.1
const LAYOUT_SAVE_DEBOUNCE_MS = 700
const LAYOUT_LOGOUT_FLUSH_TIMEOUT_MS = 1_500
const DEFAULT_CONTROL_PANEL_WIDTH = 320
const DEFAULT_INSPECTOR_PANEL_WIDTH = 320

const BASE_NODE_WIDTH = DEFAULT_NODE_WIDTH
const BASE_FONT_SIZE = 16
const ASYNC_TASK_POLL_INTERVAL_MS = 1000
const ASYNC_TASK_MAX_POLLS = 600
const TASK_INBOX_REFRESH_INTERVAL_MS = 5000
const AI_RECOMMENDATION_REQUIREMENT_MAX_LENGTH = 2000
const pollingAborted = ref(false)
let boardLifecycleDisposed = false

const formatEnvironmentSnapshot = (variable: ModelEnvironmentVariable | null | undefined): string => {
  if (!variable) return ''
  const labels = [
    variable.value,
    variable.trust ? t(`app.${variable.trust}`) : '',
    variable.privacy ? t(`app.${variable.privacy}`) : ''
  ].filter(Boolean)
  return labels.length > 0 ? `${variable.name}: ${labels.join(' · ')}` : variable.name
}

const formatEnvironmentChange = (change: EnvironmentVariableChange): string => {
  if (change.changeType === 'ADDED') {
    return t('app.environmentChangeAdded', { item: formatEnvironmentSnapshot(change.currentValue) })
  }
  if (change.changeType === 'UPDATED') {
    return t('app.environmentChangeUpdated', {
      before: formatEnvironmentSnapshot(change.previousValue),
      after: formatEnvironmentSnapshot(change.currentValue)
    })
  }
  return t('app.environmentChangeRemoved', { item: formatEnvironmentSnapshot(change.previousValue) })
}

const reportEnvironmentChanges = (changes: EnvironmentVariableChange[] | null | undefined) => {
  const values = Array.isArray(changes) ? changes : []
  const added = values.filter(change => change.changeType === 'ADDED')
    .map(change => formatEnvironmentSnapshot(change.currentValue))
  const updated = values.filter(change => change.changeType === 'UPDATED')
    .map(change => `${formatEnvironmentSnapshot(change.previousValue)} -> ${formatEnvironmentSnapshot(change.currentValue)}`)
  const removed = values.filter(change => change.changeType === 'REMOVED')
    .map(change => formatEnvironmentSnapshot(change.previousValue))
  if (added.length > 0) ElMessage.info(t('app.environmentPoolAddedByDeviceChange', { items: added.join(', ') }))
  if (updated.length > 0) ElMessage.info(t('app.environmentPoolUpdatedByDeviceChange', { items: updated.join(', ') }))
  if (removed.length > 0) ElMessage.info(t('app.environmentPoolRemovedByDeviceChange', { items: removed.join(', ') }))
}

const SCENE_FILE_SCHEMA = 'iot-verify.board-scene'
const SCENE_FILE_VERSION = 4

type BoardSceneModel = {
  schema: typeof SCENE_FILE_SCHEMA
  version: typeof SCENE_FILE_VERSION
  templates: DeviceTemplate[]
  devices: DeviceNode[]
  environmentVariables: ModelEnvironmentVariable[]
  rules: RuleForm[]
  specs: Specification[]
}

type NormalizedSceneDevice = Omit<DeviceNode, 'currentStateTrust' | 'currentStatePrivacy'> & {
  currentStateTrust?: 'trusted' | 'untrusted'
  currentStatePrivacy?: 'public' | 'private'
}

type ScenarioRecommendationResult = {
  message: string
  count: number
  requestedCount: number
  validatedCount: number
  filteredCount: number
  filteredItems: RecommendationFilteredItem[]
  adjustedCount: number
  adjustedItems: RecommendationAdjustmentItem[]
  rawCandidateCount: number
  inspectedCount: number
  truncatedCount: number
  scenarioName: string
  rationale: string
  verificationReady: boolean
  readinessIssues: ScenarioRecommendationResponse['readinessIssues']
  scene: BoardSceneModel | null
}

class PollingAbortedError extends Error {
  constructor() {
    super('Polling aborted')
    this.name = 'PollingAbortedError'
  }
}

class AsyncTaskCancelledError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'AsyncTaskCancelledError'
  }
}

class FuzzTaskRecoveryPendingError extends Error {
  constructor() {
    super('Fuzz task or completed result is awaiting recovery')
    this.name = 'FuzzTaskRecoveryPendingError'
  }
}

class FuzzCompletedResultUnavailableError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'FuzzCompletedResultUnavailableError'
  }
}

const throwIfPollingAborted = () => {
  if (pollingAborted.value) {
    throw new PollingAbortedError()
  }
}

const isPollingAbortedError = (error: unknown): boolean =>
  error instanceof PollingAbortedError

const isAsyncTaskCancelledError = (error: unknown): boolean =>
  error instanceof AsyncTaskCancelledError

const isFuzzTaskRecoveryPendingError = (error: unknown): boolean =>
  error instanceof FuzzTaskRecoveryPendingError

const isFuzzCompletedResultUnavailableError = (error: unknown): boolean =>
  error instanceof FuzzCompletedResultUnavailableError

const waitForNextPoll = async () => {
  await new Promise(resolve => setTimeout(resolve, ASYNC_TASK_POLL_INTERVAL_MS))
  throwIfPollingAborted()
}

const waitForPollingDelay = async (delayMs: number) => {
  await new Promise(resolve => setTimeout(resolve, delayMs))
  throwIfPollingAborted()
}

/* =================================================================================
 * 3. State Definitions
 * ================================================================================= */

// --- Canvas State ---
const canvasZoom = ref(1)
const isCanvasHovered = ref(false)
const canvasPan = ref<CanvasPan>({ x: 0, y: 0 })

let isPanning = false
let panStart = { x: 0, y: 0 }
let panOrigin = { x: 0, y: 0 }
let layoutSaveTimer: ReturnType<typeof setTimeout> | null = null
let layoutSaveFeedbackSuppressed = false
let persistedWideLayout: BoardLayoutDto | null = null

type ControlCenterSection = 'devices' | 'templates' | 'rules' | 'specs'
type InspectorSection = 'devices' | 'rules' | 'specs'

const isNarrowViewport = () =>
  typeof window !== 'undefined' && window.innerWidth < 768

let wasNarrowViewport = isNarrowViewport()

const isControlCenterSection = (value?: string): value is ControlCenterSection =>
  value === 'devices' || value === 'templates' || value === 'rules' || value === 'specs'

const isInspectorSection = (value?: string): value is InspectorSection =>
  value === 'devices' || value === 'rules' || value === 'specs'

const clampPanelWidth = (value: unknown, fallback: number): number => {
  const width = typeof value === 'number' ? value : fallback
  if (!Number.isFinite(width)) return fallback
  return Math.min(520, Math.max(240, Math.round(width)))
}

const boardPanels = reactive({
  control: {
    collapsed: isNarrowViewport(),
    width: DEFAULT_CONTROL_PANEL_WIDTH,
    activeSection: 'templates' as ControlCenterSection
  },
  inspector: {
    collapsed: isNarrowViewport(),
    width: DEFAULT_INSPECTOR_PANEL_WIDTH,
    activeSection: 'devices' as InspectorSection
  }
})

type ActionDockMode = 'expanded' | 'compact' | 'packed'

const actionDockViewportWidth = ref(typeof window !== 'undefined' ? window.innerWidth : 1440)
const actionDockPreferredMode = ref<ActionDockMode>('expanded')
const wideActionDockModeCycle: ActionDockMode[] = ['expanded', 'compact', 'packed']
const narrowActionDockModeCycle: ActionDockMode[] = ['compact', 'packed']

const actionDockModeCycle = computed<ActionDockMode[]>(() =>
  actionDockViewportWidth.value >= 1280 ? wideActionDockModeCycle : narrowActionDockModeCycle
)

const actionDockMode = computed<ActionDockMode>(() => {
  const width = actionDockViewportWidth.value
  if (width < 720 && actionDockPreferredMode.value === 'expanded') return 'packed'
  if (width < 1280 && actionDockPreferredMode.value === 'expanded') return 'compact'
  return actionDockPreferredMode.value
})

const isActionDockPackedMode = computed(() => actionDockMode.value === 'packed')
const nextActionDockPreferredMode = computed<ActionDockMode>(() => {
  const cycle = actionDockModeCycle.value
  const currentMode = cycle.includes(actionDockMode.value) ? actionDockMode.value : cycle[0]
  const index = cycle.indexOf(currentMode)
  return cycle[(index + 1) % cycle.length]
})
const actionDockToggleIcon = computed(() => {
  if (nextActionDockPreferredMode.value === 'compact') return 'chevron_right'
  if (nextActionDockPreferredMode.value === 'packed') return 'toolbar'
  return 'chevron_left'
})
const actionDockToggleLabel = computed(() => {
  if (nextActionDockPreferredMode.value === 'compact') return t('app.actionDockSwitchCompact')
  if (nextActionDockPreferredMode.value === 'packed') return t('app.actionDockSwitchPacked')
  return t('app.actionDockSwitchExpanded')
})
const cycleActionDockMode = () => {
  actionDockPreferredMode.value = nextActionDockPreferredMode.value
}
const restoreActionDockFromPacked = () => {
  actionDockPreferredMode.value = actionDockViewportWidth.value >= 1280 ? 'expanded' : 'compact'
}
const hasActionDockActivity = computed(() =>
  isSimulating.value ||
  isFuzzing.value ||
  isVerifying.value ||
  simulationAnimationState.value.visible ||
  traceAnimationState.value.visible ||
  isRecommendingScenario.value ||
  isAnyRecommendationRunning() ||
  unreadFuzzNotificationCount.value > 0
)
const actionDockRailWidth = computed(() => actionDockMode.value === 'expanded' ? '8.75rem' : '3.5rem')
const actionDockReservedWidth = computed(() => actionDockMode.value === 'expanded' ? 150 : 64)
const actionDockRightInset = computed(() => {
  const inspectorWidth = boardPanels.inspector.collapsed ? 48 : boardPanels.inspector.width
  const gap = actionDockViewportWidth.value < 640 ? 8 : 14
  return inspectorWidth + gap
})
const actionDockStyle = computed(() => ({
  '--board-action-dock-right': `${actionDockRightInset.value}px`,
  '--board-action-dock-width': actionDockRailWidth.value
}))

const updateActionDockViewport = () => {
  if (typeof window === 'undefined') return
  const narrow = isNarrowViewport()
  if (!wasNarrowViewport && narrow && layoutHydrated.value) {
    if (layoutSaveTimer) {
      clearTimeout(layoutSaveTimer)
      layoutSaveTimer = null
    }
    persistedWideLayout = buildBoardLayoutPayload()
    void saveBoardLayout({ silent: true })
  }
  actionDockViewportWidth.value = window.innerWidth
  if (narrow) {
    applyViewportPanelConstraints()
    if (!wasNarrowViewport && layoutHydrated.value) {
      void nextTick(() => fitNodesToCanvas(getVisibleDeviceNodes()))
    }
  } else if (wasNarrowViewport && persistedWideLayout) {
    applyBoardLayout(persistedWideLayout)
  }
  wasNarrowViewport = narrow
}

const layoutHydrated = ref(false)
let layoutSaveErrorShown = false
let panelStateTouchedBeforeLayout = false

const boardShellStyle = computed(() => ({
  '--board-control-width': `${boardPanels.control.collapsed ? 64 : boardPanels.control.width}px`,
  '--board-inspector-width': `${boardPanels.inspector.collapsed ? 48 : boardPanels.inspector.width}px`,
  '--board-action-rail-width': actionDockRailWidth.value
}))

const boardHeaderTone = computed(() => theme.value === 'dark' ? 'dark' : 'light')

const applyViewportPanelConstraints = () => {
  if (!isNarrowViewport()) return
  boardPanels.control.collapsed = true
  boardPanels.inspector.collapsed = true
}

watch(actionDockViewportWidth, applyViewportPanelConstraints, { immediate: true })

// --- Core Data State ---
const deviceTemplates = ref<DeviceTemplate[]>([])
const templatesLoading = ref(false)
const nodes = ref<DeviceNode[]>([])
const environmentVariables = ref<ModelEnvironmentVariable[]>([])
const edges = ref<DeviceEdge[]>([])
const rules = ref<RuleForm[]>([])  // 独立存储规则列表
const rulesReordering = ref(false)
const focusedNodeId = ref<string | null>(null)
const focusedRuleId = ref<string | null>(null)
const focusedSpecId = ref<string | null>(null)
const sceneImportInputRef = ref<HTMLInputElement | null>(null)
const sceneActionsMenuRef = ref<HTMLDetailsElement | null>(null)
const sceneActionsMenuOpen = ref(false)
const closeSceneActionsMenu = (restoreFocus = false) => {
  const menu = sceneActionsMenuRef.value
  if (!menu) return
  menu.removeAttribute('open')
  sceneActionsMenuOpen.value = false
  if (restoreFocus) {
    void nextTick(() => menu.querySelector<HTMLElement>('summary')?.focus())
  }
}
const handleSceneActionsMenuToggle = () => {
  sceneActionsMenuOpen.value = sceneActionsMenuRef.value?.open === true
}
const isImportingScene = ref(false)
const isClearingScene = ref(false)
const isSceneReplacementInProgress = computed(() => isImportingScene.value || isClearingScene.value)

const isInternalVariableNode = (_node?: DeviceNode | null): boolean => false

const deepClone = <T,>(value: T): T =>
  JSON.parse(JSON.stringify(value))

const getVisibleDeviceNodes = (source: DeviceNode[] = nodes.value): DeviceNode[] =>
  source.filter(node => !isInternalVariableNode(node))

const cloneVisibleDeviceNodes = (): DeviceNode[] =>
  deepClone(getVisibleDeviceNodes())

// 画布只展示由用户规则派生的可见连线；模板内部变量保留在 manifest 中，不再生成用户可见节点/边。
const allEdges = computed(() => {
  return edges.value
})
const specifications = ref<Specification[]>([])

type BoardDataKey = 'templates' | 'nodes' | 'environment' | 'rules' | 'specs'
type BoardDataLoadState = 'loading' | 'ready' | 'error'

const boardDataLoadState = reactive<Record<BoardDataKey, BoardDataLoadState>>({
  templates: 'loading',
  nodes: 'loading',
  environment: 'loading',
  rules: 'loading',
  specs: 'loading'
})
const allBoardDataKeys: BoardDataKey[] = ['templates', 'nodes', 'environment', 'rules', 'specs']
const failedBoardDataKeys = computed(() =>
  allBoardDataKeys.filter(key => boardDataLoadState[key] === 'error'))
const isBoardDataReady = computed(() =>
  allBoardDataKeys.every(key => boardDataLoadState[key] === 'ready'))

const boardDataKeyLabel = (key: BoardDataKey): string => t(`app.boardDataKey_${key}`)

const ensureBoardDataReady = (keys: BoardDataKey[] = allBoardDataKeys): boolean => {
  const unavailable = keys.filter(key => boardDataLoadState[key] !== 'ready')
  if (unavailable.length === 0) return true
  ElMessage.error(t('app.boardDataEditBlocked', {
    collections: unavailable.map(boardDataKeyLabel).join(', ')
  }))
  return false
}

const resolveNodeRef = (refValue?: string | null): DeviceNode | undefined => {
  if (!refValue) return undefined
  return nodes.value.find(n => n.id === refValue)
}

const assertRulesHaveTriggers = (candidateRules: RuleForm[]): boolean => {
  try {
    candidateRules.forEach((rule, index) => assertRuleHasTrigger(rule, index))
    return true
  } catch (error: any) {
    ElMessage.warning({ message: t('app.ruleTriggerSourceRequired'), type: 'warning' })
    return false
  }
}

const countLogMarker = (logs: string[] | undefined, marker: string): number => {
  return (logs || []).filter(log => String(log).includes(marker)).length
}

const getGenerationIssues = (result: any): ModelGenerationIssue[] => {
  if (!Array.isArray(result?.generationIssues)) return []
  return result.generationIssues
    .filter((issue: unknown) => issue && typeof issue === 'object')
    .map((issue: any) => ({
      issueType: String(issue.issueType || 'MODEL_ITEM_OMITTED'),
      itemLabel: String(issue.itemLabel || t('app.unknownModelItem')),
      reasonCode: String(issue.reasonCode || 'UNCLASSIFIED_GENERATION_ISSUE') as ModelGenerationIssue['reasonCode'],
      reason: String(issue.reason || t('app.unknownOmissionReason'))
    }))
}

const getGenerationWarningCounts = (result: any) => {
  const logs = result?.checkLogs || []
  const issues = getGenerationIssues(result)
  const disabledRuleCount = Number(result?.disabledRuleCount ?? (issues.length > 0
    ? issues.filter(issue => issue.issueType === 'RULE_DISABLED').length
    : countLogMarker(logs, '[rule-disabled]')))
  const skippedSpecCount = Number(result?.skippedSpecCount ?? (issues.length > 0
    ? issues.filter(issue => issue.issueType === 'SPECIFICATION_SKIPPED').length
    : countLogMarker(logs, '[spec-skipped]')))
  return {
    disabledRuleCount,
    skippedSpecCount,
    total: disabledRuleCount + skippedSpecCount
  }
}

const getSimulationDisabledRuleCount = (result: any): number => {
  const issues = getGenerationIssues(result)
  return Number(result?.disabledRuleCount ?? (issues.length > 0
    ? issues.filter(issue => issue.issueType === 'RULE_DISABLED').length
    : countLogMarker(result?.logs || result?.checkLogs, '[rule-disabled]')))
}

const isSimulationModelComplete = (result: any): boolean => {
  return result?.modelComplete === true
}

const getSimulationStateCount = (result: any): number =>
  Array.isArray(result?.states) ? result.states.length : 0

const getSimulationActualStepCount = (result: any): number => {
  const steps = Number(result?.steps)
  return Number.isInteger(steps) && steps >= 0
    ? steps
    : Math.max(getSimulationStateCount(result) - 1, 0)
}

const getSimulationRequestedStepCount = (result: any): number => {
  const steps = Number(result?.requestedSteps)
  return Number.isInteger(steps) && steps >= 0 ? steps : 0
}

const isSimulationHorizonShorterThanRequested = (result: any): boolean =>
  getSimulationActualStepCount(result) < getSimulationRequestedStepCount(result)

const isSimulationModelSemanticsConsistent = (result: any): boolean =>
  isModelSemanticsConsistent(result?.modelSemantics, {
    isAttack: result?.isAttack,
    attackBudget: result?.attackBudget,
    enablePrivacy: result?.enablePrivacy
  })

const notifySimulationOutcome = (result: any, saved: boolean) => {
  const stateCount = result?.states?.length || 0
  const disabledRuleCount = getSimulationDisabledRuleCount(result)
  if (!isSimulationModelComplete(result)) {
    ElMessage.warning({
      message: t('app.simulationCompletedWithDisabledRules', {
        states: stateCount,
        rules: disabledRuleCount,
        saved: saved ? t('app.savedToHistorySuffix') : ''
      }),
      type: 'warning'
    })
    return
  }
  ElMessage.success({
    message: saved
      ? t('app.simulationTaskCompletedSaved', { count: stateCount })
      : t('app.simulationCompletedWithStates', { count: stateCount }),
    type: 'success'
  })
}

const extractApiErrorMessage = (error: any, fallback: string): string => {
  if (error?.code === BOARD_RESPONSE_INCOMPLETE_CODE) {
    return t('app.boardMutationResponseIncomplete')
  }
  if (error?.code === RUN_RESPONSE_INCOMPLETE_CODE) {
    return t('app.runResponseIncomplete')
  }
  if (error?.code === FUZZ_RESPONSE_INCOMPLETE_CODE) {
    return t('app.fuzzResponseIncomplete')
  }
  return localizedErrorMessage(error, fallback, locale.value)
}

const hasApiValidationError = (error: any, field: string): boolean => {
  const status = Number(error?.response?.status || 0)
  const fieldError = error?.response?.data?.data?.errors?.[field]
  return (status === 400 || status === 422)
    && typeof fieldError === 'string'
    && fieldError.trim().length > 0
}

const fuzzTaskQuotaMessage = (error: any): string | null => {
  const quota = getFuzzActiveTaskLimit(error)
  if (quota) {
    if (quota.activeTaskCount === undefined || quota.maxActiveTasksPerUser === undefined) {
      return t('app.fuzzActiveTaskLimitGeneric')
    }
    return t('app.fuzzActiveTaskLimitReached', {
      active: quota.activeTaskCount,
      limit: quota.maxActiveTasksPerUser
    })
  }
  const storedQuota = getFuzzStoredTaskLimit(error)
  if (!storedQuota) return null
  if (storedQuota.storedTaskCount === undefined
    || storedQuota.maxStoredTasksPerUser === undefined) {
    return t('app.fuzzStoredTaskLimitGeneric')
  }
  return t('app.fuzzStoredTaskLimitReached', {
    stored: storedQuota.storedTaskCount,
    limit: storedQuota.maxStoredTasksPerUser
  })
}

const asyncTaskQuotaMessage = (
  error: any,
  kind: 'verification' | 'simulation'
): string | null => {
  if (Number(error?.response?.status) !== 429) return null
  const data = error?.response?.data?.data
  const prefix = kind.toUpperCase()
  if (data?.reasonCode !== `${prefix}_ACTIVE_TASK_LIMIT_REACHED`
    && data?.reasonCode !== `${prefix}_STORED_TASK_LIMIT_REACHED`) return null
  const count = Number(data.taskCount)
  const limit = Number(data.maxTasksPerUser)
  const detailed = Number.isInteger(count) && Number.isInteger(limit)
  if (data.quotaType === 'ACTIVE') {
    return detailed
      ? t('app.asyncTaskActiveLimitReached', { count, limit })
      : t('app.asyncTaskActiveLimitGeneric')
  }
  return detailed
    ? t('app.asyncTaskStoredLimitReached', { count, limit })
    : t('app.asyncTaskStoredLimitGeneric')
}

const extractRecommendationErrorMessage = (error: any, fallback: string): string => {
  if (error?.code === RECOMMENDATION_RESPONSE_INCOMPLETE_CODE) {
    return t('app.recommendationResponseIncomplete')
  }
  if (error instanceof RecommendationCandidateError) {
    return t('app.recommendationInvalidFieldNoChange', { field: error.field })
  }
  return localizedErrorMessage(error, fallback, locale.value)
}

const isDefinitiveMutationRejection = (error: any): boolean => {
  const status = Number(error?.response?.status || 0)
  return status >= 400 && status < 500
}

type AsyncTaskStatus = 'PENDING' | 'RUNNING' | 'COMPLETED' | 'FAILED' | 'CANCELLED'

const formatAsyncTaskStatus = (status?: AsyncTaskStatus | string): string => {
  switch (status) {
    case 'PENDING':
      return t('app.taskStatusPending')
    case 'RUNNING':
      return t('app.taskStatusRunning')
    case 'COMPLETED':
      return t('app.taskStatusCompleted')
    case 'FAILED':
      return t('app.taskStatusFailed')
    case 'CANCELLED':
      return t('app.taskStatusCancelled')
    default:
      return status || t('app.taskInitializing')
  }
}

const formatTaskProgressStage = (
  stage?: TaskProgressStage | null,
  status?: AsyncTaskStatus | string
): string => {
  const activeStage = activeTaskProgressStage(stage, status)
  return activeStage ? t(`app.taskProgressStage_${activeStage}`) : formatAsyncTaskStatus(status)
}

const buildVerificationResultFromTask = (task: VerificationTask, traces: Trace[] = []): VerificationResult => {
  const completedTask = validateCompletedVerificationTask(task)
  return {
    outcome: completedTask.outcome,
    traces,
    specResults: normalizeSpecResults(completedTask.specResults),
    checkLogs: completedTask.checkLogs,
    disabledRuleCount: completedTask.disabledRuleCount,
    skippedSpecCount: completedTask.skippedSpecCount,
    generationIssues: completedTask.generationIssues,
    isAttack: completedTask.isAttack,
    attackBudget: completedTask.attackBudget,
    enablePrivacy: completedTask.enablePrivacy,
    modelSemantics: completedTask.modelSemantics,
    modelSnapshot: completedTask.modelSnapshot,
    historyPersistence: { status: 'SAVED', runId: completedTask.id },
    modelComplete: completedTask.modelComplete,
    nusmvOutput: completedTask.nusmvOutput
  }
}

const buildVerificationResultFromRun = (run: VerificationRun, traces: Trace[] = []): VerificationResult => ({
  outcome: run.outcome,
  traces,
  specResults: normalizeSpecResults(run.specResults),
  checkLogs: run.checkLogs,
  disabledRuleCount: run.disabledRuleCount,
  skippedSpecCount: run.skippedSpecCount,
  generationIssues: run.generationIssues,
  isAttack: run.isAttack,
  attackBudget: run.attackBudget,
  enablePrivacy: run.enablePrivacy,
  modelSemantics: run.modelSemantics,
  modelSnapshot: run.modelSnapshot,
  historyPersistence: { status: 'SAVED', runId: run.id },
  modelComplete: run.modelComplete,
  nusmvOutput: run.nusmvOutput
})

const isVerificationModelComplete = (
  result: any,
  _outcome = getVerificationOutcome(result)
): boolean => result?.modelComplete === true

const getSpecResultDisplayTitle = (spec: Specification | undefined, index: number): string => {
  const detail = specTemplateDetails.find(template => template.id === spec?.templateId)
  if (detail?.labelKey) return t(detail.labelKey)
  return spec?.templateLabel || detail?.label || t('app.specificationNumber', { number: index + 1 })
}

const getTraceSpecDisplayTitle = (trace: Pick<Trace, 'violatedSpecId' | 'violatedSpec'> | null | undefined): string => {
  if (!trace) return t('app.unknown')
  if (trace.violatedSpec) {
    const summary = formatTraceSpec(trace.violatedSpec, t)
    if (summary) return summary
  }
  const matchedSpec = specifications.value.find(spec => spec.id === trace.violatedSpecId)
  if (matchedSpec) return getSpecResultDisplayTitle(matchedSpec, 0)
  return t('app.unknown')
}

const countVerificationFailures = (result: any): number => {
  const failedSpecs = normalizeSpecResults(result?.specResults)
    .filter(specResult => specResult.outcome === 'VIOLATED').length
  const traceCount = result?.traces?.length || 0
  return Math.max(failedSpecs, traceCount)
}

const getVerificationFailureMessage = (result: any): string => {
  if (getVerificationOutcome(result) === 'INCONCLUSIVE') {
    return t('app.verificationInconclusiveSummary')
  }
  const failureCount = countVerificationFailures(result)
  return failureCount > 0
    ? t('app.verificationFailedWithViolations', { count: failureCount })
    : t('app.verificationFailedNoSpecResults')
}

const notifyVerificationOutcome = (result: any) => {
  const counts = getGenerationWarningCounts(result)
  const verificationOutcome = getVerificationOutcome(result)
  const modelComplete = isVerificationModelComplete(result, verificationOutcome)
  if (!modelComplete) {
    if (counts.total === 0) {
      const message = verificationOutcome === 'SATISFIED'
        ? t('app.verificationSatisfiedButIncomplete')
        : verificationOutcome === 'INCONCLUSIVE'
          ? t('app.verificationInconclusiveSummary')
          : getVerificationFailureMessage(result)
      ElMessage.warning({ message, type: 'warning' })
      return
    }
    const outcome = verificationOutcome === 'SATISFIED'
      ? t('app.verificationPassed')
      : getVerificationFailureMessage(result)
    ElMessage.warning({
      message: t('app.generationWarningSummary', {
        outcome,
        total: counts.total,
        disabledRuleCount: counts.disabledRuleCount,
        skippedSpecCount: counts.skippedSpecCount
      }),
      type: 'warning'
    })
    return
  }

  if (verificationOutcome === 'SATISFIED') {
    ElMessage.success({ message: t('app.verificationSatisfiedComplete'), type: 'success' })
  } else if (verificationOutcome === 'INCONCLUSIVE') {
    ElMessage.warning({ message: t('app.verificationInconclusiveSummary'), type: 'warning' })
  } else {
    ElMessage.warning({ message: getVerificationFailureMessage(result), type: 'warning' })
  }
}

const draggingTplName = ref<string | null>(null)
const templateInstanceDialogVisible = ref(false)
const templateInstanceSaving = ref(false)
const templateInstanceDialogData = reactive({
  template: null as DeviceTemplate | null,
  name: '',
  position: { x: 0, y: 0 }
})

const templateInstanceRuntime = reactive(createDeviceRuntimeDraft())

const templateInstanceWorkingStates = computed(() =>
  getTemplateWorkingStates(templateInstanceDialogData.template)
)

const templateInstanceInternalVariables = computed(() =>
  getTemplateLocalVariables(templateInstanceDialogData.template)
)

const templateInstanceHasModes = computed(() => {
  const manifest = templateInstanceDialogData.template?.manifest
  return Array.isArray(manifest?.Modes)
    && manifest.Modes.length > 0
    && templateInstanceWorkingStates.value.length > 0
})

const templateInstanceHasRuntimeFields = computed(() =>
  Boolean(templateInstanceDialogData.template && (templateInstanceHasModes.value || templateInstanceInternalVariables.value.length > 0))
)

const getTemplateRequiredEnvironmentNames = (template?: DeviceTemplate | null): string[] => {
  if (!template) return []
  const names = new Set<string>()
  getTemplateEnvironmentVariables(template).forEach(variable => {
    const name = String(variable.Name || '').trim()
    if (name) names.add(name)
  })
  ;(template.manifest.ImpactedVariables || []).forEach(rawName => {
    const name = String(rawName || '').trim()
    if (name) names.add(name)
  })
  return Array.from(names).sort((left, right) => left.localeCompare(right))
}

const getMissingTemplateEnvironmentNames = (template?: DeviceTemplate | null): string[] => {
  const existing = new Set(environmentVariables.value.map(variable => variable.name))
  return getTemplateRequiredEnvironmentNames(template).filter(name => !existing.has(name))
}

const templateInstanceEnvironmentAdditions = computed(() =>
  getMissingTemplateEnvironmentNames(templateInstanceDialogData.template)
)

const recommendedDeviceEnvironmentAdditions = (recommendation: DeviceRecommendation): string[] =>
  getMissingTemplateEnvironmentNames(findTemplateByAnyName(recommendation.templateName))

const resetTemplateInstanceRuntime = (template = templateInstanceDialogData.template) => {
  resetDeviceRuntimeDraft(templateInstanceRuntime, template)
}

watch(() => templateInstanceDialogData.template, template => {
  resetTemplateInstanceRuntime(template)
})

watch(() => templateInstanceRuntime.state, state => {
  if (!templateInstanceHasModes.value) return
  templateInstanceRuntime.currentStateTrust = findTemplateStateTrust(templateInstanceDialogData.template, state)
  templateInstanceRuntime.currentStatePrivacy = findTemplateStatePrivacy(templateInstanceDialogData.template, state)
})

const templateVariableInputPlaceholder = (variable: InternalVariable) => {
  if (templateVariableUsesNumericBounds(variable)) {
    const lower = variable.LowerBound ?? '-∞'
    const upper = variable.UpperBound ?? '∞'
    return `${lower} - ${upper}`
  }
  return t('app.enterValuePlaceholder')
}

const buildTemplateInstanceRuntimeConfig = (template: DeviceTemplate): DeviceRuntimeConfig | undefined => {
  return buildDeviceRuntimeConfig(template, templateInstanceRuntime, { variableScope: 'local' })
}

const validateTemplateInstanceRuntimeConfig = (template: DeviceTemplate, runtime?: DeviceRuntimeConfig) => {
  return validateDeviceRuntimeConfig(template, runtime, t, { variableScope: 'local' })
}

let boardMutationQueue: Promise<void> = Promise.resolve()
let nodeLayoutMutationVersion = 0
const pendingNodeLayouts = new Map<string, { version: number; layout: DeviceLayout }>()

const enqueueBoardMutation = async <T,>(work: () => Promise<T>): Promise<T> => {
  const next = boardMutationQueue.then(work, work)
  boardMutationQueue = next.then(() => undefined, () => undefined)
  return next
}

const waitForPendingBoardMutations = async () => {
  await boardMutationQueue
}

const applyLayoutToNode = (node: DeviceNode | undefined, layout: DeviceLayout) => {
  if (!node) return
  node.position = { ...layout.position }
  node.width = layout.width
  node.height = layout.height
}

const deviceLayoutMatches = (node: DeviceNode | undefined, layout: DeviceLayout) =>
  !!node
  && node.position.x === layout.position.x
  && node.position.y === layout.position.y
  && node.width === layout.width
  && node.height === layout.height

const deviceRuntimeMatches = (node: DeviceNode | undefined, runtime: DeviceRuntimeConfig) => {
  if (!node) return false
  if (runtime.state !== undefined && node.state !== runtime.state) return false
  if ((node.currentStateTrust ?? null) !== (runtime.currentStateTrust ?? null)) return false
  if ((node.currentStatePrivacy ?? null) !== (runtime.currentStatePrivacy ?? null)) return false
  if (JSON.stringify(node.variables ?? []) !== JSON.stringify(runtime.variables ?? [])) return false
  return JSON.stringify(node.privacies ?? []) === JSON.stringify(runtime.privacies ?? [])
}

// --- UI State ---
const dialogVisible = ref(false)
const dialogMeta = reactive<DeviceDialogMeta>({
  nodeId: '',
  deviceName: '',
  description: '',
  label: '',
  manifest: null,
  rules: [],
  specs: []
})
const deviceRuntimeSaving = ref(false)

// Custom dialog states
const renameDialogVisible = ref(false)
const renameDialogData = reactive({
  node: null as DeviceNode | null,
  newName: ''
})

const deleteConfirmDialogVisible = ref(false)
const deleteConfirmDialogData = reactive({
  node: null as DeviceNode | null,
  hasRelations: false,
  relationCount: {
    rules: 0,
    specs: 0
  },
  relatedRules: [] as string[],
  relatedSpecs: [] as string[],
  environmentChanges: [] as EnvironmentVariableChange[],
  impactToken: ''
})

/* =================================================================================
 * 4. Helper Functions (Styles & Calculation)
 * ================================================================================= */

// getCardWidth removed


const getNodeLabelStyle = (node: DeviceNode) => {
  const ratio = Math.min(node.width / BASE_NODE_WIDTH, node.height / 100)
  const scale = Math.min(Math.max(ratio, 0.68), 1.05)
  const fontSize = Math.min(13, Math.max(10, BASE_FONT_SIZE * scale * 0.72))
  return {
    fontSize: fontSize + 'px',
    lineHeight: '1.18',
    maxWidth: Math.max(48, node.width - 18) + 'px'
  }
}

const normalizeTemplateLookupName = (value: unknown): string =>
  String(value ?? '').trim().toLowerCase()

const templateMatchesName = (template: DeviceTemplate, name: unknown): boolean => {
  const target = normalizeTemplateLookupName(name)
  if (!target) return false
  return [template.name, template.manifest?.Name]
    .some(candidate => normalizeTemplateLookupName(candidate) === target)
}

const findTemplateByAnyName = (name: unknown): DeviceTemplate | undefined =>
  deviceTemplates.value.find(template => templateMatchesName(template, name))

const resolveTemplateForNode = (node: DeviceNode): DeviceTemplate | null => {
  return findTemplateByAnyName(node.templateName) || null
}

const getBoardNodeIcon = (node: DeviceNode, stateOverride?: string): string => {
  const template = resolveTemplateForNode(node)
  return resolveNodeIcon(node, template?.manifest || stateOverride || null, stateOverride)
}

/* =================================================================================
 * 5. Canvas Interaction (Zoom & Pan)
 * ================================================================================= */

const clampZoom = (value: number) =>
  Math.min(MAX_ZOOM, Math.max(MIN_ZOOM, value))

const setCanvasZoom = (value: number, options: { preserveCenter?: boolean } = {}) => {
  const nextZoom = clampZoom(value)
  if (!Number.isFinite(nextZoom)) return
  if (Math.abs(nextZoom - canvasZoom.value) < 0.001) return

  const center = options.preserveCenter ? getVisibleCanvasCenterWorld() : null
  canvasZoom.value = nextZoom
  if (center) {
    panCanvasToWorldCenter(center.x, center.y)
  }
}

const adjustCanvasZoom = (delta: number) => {
  setCanvasZoom(canvasZoom.value + delta, { preserveCenter: true })
}

const canvasZoomPercent = computed(() => Math.round(canvasZoom.value * 100))

const handleCanvasMapZoomInput = (event: Event) => {
  const input = event.target as HTMLInputElement | null
  const value = Number(input?.value)
  if (!Number.isFinite(value)) {
    if (input) input.value = String(canvasZoomPercent.value)
    return
  }
  setCanvasZoom(value / 100, { preserveCenter: true })
}

const onBoardWheel = (e: WheelEvent) => {
  if (e.ctrlKey) {
    if (e.deltaY > 0) {
      adjustCanvasZoom(-ZOOM_STEP)
    } else {
      adjustCanvasZoom(ZOOM_STEP)
    }
  }
}

const onCanvasEnter = () => (isCanvasHovered.value = true)
const onCanvasLeave = () => (isCanvasHovered.value = false)

const onGlobalKeydown = (e: KeyboardEvent) => {
  if (e.ctrlKey) {
    if (['=', '+', '-', '0'].includes(e.key)) {
      e.preventDefault()

      if (e.key === '=' || e.key === '+') {
        adjustCanvasZoom(ZOOM_STEP)
      } else if (e.key === '-') {
        adjustCanvasZoom(-ZOOM_STEP)
      } else if (e.key === '0') {
        setCanvasZoom(1, { preserveCenter: true })
      }
    }
  }
}

const onCanvasPointerDown = (e: PointerEvent) => {
  if (e.button !== 0) return
  isPanning = true
  panStart = { x: e.clientX, y: e.clientY }
  panOrigin = { x: canvasPan.value.x, y: canvasPan.value.y }

  const target = e.currentTarget as HTMLElement
  if (target && target.setPointerCapture) {
    target.setPointerCapture(e.pointerId)
  }

  window.addEventListener('pointermove', onCanvasPointerMove)
  window.addEventListener('pointerup', onCanvasPointerUp)
}

const onCanvasPointerMove = (e: PointerEvent) => {
  if (!isPanning) return
  const dx = e.clientX - panStart.x
  const dy = e.clientY - panStart.y
  canvasPan.value = {
    x: panOrigin.x + dx,
    y: panOrigin.y + dy
  }
}

const onCanvasPointerUp = async (e: PointerEvent) => {
  isPanning = false

  const target = e.target as HTMLElement
  if (target && target.releasePointerCapture) {
    try { target.releasePointerCapture(e.pointerId) } catch(err){}
  }

  // Layout saving removed
  window.removeEventListener('pointermove', onCanvasPointerMove)
  window.removeEventListener('pointerup', onCanvasPointerUp)
}

// Panel interaction removed

/* =================================================================================
 * 7. Node / Edge / Spec Management
 * ================================================================================= */


const createDeviceInstanceAt = async (
  tpl: DeviceTemplate,
  pos: { x: number; y: number },
  customName?: string,
  runtime?: DeviceRuntimeConfig
) => {
  if (!ensureBoardDataReady(['nodes', 'templates'])) {
    throw new Error(t('app.boardDataLoadFailed'))
  }
  return enqueueBoardMutation(async () => {
    const baseName = customName?.trim() || tpl.manifest.Name
    const uniqueLabel = getUniqueLabel(baseName, getVisibleDeviceNodes())
    if (uniqueLabel !== baseName) {
      ElMessage.warning(t('app.deviceNameChangedBeforeCreate', { name: uniqueLabel }))
      throw new Error('Device name changed before queued creation')
    }
    const node: DeviceNode = {
      id: createDeviceInstanceId(getVisibleDeviceNodes()),
      templateName: tpl.manifest.Name,
      label: uniqueLabel,
      position: pos,
      state: tpl.manifest.InitState || 'Working',
      width: DEFAULT_NODE_WIDTH,
      height: DEFAULT_NODE_HEIGHT,
      ...(runtime || {})
    }
    try {
      const mutation = await boardApi.addNodes([node])
      nodes.value = getVisibleDeviceNodes(mutation.currentNodes)
      environmentVariables.value = mutation.environmentVariables
      reportEnvironmentChanges(mutation.environmentChanges)
      syncRuleDerivedEdges()
      const created = mutation.affectedDevices[0]
      await focusCreatedDeviceNode(created)
      return { device: created, responseConfirmed: true }
    } catch (error: any) {
      if (!isDefinitiveMutationRejection(error)) {
        const [nodesRefreshed, environmentRefreshed] = await Promise.all([
          refreshDevices(),
          refreshEnvironmentVariables()
        ])
        const created = nodes.value.find(candidate => candidate.id === node.id)
        if (nodesRefreshed && environmentRefreshed && created) {
          await focusCreatedDeviceNode(created)
          ElMessage.warning(t('app.deviceCreateOutcomeRefreshed', { name: created.label }))
          return { device: created, responseConfirmed: false }
        }
      }
      ElMessage.error(localizedErrorMessage(error, t('app.saveNodesFailed'), locale.value))
      throw error
    }
  })
}

const openTemplateInstanceDialog = (tpl: DeviceTemplate, pos: { x: number; y: number }) => {
  if (!ensurePlaybackClosedForMutation()) return
  templateInstanceDialogData.template = tpl
  templateInstanceDialogData.position = pos
  templateInstanceDialogData.name = getUniqueLabel(tpl.manifest.Name, getVisibleDeviceNodes())
  resetTemplateInstanceRuntime(tpl)
  templateInstanceDialogVisible.value = true
}

const cancelTemplateInstanceCreate = () => {
  if (templateInstanceSaving.value) return
  templateInstanceDialogVisible.value = false
  templateInstanceDialogData.template = null
  templateInstanceDialogData.name = ''
  resetTemplateInstanceRuntime(null)
}

const confirmTemplateInstanceCreate = async () => {
  if (!ensurePlaybackClosedForMutation()) return
  const tpl = templateInstanceDialogData.template
  const name = templateInstanceDialogData.name.trim()
  if (!tpl) return
  if (!name) {
    ElMessage.warning(t('app.enterDeviceName'))
    return
  }
  const availableName = getUniqueLabel(name, getVisibleDeviceNodes())
  if (availableName !== name) {
    templateInstanceDialogData.name = availableName
    ElMessage.warning(t('app.deviceNameAdjustedToAvoidConflict', { name: availableName }))
    return
  }

  const runtime = buildTemplateInstanceRuntimeConfig(tpl)
  const runtimeError = validateTemplateInstanceRuntimeConfig(tpl, runtime)
  if (runtimeError) {
    ElMessage.warning(runtimeError)
    return
  }

  templateInstanceSaving.value = true
  try {
    const outcome = await createDeviceInstanceAt(tpl, templateInstanceDialogData.position, availableName, runtime)
    const created = outcome.device
    if (created.label !== availableName) {
      ElMessage.warning(t('app.deviceNameAdjustedToAvoidConflict', { name: created.label }))
    }
    if (outcome.responseConfirmed) {
      ElMessage.success(t('app.deviceAddedWithName', { name: created.label }))
    }
    templateInstanceDialogVisible.value = false
    templateInstanceDialogData.template = null
    templateInstanceDialogData.name = ''
    resetTemplateInstanceRuntime(null)
  } catch { /* 已回滚并提示 */ }
  finally {
    templateInstanceSaving.value = false
  }
}

const handleTemplateDragStart = (templateName: string) => {
  draggingTplName.value = templateName
}

const handleTemplateDragEnd = () => {
  draggingTplName.value = null
}

const onCanvasDragOver = (e: DragEvent) => {
  if (!e.dataTransfer) return
  if (isModelPlaybackActive.value) {
    e.dataTransfer.dropEffect = 'none'
    return
  }
  const hasTemplateData = draggingTplName.value
    || Array.from(e.dataTransfer.types || []).includes('application/x-iot-template')
  e.dataTransfer.dropEffect = hasTemplateData ? 'copy' : 'none'
}

const onCanvasDrop = async (e: DragEvent) => {
  if (!ensurePlaybackClosedForMutation()) return
  const droppedTemplateName = draggingTplName.value
    || e.dataTransfer?.getData('application/x-iot-template')
    || e.dataTransfer?.getData('text/plain')
  if (!droppedTemplateName) return
  const tpl = findTemplateByAnyName(droppedTemplateName)
  if (!tpl) return

  const rect = (e.currentTarget as HTMLElement).getBoundingClientRect()
  const Sx = e.clientX - rect.left
  const Sy = e.clientY - rect.top

  const x = (Sx - canvasPan.value.x) / canvasZoom.value
  const y = (Sy - canvasPan.value.y) / canvasZoom.value

  openTemplateInstanceDialog(tpl, { x, y })
  draggingTplName.value = null
}

const handleNodeMovedOrResized = async (nodeId: string) => {
  if (!ensurePlaybackClosedForMutation()) return
  if (!ensureBoardDataReady(['nodes'])) return
  const node = nodes.value.find(candidate => candidate.id === nodeId)
  if (!node) return
  const layout: DeviceLayout = {
    position: { x: node.position.x, y: node.position.y },
    width: Math.round(node.width),
    height: Math.round(node.height)
  }
  applyLayoutToNode(node, layout)
  const version = ++nodeLayoutMutationVersion
  pendingNodeLayouts.set(nodeId, { version, layout })
  await enqueueBoardMutation(async () => {
    try {
      const mutation = await boardApi.updateNodeLayout(nodeId, layout)
      nodes.value = getVisibleDeviceNodes(mutation.currentNodes)
      const pending = pendingNodeLayouts.get(nodeId)
      if (pending && pending.version > version) {
        applyLayoutToNode(nodes.value.find(candidate => candidate.id === nodeId), pending.layout)
      } else if (pending?.version === version) {
        pendingNodeLayouts.delete(nodeId)
      }
      syncRuleDerivedEdges()
    } catch (error: any) {
      const pending = pendingNodeLayouts.get(nodeId)
      if (pending?.version !== version) return
      pendingNodeLayouts.delete(nodeId)
      const refreshed = await refreshDevices()
      if (!isDefinitiveMutationRejection(error)
        && refreshed
        && deviceLayoutMatches(nodes.value.find(candidate => candidate.id === nodeId), layout)) {
        ElMessage.warning(t('app.deviceLayoutOutcomeRefreshed'))
      } else {
        ElMessage.error(extractApiErrorMessage(error, t('app.saveNodesFailed')))
      }
    }
  })
  // edges 由 rules 动态生成，不需要单独保存
}

const handleAddRule = async (request: {
  rule: RuleForm
  complete: (saved: boolean) => void
}) => {
  if (!ensurePlaybackClosedForMutation()) {
    request.complete(false)
    return
  }
  let saved = false
  let attemptedRule: RuleForm | null = null
  try {
    await enqueueBoardMutation(async () => {
      try {
        const payload = request.rule
        if (!ensureBoardDataReady(['nodes', 'templates', 'rules'])) return
        const { sources, toId, toApi } = payload
        if (!sources || !sources.length || !toId || !toApi) {
          ElMessage.warning(t('app.fillAllRuleFields'))
          return
        }
        if (!assertRulesHaveTriggers([payload])) return
        if (!resolveNodeRef(toId)) return

        const newRule: RuleForm = {
          ...payload,
          id: 'rule_' + Date.now(),
          name: payload.name || t('app.automationRule')
        }
        attemptedRule = newRule
        const mutation = await boardApi.addRule(JSON.parse(JSON.stringify(newRule)))
        rules.value = mutation.currentItems
        syncRuleDerivedEdges()
        if (mutation.affectedItem?.id) {
          await focusRuleOnCanvas(mutation.affectedItem.id)
        }
        ElMessage.success(t('app.addRuleSuccess'))
        saved = true
      } catch (error: any) {
        console.error('addRule error', error)
        if (!isDefinitiveMutationRejection(error) && attemptedRule) {
          const refreshed = await refreshRules()
          if (refreshed && ruleExists(attemptedRule)) {
            ElMessage.warning(t('app.ruleCreateOutcomeRefreshed'))
            saved = true
            return
          }
        }
        ElMessage.error(extractApiErrorMessage(error, t('app.saveRulesFailed')))
      }
    })
  } finally {
    request.complete(saved)
  }
}

const ruleRecommendationTargetTypes = new Set<RuleSourceItemType>(['api', 'variable', 'mode', 'state'])
const valueBasedRuleRecommendationTargetTypes = new Set<RuleSourceItemType>(['variable', 'mode', 'state'])

const normalizeRuleRecommendationTargetType = (targetType?: string): RuleSourceItemType | undefined => {
  const normalized = String(targetType || '').trim().toLowerCase()
  return ruleRecommendationTargetTypes.has(normalized as RuleSourceItemType)
    ? normalized as RuleSourceItemType
    : undefined
}

const isValueBasedRuleRecommendationCondition = (targetType?: string) => {
  const normalized = normalizeRuleRecommendationTargetType(targetType)
  return normalized ? valueBasedRuleRecommendationTargetTypes.has(normalized) : false
}

const formatRecommendedRuleDevice = (deviceId?: string, label?: string): string => {
  const nodeId = String(deviceId || '').trim()
  const currentLabel = nodeId ? resolveNodeRef(nodeId)?.label : ''
  if (currentLabel) return currentLabel
  const displayLabel = String(label || '').trim()
  return displayLabel || t('app.unknownModelItem')
}

const formatRecommendedSpecConditionTarget = (condition: any): string => {
  const device = formatRecommendedRuleDevice(condition?.deviceId, condition?.deviceLabel)
  const targetType = String(condition?.targetType || '').trim().toLowerCase()
  const key = String(condition?.key || '').trim()
  if (targetType === 'trust' || targetType === 'privacy') {
    const property = condition?.propertyScope === 'state'
      ? t('app.currentModeStateProperty', { mode: key })
      : key
    const dimension = targetType === 'trust' ? t('app.sourceLabel') : t('app.sensitivityLabel')
    return `${device} · ${property} · ${dimension}`
  }
  return key ? `${device}.${key}` : device
}

const formatRecommendedRuleConditionDevice = (condition: RuleRecommendation['conditions'][number]): string =>
  formatRecommendedRuleDevice(condition.deviceId, condition.deviceLabel || condition.deviceName)

const formatRecommendedRuleCommandDevice = (command: RuleRecommendation['command']): string =>
  formatRecommendedRuleDevice(command.deviceId, command.deviceLabel || command.deviceName)

const formatRecommendedRuleContentDevice = (command: RuleRecommendation['command']): string =>
  formatRecommendedRuleDevice(command.contentDevice, command.contentDeviceLabel)

const normalizeRuleDuplicateText = (value: unknown): string => {
  if (value === null || value === undefined) return ''
  return String(value).trim()
}

const buildRuleDuplicateKey = (rule: RuleForm): string => {
  const sources = (rule.sources || [])
    .map(source => {
      const itemType = normalizeRuleRecommendationTargetType(source.itemType)
      const isValueBased = itemType ? valueBasedRuleRecommendationTargetTypes.has(itemType) : false
      return {
        fromId: normalizeRuleDuplicateText(source.fromId),
        fromApi: itemType === 'state' ? 'state' : normalizeRuleDuplicateText(source.fromApi),
        itemType: itemType || '',
        // A missing relation is invalid input, not an implicit equality. Keep it
        // distinguishable here so local duplicate detection cannot change semantics.
        relation: isValueBased
          ? (normalizeModelRelation(source.relation) || normalizeRuleDuplicateText(source.relation))
          : '',
        value: isValueBased ? normalizeRuleDuplicateText(source.value) : ''
      }
    })
    .sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)))

  return JSON.stringify({
    sources,
    command: {
      toId: normalizeRuleDuplicateText(rule.toId),
      toApi: normalizeRuleDuplicateText(rule.toApi),
      contentDevice: normalizeRuleDuplicateText(rule.contentDevice),
      content: normalizeRuleDuplicateText(rule.content)
    }
  })
}

const ruleExists = (candidate: RuleForm): boolean => {
  const candidateKey = buildRuleDuplicateKey(candidate)
  return rules.value.some(rule => buildRuleDuplicateKey(rule) === candidateKey)
}

const confirmRecommendedRuleSimilarity = async (candidate: RuleForm): Promise<boolean> => {
  try {
    const result = await boardApi.checkRuleSimilarity(candidate)
    if (!result.requiresReview) return true

    const reason = t(ruleSimilarityReasonKey(result.reasonCode))
    const message = result.matchedRule
      ? t('app.aiSimilarRuleMayExistWithMatch', {
          rule: result.matchedRule,
          reason
        })
      : t('app.aiSimilarRuleMayExist', { reason })

    try {
      await ElMessageBox.confirm(
        message,
        t('app.aiRuleSimilarityDetected'),
        {
          confirmButtonText: t('app.applyAnyway'),
          cancelButtonText: t('app.cancel'),
          type: 'warning',
          appendTo: 'body',
          lockScroll: false
        }
      )
      return true
    } catch (error: any) {
      if (error === 'cancel' || error === 'close') return false
      console.error('AI similarity confirmation failed:', error)
      return false
    }
  } catch (error) {
    console.error('AI similarity check failed before applying recommendation:', error)
    try {
      await ElMessageBox.confirm(
        t('app.aiSimilarityCheckFailedCanStillApply'),
        t('app.aiRuleSimilarityDetected'),
        {
          confirmButtonText: t('app.applyAnyway'),
          cancelButtonText: t('app.cancel'),
          type: 'warning',
          appendTo: 'body',
          lockScroll: false
        }
      )
      return true
    } catch (confirmError: any) {
      if (confirmError === 'cancel' || confirmError === 'close') return false
      console.error('AI similarity failure confirmation failed:', confirmError)
      return false
    }
  }
}

// 应用推荐的规则
const applyRecommendation = async (rec: RuleRecommendation, index: number) => {
  if (!ensurePlaybackClosedForMutation()) return
  if (!ensureBoardDataReady(['nodes', 'templates', 'rules'])) return
  if (appliedRuleRecommendations.value.has(index)) {
    ElMessage.warning(t('app.recommendationAlreadyApplied'))
    return
  }
  if (applyingRuleRecommendations.value.has(index)) return

  const recommendationEpoch = ruleRecommendationRequestEpoch

  let attemptedRule: RuleForm | null = null
  const reportFailure = async (error: any) => {
    console.error('applyRecommendation error', error)
    if (!isDefinitiveMutationRejection(error) && attemptedRule) {
      const refreshed = await refreshRules()
      if (refreshed && ruleExists(attemptedRule)) {
        if (recommendationEpoch === ruleRecommendationRequestEpoch) {
          appliedRuleRecommendations.value.add(index)
        }
        ElMessage.warning(t('app.ruleCreateOutcomeRefreshed'))
        return
      }
    }
    ElMessage.error(extractApiErrorMessage(error, t('app.failedToApplyRule')))
  }
  try {
    const newRule = materializeRuleRecommendation(rec, 'rule_' + Date.now())
    attemptedRule = newRule

    if (!assertRulesHaveTriggers([newRule])) {
      return
    }
    if (ruleExists(newRule)) {
      ElMessage.warning(t('app.duplicateRuleExists'))
      return
    }
    applyingRuleRecommendations.value.add(index)
    const shouldApply = await confirmRecommendedRuleSimilarity(newRule)
    if (!shouldApply) return
    if (recommendationEpoch !== ruleRecommendationRequestEpoch) return

    await enqueueBoardMutation(async () => {
      try {
        const mutation = await boardApi.addRule(JSON.parse(JSON.stringify(newRule)))
        rules.value = mutation.currentItems
        syncRuleDerivedEdges()
        const createdRule = mutation.affectedItem
        if (createdRule?.id) {
          await focusRuleOnCanvas(createdRule.id)
        }
        if (recommendationEpoch === ruleRecommendationRequestEpoch) {
          appliedRuleRecommendations.value.add(index)
        }
        ElMessage.success(t('app.ruleAddedSuccessfully'))
      } catch (error: any) {
        await reportFailure(error)
      }
    })
  } catch (error: any) {
    if (error instanceof RecommendationCandidateError) {
      ElMessage.warning(t('app.recommendationInvalidFieldNoChange', { field: error.field }))
      return
    }
    await reportFailure(error)
  } finally {
    if (recommendationEpoch === ruleRecommendationRequestEpoch) {
      applyingRuleRecommendations.value.delete(index)
    }
  }
}


/* =================================================================================
 * 8. Context Menu & Deletion
 * ================================================================================= */

const onDeviceListClick = (deviceId: string, options: { focus?: boolean; ensureReadable?: boolean } = {}) => {
  if (isModelPlaybackActive.value) {
    ElMessage.info({ message: t('app.playbackDeviceDetailsUseTimeline'), type: 'info' })
    return
  }
  const node = nodes.value.find(n => n.id === deviceId)
  if (!node) return
  const shouldFocus = options.focus ?? true

  if (shouldFocus) {
    focusDeviceNodeOnCanvas(node, { ensureReadable: options.ensureReadable })
  }

  const tpl = resolveTemplateForNode(node)
  const manifest = tpl?.manifest || null
  dialogMeta.nodeId = node.id
  dialogMeta.label = node.label
  dialogMeta.deviceName = manifest?.Name || tpl?.manifest?.Name || node.templateName
  dialogMeta.description = manifest?.Description || tpl?.manifest?.Description || ''
  dialogMeta.manifest = manifest
  dialogMeta.rules = edges.value.filter(e => e.from === node.id || e.to === node.id)
  dialogMeta.specs = specifications.value.filter(spec =>
    isSpecRelatedToNode(spec, node.id)
  )
  dialogVisible.value = true
}

const focusDeviceFromInspector = (deviceId: string) => {
  const node = nodes.value.find(n => n.id === deviceId)
  if (!node) return
  focusDeviceNodeOnCanvas(node, { ensureReadable: true })
}

// 右键菜单状态
const contextMenu = ref({
  visible: false,
  x: 0,
  y: 0,
  node: null as DeviceNode | null
})

const onNodeContext = (node: DeviceNode, position: { x: number; y: number }) => {
  if (isInternalVariableNode(node)) {
    return
  }
  contextMenu.value = {
    visible: true,
    x: position.x,
    y: position.y,
    node
  }
}

const openNodeFromCanvas = (node: DeviceNode) => {
  onDeviceListClick(node.id, { ensureReadable: true })
}

const closeContextMenu = () => {
  contextMenu.value.visible = false
}

const openRenameDialog = (node: DeviceNode) => {
  renameDialogData.node = node
  renameDialogData.newName = node.label
  renameDialogVisible.value = true
}

// 右键菜单操作
const renameDevice = () => {
  if (!contextMenu.value.node) return
  openRenameDialog(contextMenu.value.node)
  closeContextMenu()
}

const handleDialogRename = () => {
  const node = nodes.value.find(candidate => candidate.id === dialogMeta.nodeId)
  if (!node) return
  dialogVisible.value = false
  openRenameDialog(node)
}

const deleteDevice = () => {
  if (!contextMenu.value.node) return
  deleteCurrentNodeWithConfirm(contextMenu.value.node.id)
  closeContextMenu()
}

const handleRenameDevice = async (nodeId: string, newLabel: string): Promise<boolean> => {
  if (!ensurePlaybackClosedForMutation()) return false
  if (!ensureBoardDataReady(['nodes', 'specs'])) return false
  return enqueueBoardMutation(async () => {
    const requestedLabelKey = deviceLabelKey(newLabel)
    const exists = nodes.value.some(n => deviceLabelKey(n.label) === requestedLabelKey && n.id !== nodeId)
    if (exists) {
      ElMessage.error(t('app.nameExists'))
      return false
    }
    if (!nodes.value.some(node => node.id === nodeId)) return false

    try {
      const mutation = await boardApi.renameNode(nodeId, newLabel)
      nodes.value = getVisibleDeviceNodes(mutation.currentNodes)
      environmentVariables.value = mutation.environmentVariables
      specifications.value = mutation.currentSpecifications
      reportEnvironmentChanges(mutation.environmentChanges)
      syncRuleDerivedEdges()
      ElMessage.success(t('app.renameSuccess'))
      return true
    } catch (error: any) {
      if (!isDefinitiveMutationRejection(error)) {
        const [nodesRefreshed, specsRefreshed, environmentRefreshed] = await Promise.all([
          refreshDevices(),
          refreshSpecifications(),
          refreshEnvironmentVariables()
        ])
        const renamed = nodes.value.find(candidate => candidate.id === nodeId && candidate.label === newLabel)
        if (nodesRefreshed && specsRefreshed && environmentRefreshed && renamed) {
          ElMessage.warning(t('app.deviceRenameOutcomeRefreshed', { name: newLabel }))
          return true
        }
      }
      ElMessage.error(extractApiErrorMessage(error, t('app.saveNodesFailed')))
      return false
    }
  })
}

const handleDeviceRuntimeSave = async (nodeId: string, runtime: DeviceRuntimeConfig) => {
  if (!ensurePlaybackClosedForMutation()) return
  if (!ensureBoardDataReady(['nodes', 'templates'])) return
  if (deviceRuntimeSaving.value) return
  const node = nodes.value.find(n => n.id === nodeId)
  if (!node) return

  const template = resolveTemplateForNode(node)
  if (!template) {
    ElMessage.error(t('app.loadTemplatesFailed'))
    return
  }

  const validationMessage = validateDeviceRuntimeConfig(template, runtime, t, { variableScope: 'local' })
  if (validationMessage) {
    ElMessage.warning(validationMessage)
    return
  }

  const runtimeRequest: DeviceRuntimeConfig = deepClone(runtime)

  deviceRuntimeSaving.value = true
  try {
    await enqueueBoardMutation(async () => {
      try {
        const mutation = await boardApi.updateNodeRuntime(nodeId, runtimeRequest)
        nodes.value = getVisibleDeviceNodes(mutation.currentNodes)
        syncRuleDerivedEdges()
        ElMessage.success(mutation.operation === 'updated'
          ? t('app.instanceConfigSaved')
          : t('app.instanceConfigUnchanged'))
        onDeviceListClick(nodeId)
      } catch (error: any) {
        console.error('保存设备实例配置失败', error)
        if (!isDefinitiveMutationRejection(error)) {
          const nodesRefreshed = await refreshDevices()
          const persisted = nodes.value.find(candidate => candidate.id === nodeId)
          if (nodesRefreshed && deviceRuntimeMatches(persisted, runtimeRequest)) {
            ElMessage.warning(t('app.deviceRuntimeOutcomeRefreshed'))
            onDeviceListClick(nodeId)
            return
          }
        }
        ElMessage.error(extractApiErrorMessage(error, t('app.instanceConfigSaveFailed')))
      }
    })
  } finally {
    deviceRuntimeSaving.value = false
  }
}

const viewDeviceDetails = () => {
  if (!contextMenu.value.node) return
  // 显示设备详情 - 复用左侧列表点击的逻辑
  onDeviceListClick(contextMenu.value.node.id)
  closeContextMenu()
}


type DeviceDeletionOutcome = {
  responseConfirmed: boolean
}

const forceDeleteNode = async (
  nodeId: string,
  impactToken: string
): Promise<DeviceDeletionOutcome | null> => {
  if (!ensureBoardDataReady(['nodes', 'environment', 'rules', 'specs'])) return null
  return enqueueBoardMutation(async () => {
    try {
      const mutation = await boardApi.deleteNode(nodeId, impactToken)
      nodes.value = getVisibleDeviceNodes(mutation.currentNodes)
      environmentVariables.value = mutation.environmentVariables
      rules.value = mutation.currentRules
      specifications.value = mutation.currentSpecifications
      reportEnvironmentChanges(mutation.environmentChanges)
      syncRuleDerivedEdges()
      return { responseConfirmed: true }
    } catch (error: any) {
      console.error('删除设备失败', error)
      const message = extractApiErrorMessage(error, t('app.deleteDeviceFailedRetry'))
      if (error?.response?.status === 409) {
        await Promise.all([refreshDevices(), refreshEnvironmentVariables(), refreshRules(), refreshSpecifications()])
        void deleteCurrentNodeWithConfirm(nodeId)
        ElMessage.warning(message)
      } else if (!isDefinitiveMutationRejection(error)) {
        const refreshed = await refreshSceneForReconciliation()
        if (!refreshed) {
          ElMessage.warning(t('app.deviceDeleteOutcomeUnknownRefreshFailed'))
        } else if (!nodes.value.some(node => node.id === nodeId)) {
          ElMessage.warning(t('app.deviceDeleteOutcomeRefreshed'))
          return { responseConfirmed: false }
        } else {
          ElMessage.warning(t('app.deviceDeleteOutcomeUnconfirmedAfterRefresh'))
        }
      } else {
        ElMessage.error(message)
      }
      return null
    }
  })
}

const deleteCurrentNodeWithConfirm = async (nodeId: string) => {
  if (!ensurePlaybackClosedForMutation()) return
  if (!ensureBoardDataReady(['nodes', 'environment', 'rules', 'specs'])) return
  try {
    const preview = await boardApi.previewNodeDeletion(nodeId)
    const impactToken = preview.impactToken?.trim()
    if (!impactToken) throw new Error(t('app.deviceDeletionPreviewFailed'))
    const relatedRules = preview.removedRules
    const relatedSpecs = preview.removedSpecifications
    const environmentChanges = preview.environmentChanges
    deleteConfirmDialogData.node = preview.deletedDevice
    deleteConfirmDialogData.hasRelations = relatedRules.length > 0
      || relatedSpecs.length > 0
      || environmentChanges.length > 0
    deleteConfirmDialogData.relationCount = {
      rules: relatedRules.length,
      specs: relatedSpecs.length
    }
    deleteConfirmDialogData.relatedRules = relatedRules.map((rule, index) =>
      rule.name || t('app.ruleNumber', { number: index + 1 }))
    deleteConfirmDialogData.relatedSpecs = relatedSpecs.map((spec, index) =>
      getSpecResultDisplayTitle(spec, index))
    deleteConfirmDialogData.environmentChanges = environmentChanges
    deleteConfirmDialogData.impactToken = impactToken
    deleteConfirmDialogVisible.value = true
  } catch (error: any) {
    ElMessage.error(localizedErrorMessage(error, t('app.deviceDeletionPreviewFailed'), locale.value))
  }
}

const handleDialogDelete = () => {
  if (!dialogMeta.nodeId) return
  void deleteCurrentNodeWithConfirm(dialogMeta.nodeId)
}

// Custom dialog handlers
const confirmRename = async () => {
  if (!renameDialogData.node || !renameDialogData.newName.trim()) return

  const saved = await handleRenameDevice(renameDialogData.node.id, renameDialogData.newName.trim())
  if (!saved) return
  renameDialogVisible.value = false
  renameDialogData.node = null
  renameDialogData.newName = ''
}

const cancelRename = () => {
  renameDialogVisible.value = false
  renameDialogData.node = null
  renameDialogData.newName = ''
}

const isRenameDialogOpen = computed(() => renameDialogVisible.value)
const {
  setDialogRef: setRenameDialogRef,
  handleModalKeydown: handleRenameDialogKeydown
} = useModalAccessibility(isRenameDialogOpen, cancelRename)

const confirmDelete = async () => {
  if (!ensurePlaybackClosedForMutation()) return
  if (!deleteConfirmDialogData.node) return

  try {
    const nodeName = deleteConfirmDialogData.node.label
    const outcome = await forceDeleteNode(
      deleteConfirmDialogData.node.id,
      deleteConfirmDialogData.impactToken
    )
    if (!outcome) return
    if (outcome.responseConfirmed) {
      ElMessage.success(t('app.deviceDeleteSuccessSummary', {
        name: nodeName,
        rules: deleteConfirmDialogData.relationCount.rules,
        specs: deleteConfirmDialogData.relationCount.specs,
        variables: deleteConfirmDialogData.environmentChanges.length
      }))
    }
    // 如果设备详情对话框是打开的，也要关闭它
    if (dialogVisible.value) {
      dialogVisible.value = false
    }
    deleteConfirmDialogVisible.value = false
    deleteConfirmDialogData.node = null
    deleteConfirmDialogData.impactToken = ''
    deleteConfirmDialogData.environmentChanges = []
  } catch (error) {
    console.error('删除设备失败:', error)
    ElMessage.error(t('app.deleteDeviceFailedRetry'))
  }
}

const cancelDelete = () => {
  deleteConfirmDialogVisible.value = false
  deleteConfirmDialogData.node = null
  deleteConfirmDialogData.impactToken = ''
  deleteConfirmDialogData.environmentChanges = []
}

const isDeleteConfirmDialogOpen = computed(() => deleteConfirmDialogVisible.value)
const {
  setDialogRef: setDeleteConfirmDialogRef,
  handleModalKeydown: handleDeleteConfirmDialogKeydown
} = useModalAccessibility(isDeleteConfirmDialogOpen, cancelDelete)

const deleteNodeFromStatus = (nodeId: string) => deleteCurrentNodeWithConfirm(nodeId)

/**
 * 删除规则（edges 由 rules 动态生成）
 */
const deleteRule = async (ruleId: string) => {
  if (!ensurePlaybackClosedForMutation()) return
  if (!ensureBoardDataReady(['rules'])) return
  const ruleToDelete = rules.value.find(r => r.id === ruleId)
  if (!ruleToDelete) return

  try {
    await ElMessageBox.confirm(
      t('app.deleteRuleConfirmMessage', { name: ruleToDelete.name || t('app.unnamedRule') }),
      t('app.deleteRuleConfirmTitle'),
      {
        type: 'warning',
        confirmButtonText: t('app.delete'),
        cancelButtonText: t('app.cancel')
      }
    )
  } catch (error: any) {
    if (error === 'cancel' || error === 'close') return
    console.error('规则删除确认失败', error)
    return
  }

  await enqueueBoardMutation(async () => {
    try {
      const mutation = await boardApi.removeRule(ruleId)
      rules.value = mutation.currentItems
      if (focusedRuleId.value === ruleId) {
        focusedRuleId.value = null
      }
      syncRuleDerivedEdges()
      ElMessage.success(t('app.deleteRuleSuccess'))
    } catch (error: any) {
      console.error('删除规则失败', error)
      const refreshed = await refreshRules()
      if (refreshed && !rules.value.some(rule => rule.id === ruleId)) {
        ElMessage.warning(t('app.ruleDeleteOutcomeRefreshed'))
        return
      }
      ElMessage.error(localizedErrorMessage(error, t('app.deleteRuleFailed'), locale.value))
    }
  })
}

const moveRule = async (ruleId: string, direction: 'up' | 'down') => {
  if (!ensurePlaybackClosedForMutation() || rulesReordering.value) return
  if (!ensureBoardDataReady(['rules'])) return
  rulesReordering.value = true
  try {
    await enqueueBoardMutation(async () => {
      const currentIndex = rules.value.findIndex(rule => rule.id === ruleId)
      const targetIndex = direction === 'up' ? currentIndex - 1 : currentIndex + 1
      if (currentIndex < 0 || targetIndex < 0 || targetIndex >= rules.value.length) return

      const reordered = [...rules.value]
      const movedRule = reordered[currentIndex]
      reordered[currentIndex] = reordered[targetIndex]
      reordered[targetIndex] = movedRule
      const requestedOrder = reordered.map(rule => String(rule.id || ''))
      try {
        rules.value = await boardApi.reorderRules(requestedOrder)
        syncRuleDerivedEdges()
        focusedRuleId.value = ruleId
        ElMessage.success(t('app.ruleOrderUpdated'))
      } catch (error: any) {
        console.error('规则执行顺序保存失败', error)
        const refreshed = await refreshRules()
        const currentOrder = rules.value.map(rule => String(rule.id || ''))
        if (!isDefinitiveMutationRejection(error)
          && refreshed && currentOrder.length === requestedOrder.length
          && currentOrder.every((id, index) => id === requestedOrder[index])) {
          focusedRuleId.value = ruleId
          ElMessage.warning(t('app.ruleOrderOutcomeRefreshed'))
        } else {
          ElMessage.error(extractApiErrorMessage(error, t('app.ruleOrderUpdateFailed')))
        }
      }
    })
  } finally {
    rulesReordering.value = false
  }
}

const deleteSpecification = async (specId: string) => {
  if (!ensurePlaybackClosedForMutation()) return
  if (!ensureBoardDataReady(['specs'])) return
  const specToDelete = specifications.value.find(s => s.id === specId)
  if (!specToDelete) return

  try {
    await ElMessageBox.confirm(
      t('app.deleteSpecConfirmMessage', {
        name: getSpecResultDisplayTitle(specToDelete, 0) || t('app.unnamedSpecification')
      }),
      t('app.deleteSpecConfirmTitle'),
      {
        type: 'warning',
        confirmButtonText: t('app.delete'),
        cancelButtonText: t('app.cancel')
      }
    )
  } catch (error: any) {
    if (error === 'cancel' || error === 'close') return
    console.error('规约删除确认失败', error)
    return
  }

  await enqueueBoardMutation(async () => {
    try {
      const mutation = await boardApi.removeSpec(specId)
      specifications.value = mutation.currentItems
      if (focusedSpecId.value === specId) {
        focusedSpecId.value = null
      }
      ElMessage.success(t('app.deleteSpecSuccess'))
    } catch (error: any) {
      console.error('删除规约失败', error)
      const refreshed = await refreshSpecifications()
      if (refreshed && !specifications.value.some(spec => spec.id === specId)) {
        ElMessage.warning(t('app.specDeleteOutcomeRefreshed'))
        return
      }
      ElMessage.error(localizedErrorMessage(error, t('app.deleteSpecFailed'), locale.value))
    }
  })
}

/* =================================================================================
 * 9. API Interactions (Save)
 * ================================================================================= */

const buildBoardLayoutPayload = (): BoardLayoutDto => {
  return {
    canvasPan: { x: canvasPan.value.x, y: canvasPan.value.y },
    canvasZoom: canvasZoom.value,
    panels: {
      control: {
        collapsed: boardPanels.control.collapsed,
        width: boardPanels.control.width,
        activeSection: boardPanels.control.activeSection
      },
      inspector: {
        collapsed: boardPanels.inspector.collapsed,
        width: boardPanels.inspector.width,
        activeSection: boardPanels.inspector.activeSection
      }
    }
  }
}

const applyBoardLayout = (layout?: BoardLayoutDto | null) => {
  if (!layout) return

  if (layout.canvasPan) {
    canvasPan.value = {
      x: Number.isFinite(layout.canvasPan.x) ? layout.canvasPan.x : 0,
      y: Number.isFinite(layout.canvasPan.y) ? layout.canvasPan.y : 0
    }
  }
  if (typeof layout.canvasZoom === 'number') {
    canvasZoom.value = Math.min(MAX_ZOOM, Math.max(MIN_ZOOM, layout.canvasZoom))
  }

  const shouldApplyPanelLayout = !panelStateTouchedBeforeLayout
  const control = layout.panels?.control
  if (control && shouldApplyPanelLayout) {
    boardPanels.control.collapsed = Boolean(control.collapsed)
    boardPanels.control.width = clampPanelWidth(control.width, DEFAULT_CONTROL_PANEL_WIDTH)
    boardPanels.control.activeSection = isControlCenterSection(control.activeSection)
      ? control.activeSection
      : 'devices'
  }

  const inspector = layout.panels?.inspector
  if (inspector && shouldApplyPanelLayout) {
    boardPanels.inspector.collapsed = Boolean(inspector.collapsed)
    boardPanels.inspector.width = clampPanelWidth(inspector.width, DEFAULT_INSPECTOR_PANEL_WIDTH)
    boardPanels.inspector.activeSection = isInspectorSection(inspector.activeSection)
      ? inspector.activeSection
      : 'devices'
  }

  applyViewportPanelConstraints()
}

type QueuedBoardLayoutSave = {
  payload: BoardLayoutDto
  silent: boolean
  resolve: Array<(saved: boolean) => void>
}

let pendingBoardLayoutSave: QueuedBoardLayoutSave | null = null
let boardLayoutSaveDrainRunning = false
let boardLayoutSaveIdleResolvers: Array<() => void> = []

const persistBoardLayout = async (request: QueuedBoardLayoutSave): Promise<boolean> => {
  if (!getToken()) return false
  try {
    await boardApi.saveLayout(request.payload)
    persistedWideLayout = request.payload
    layoutSaveErrorShown = false
    return true
  } catch (e) {
    const mayShowFeedback = !request.silent
      && !layoutSaveFeedbackSuppressed
      && !boardLifecycleDisposed
      && Boolean(getToken())
    if (mayShowFeedback) {
      console.error('保存画布布局失败', e)
      if (!layoutSaveErrorShown) {
        layoutSaveErrorShown = true
        ElMessage.error(t('app.saveLayoutFailed'))
      }
    }
    return false
  }
}

const drainBoardLayoutSaveQueue = async () => {
  if (boardLayoutSaveDrainRunning) return
  boardLayoutSaveDrainRunning = true
  try {
    while (pendingBoardLayoutSave) {
      const request = pendingBoardLayoutSave
      pendingBoardLayoutSave = null
      const saved = await persistBoardLayout(request)
      request.resolve.forEach(resolve => resolve(saved))
    }
  } finally {
    boardLayoutSaveDrainRunning = false
    const idleResolvers = boardLayoutSaveIdleResolvers
    boardLayoutSaveIdleResolvers = []
    idleResolvers.forEach(resolve => resolve())
  }
}

const waitForBoardLayoutSaveIdle = (): Promise<void> => {
  if (!boardLayoutSaveDrainRunning && !pendingBoardLayoutSave) return Promise.resolve()
  return new Promise(resolve => boardLayoutSaveIdleResolvers.push(resolve))
}

const saveBoardLayout = (options: { silent?: boolean } = {}): Promise<boolean> => {
  if (!getToken()) return Promise.resolve(false)
  const payload = buildBoardLayoutPayload()
  return new Promise(resolve => {
    if (pendingBoardLayoutSave) {
      pendingBoardLayoutSave.payload = payload
      pendingBoardLayoutSave.silent = options.silent === true
      pendingBoardLayoutSave.resolve.push(resolve)
    } else {
      pendingBoardLayoutSave = {
        payload,
        silent: options.silent === true,
        resolve: [resolve]
      }
    }
    void drainBoardLayoutSaveQueue()
  })
}

const flushPendingBoardLayout = async (options: {
  silent?: boolean
  timeoutMs?: number
} = {}): Promise<boolean> => {
  const hasPendingSave = layoutSaveTimer !== null
  if (layoutSaveTimer) {
    clearTimeout(layoutSaveTimer)
    layoutSaveTimer = null
  }

  const flush = async () => {
    let saved = true
    if (hasPendingSave && layoutHydrated.value && getToken() && !isNarrowViewport()) {
      saved = await saveBoardLayout({ silent: options.silent })
    }
    await waitForBoardLayoutSaveIdle()
    return saved
  }

  if (!options.timeoutMs || options.timeoutMs <= 0) return flush()

  let timeout: ReturnType<typeof setTimeout> | null = null
  try {
    return await Promise.race([
      flush(),
      new Promise<boolean>(resolve => {
        timeout = setTimeout(() => resolve(false), options.timeoutMs)
      })
    ])
  } finally {
    if (timeout) clearTimeout(timeout)
  }
}

const scheduleBoardLayoutSave = () => {
  if (!layoutHydrated.value || boardLifecycleDisposed || !getToken() || isNarrowViewport()) return
  if (layoutSaveTimer) {
    clearTimeout(layoutSaveTimer)
  }
  layoutSaveTimer = setTimeout(() => {
    layoutSaveTimer = null
    void saveBoardLayout()
  }, LAYOUT_SAVE_DEBOUNCE_MS)
}

watch(
  () => [
    canvasPan.value.x,
    canvasPan.value.y,
    canvasZoom.value,
    boardPanels.control.collapsed,
    boardPanels.control.width,
    boardPanels.control.activeSection,
    boardPanels.inspector.collapsed,
    boardPanels.inspector.width,
    boardPanels.inspector.activeSection
  ],
  scheduleBoardLayoutSave
)

const openControlSection = (section: InspectorSection) => {
  const controlSection: ControlCenterSection = section === 'rules'
    ? 'rules'
    : section === 'specs'
      ? 'specs'
      : 'devices'

  if (!layoutHydrated.value) {
    panelStateTouchedBeforeLayout = true
  }
  boardPanels.control.collapsed = false
  boardPanels.control.activeSection = controlSection
}

const handleControlCollapsedUpdate = (value: boolean) => {
  if (!layoutHydrated.value) {
    panelStateTouchedBeforeLayout = true
  }
  boardPanels.control.collapsed = value
}

const handleControlActiveSectionUpdate = (value: ControlCenterSection) => {
  if (!layoutHydrated.value) {
    panelStateTouchedBeforeLayout = true
  }
  boardPanels.control.activeSection = value
}

const handleInspectorCollapsedUpdate = (value: boolean) => {
  if (!layoutHydrated.value) {
    panelStateTouchedBeforeLayout = true
  }
  boardPanels.inspector.collapsed = value
}

const handleInspectorActiveSectionUpdate = (value: InspectorSection) => {
  if (!layoutHydrated.value) {
    panelStateTouchedBeforeLayout = true
  }
  boardPanels.inspector.activeSection = value
}

// 从 rules 动态生成 edges（不单独存储到服务器）
const generateEdgesFromRules = (): DeviceEdge[] => {
  const result: DeviceEdge[] = []

  for (const [ruleIndex, rule] of rules.value.entries()) {
    if (!rule.sources || !rule.toId) continue

    const toNode = resolveNodeRef(rule.toId)
    if (!toNode) continue
    
    for (const [sourceIndex, source] of rule.sources.entries()) {
      const fromId = source.fromId
      if (!fromId) continue
      
      const fromNode = resolveNodeRef(fromId)
      if (!fromNode) continue
      
      const { fromPoint, toPoint } = getLinkPoints(fromNode, toNode)
      
      result.push({
        id: `edge_${rule.id}_${sourceIndex}_${fromId}`,
        from: fromNode.id,
        to: toNode.id,
        fromLabel: fromNode.label,
        toLabel: toNode.label,
        fromPos: fromPoint,
        toPos: toPoint,
        fromApi: source.fromApi || '',
        toApi: rule.toApi || '',
        itemType: source.itemType,
        relation: source.relation || '',
        value: source.value === null || source.value === undefined ? '' : String(source.value),
        ruleId: rule.id,
        ruleIndex,
        sourceIndex
      })
    }
  }

  return result
}

const syncRuleDerivedEdges = () => {
  edges.value = generateEdgesFromRules()
}

const ruleBuilderVisible = ref(false)

const refreshDeviceTemplates = async (): Promise<boolean> => {
  templatesLoading.value = true
  boardDataLoadState.templates = 'loading'
  try {
    // A catalog read is side-effect free. Restoring bundled defaults is an explicit,
    // previewed mutation in ControlCenter.
    const res = await boardApi.getDeviceTemplates()
    deviceTemplates.value = res || []
    boardDataLoadState.templates = 'ready'
    return true
  } catch (e) {
    console.error('加载设备模板失败:', e)
    boardDataLoadState.templates = 'error'
    return false
  } finally {
    templatesLoading.value = false
  }
}

const replaceTemplateState = (state: {
  templates: DeviceTemplate[]
  environmentVariables: ModelEnvironmentVariable[]
}) => {
  deviceTemplates.value = state.templates
  environmentVariables.value = state.environmentVariables
  boardDataLoadState.templates = 'ready'
  boardDataLoadState.environment = 'ready'
}

const replaceTemplateCatalog = (templates: DeviceTemplate[]) => {
  deviceTemplates.value = templates
  boardDataLoadState.templates = 'ready'
}



/* =================================================================================
 * 10. Lifecycle & Watchers
 * ================================================================================= */

// 1. 定义刷新设备的函数
const refreshDevices = async (): Promise<boolean> => {
  boardDataLoadState.nodes = 'loading'
  try {
    const loadedNodes = await boardApi.getNodes()
    nodes.value = getVisibleDeviceNodes(loadedNodes)
    syncRuleDerivedEdges()
    boardDataLoadState.nodes = 'ready'
    return true
  } catch(e) {
    console.error('加载设备失败', e)
    boardDataLoadState.nodes = 'error'
    return false
  }
}

const refreshEnvironmentVariables = async (): Promise<boolean> => {
  boardDataLoadState.environment = 'loading'
  try {
    environmentVariables.value = await boardApi.getEnvironment()
    boardDataLoadState.environment = 'ready'
    return true
  } catch (e) {
    console.error('加载环境变量池失败', e)
    boardDataLoadState.environment = 'error'
    return false
  }
}

const refreshBoardSnapshot = async (): Promise<boolean> => {
  allBoardDataKeys.forEach(key => { boardDataLoadState[key] = 'loading' })
  templatesLoading.value = true
  try {
    const snapshot = await boardApi.getSnapshot()
    deviceTemplates.value = snapshot.deviceTemplates
    nodes.value = getVisibleDeviceNodes(snapshot.nodes)
    environmentVariables.value = snapshot.environmentVariables
    rules.value = snapshot.rules
    specifications.value = snapshot.specifications
    syncRuleDerivedEdges()
    allBoardDataKeys.forEach(key => { boardDataLoadState[key] = 'ready' })
    return true
  } catch (error) {
    console.error('加载画布语义快照失败:', error)
    allBoardDataKeys.forEach(key => { boardDataLoadState[key] = 'error' })
    return false
  } finally {
    templatesLoading.value = false
  }
}

const environmentPatchFieldLabel = (field: EnvironmentVariablePatchResult['suppliedFields'][number]) => {
  if (field === 'value') return t('app.variableValue')
  if (field === 'trust') return t('app.sourceLabel')
  return t('app.sensitivityLabel')
}

const formatEnvironmentPatchResults = (results: EnvironmentVariablePatchResult[]) =>
  results.map(result => {
    const fields = result.changedFields.length > 0 ? result.changedFields : result.suppliedFields
    return `${result.name} (${fields.map(environmentPatchFieldLabel).join(', ')})`
  }).join('; ')

const saveEnvironmentVariables = async (patches: ModelEnvironmentVariable[]) => {
  if (!ensurePlaybackClosedForMutation()) return
  if (!ensureBoardDataReady(['nodes', 'templates', 'environment'])) return
  await enqueueBoardMutation(async () => {
    try {
      const mutation = await boardApi.saveEnvironment(patches)
      environmentVariables.value = mutation.environmentVariables
      const changedPatches = mutation.patchResults.filter(result => result.changedFields.length > 0)
      if (changedPatches.length > 0) {
        ElMessage.success(t('app.environmentPatchApplied', {
          items: formatEnvironmentPatchResults(changedPatches)
        }))
      } else {
        ElMessage.info(t('app.environmentPatchUnchanged', {
          items: formatEnvironmentPatchResults(mutation.patchResults)
        }))
      }
      const changedPatchNames = new Set(changedPatches.map(result => result.name))
      reportEnvironmentChanges(mutation.environmentChanges.filter(
        change => !changedPatchNames.has(change.name)
      ))
    } catch (e: any) {
      console.error('保存环境变量池失败', e)
      if (!isDefinitiveMutationRejection(e)) {
        const refreshed = await refreshEnvironmentVariables()
        ElMessage.warning(refreshed
          ? t('app.environmentSaveOutcomeRefreshed')
          : t('app.environmentSaveOutcomeUnknownRefreshFailed'))
      } else {
        ElMessage.error(extractApiErrorMessage(e, t('app.saveEnvironmentFailed')))
      }
    }
  })
}

const normalizeSceneString = (value: unknown, field = 'value') => {
  if (value === undefined || value === null) return ''
  if (typeof value !== 'string') {
    throw new Error(t('app.sceneImportStringRequired', { field }))
  }
  return value.trim()
}

const rejectSceneInternalField = (row: unknown, field: string) => {
  if (row && typeof row === 'object' && Object.prototype.hasOwnProperty.call(row, field)) {
    throw new Error(t('app.sceneImportInternalField', { field }))
  }
}

const assertSceneAllowedFields = (row: unknown, allowedFields: readonly string[], path: string) => {
  if (!row || typeof row !== 'object' || Array.isArray(row)) return
  const allowed = new Set(allowedFields)
  const unknownField = Object.keys(row).find(field => !allowed.has(field))
  if (unknownField) {
    throw new Error(t('app.sceneImportUnknownField', {
      field: path ? `${path}.${unknownField}` : unknownField
    }))
  }
}

const formatIntegerRangeError = (field: string, min: number, max: number) =>
  t('app.integerBetween', { field, min, max })

const requireIntegerInRange = (value: unknown, field: string, min: number, max: number): number => {
  if (typeof value !== 'number' || !Number.isInteger(value)) {
    throw new Error(formatIntegerRangeError(field, min, max))
  }
  if (value < min || value > max) {
    throw new Error(formatIntegerRangeError(field, min, max))
  }
  return value
}

const optionalIntegerInRange = (value: unknown, field: string, fallback: number, min: number, max: number): number => {
  if (value === undefined || value === null) return fallback
  return requireIntegerInRange(value, field, min, max)
}

const normalizeSceneNumber = (
  value: unknown,
  fallback: number,
  field: string,
  min = Number.NEGATIVE_INFINITY,
  max = Number.POSITIVE_INFINITY
) => {
  if (value === undefined || value === null) return fallback
  if (typeof value !== 'number' || !Number.isFinite(value)) {
    throw new Error(t('app.sceneImportNumberRequired', { field }))
  }
  if (value < min || value > max) {
    throw new Error(t('app.numberBetween', { field, min, max }))
  }
  return value
}

const normalizeSceneTrust = (value: unknown, field: string): 'trusted' | 'untrusted' | null => {
  const normalized = normalizeSceneString(value, field)
  if (!normalized) return null
  if (normalized === 'trusted' || normalized === 'untrusted') return normalized
  throw new Error(t('app.sceneImportInvalidEnum', { field, value: normalized }))
}

const normalizeScenePrivacy = (value: unknown, field: string): 'public' | 'private' | null => {
  const normalized = normalizeSceneString(value, field)
  if (!normalized) return null
  if (normalized === 'public' || normalized === 'private') return normalized
  throw new Error(t('app.sceneImportInvalidEnum', { field, value: normalized }))
}

const normalizeSceneVariables = (value: unknown, field: string) => {
  if (value === undefined || value === null) return undefined
  if (!Array.isArray(value)) throw new Error(t('app.sceneImportArrayRequired', { field }))
  const seenNames = new Set<string>()
  const variables = value
    .map((item, index) => {
      const row = item as any
      if (!row || typeof row !== 'object' || Array.isArray(row)) {
        throw new Error(t('app.sceneImportObjectRequired', { field: `${field}[${index}]` }))
      }
      assertSceneAllowedFields(row, ['name', 'value', 'trust'], `${field}[${index}]`)
      const name = normalizeSceneString(row?.name, `${field}[${index}].name`)
      if (!name) throw new Error(t('app.sceneImportMissingField', { field: `${field}[${index}].name` }))
      if (seenNames.has(name)) {
        throw new Error(t('app.sceneImportDuplicateRuntimeEntry', { field, name }))
      }
      seenNames.add(name)
      if (!Object.prototype.hasOwnProperty.call(row, 'value')) {
        throw new Error(t('app.sceneImportMissingField', { field: `${field}[${index}].value` }))
      }
      const normalizedValue = normalizeSceneString(row?.value, `${field}[${index}].value`)
      if (!normalizedValue) {
        throw new Error(t('app.sceneImportMissingField', { field: `${field}[${index}].value` }))
      }
      return {
        name,
        value: normalizedValue,
        ...(row?.trust !== undefined && row?.trust !== null
          ? { trust: normalizeSceneTrust(row.trust, `${field}[${index}].trust`) || undefined }
          : {})
      }
    })
  return variables.length > 0 ? variables : undefined
}

const normalizeScenePrivacies = (value: unknown, field: string) => {
  if (value === undefined || value === null) return undefined
  if (!Array.isArray(value)) throw new Error(t('app.sceneImportArrayRequired', { field }))
  const seenNames = new Set<string>()
  const privacies = value
    .map((item, index) => {
      const row = item as any
      if (!row || typeof row !== 'object' || Array.isArray(row)) {
        throw new Error(t('app.sceneImportObjectRequired', { field: `${field}[${index}]` }))
      }
      assertSceneAllowedFields(row, ['name', 'privacy'], `${field}[${index}]`)
      const name = normalizeSceneString(row?.name, `${field}[${index}].name`)
      if (!name) throw new Error(t('app.sceneImportMissingField', { field: `${field}[${index}].name` }))
      if (seenNames.has(name)) {
        throw new Error(t('app.sceneImportDuplicateRuntimeEntry', { field, name }))
      }
      seenNames.add(name)
      const privacy = normalizeScenePrivacy(row?.privacy, `${field}[${index}].privacy`)
      if (!privacy) throw new Error(t('app.sceneImportMissingField', { field: `${field}[${index}].privacy` }))
      return { name, privacy }
    })
  return privacies.length > 0 ? privacies : undefined
}

const normalizeSceneDevice = (value: unknown, index: number): NormalizedSceneDevice => {
  const row = value as any
  if (!row || typeof row !== 'object' || Array.isArray(row)) {
    throw new Error(t('app.sceneImportObjectRequired', { field: `devices[${index}]` }))
  }
  assertSceneAllowedFields(row, [
    'id', 'templateName', 'label', 'position', 'state', 'width', 'height',
    'currentStateTrust', 'currentStatePrivacy', 'variables', 'privacies'
  ], `devices[${index}]`)
  const id = normalizeSceneString(row.id, `devices[${index}].id`)
  const templateName = normalizeSceneString(row.templateName, `devices[${index}].templateName`)
  const label = normalizeSceneString(row.label, `devices[${index}].label`)
  if (!id) throw new Error(t('app.sceneImportMissingField', { field: `devices[${index}].id` }))
  if (!templateName) throw new Error(t('app.sceneImportMissingField', { field: `devices[${index}].templateName` }))
  if (!label) throw new Error(t('app.sceneImportMissingField', { field: `devices[${index}].label` }))
  if (!row.position || typeof row.position !== 'object' || Array.isArray(row.position)) {
    throw new Error(t('app.sceneImportObjectRequired', { field: `devices[${index}].position` }))
  }
  assertSceneAllowedFields(row.position, ['x', 'y'], `devices[${index}].position`)
  if (row.position.x === undefined || row.position.x === null) {
    throw new Error(t('app.sceneImportMissingField', { field: `devices[${index}].position.x` }))
  }
  if (row.position.y === undefined || row.position.y === null) {
    throw new Error(t('app.sceneImportMissingField', { field: `devices[${index}].position.y` }))
  }
  const state = normalizeSceneString(row.state, `devices[${index}].state`)
  const variables = normalizeSceneVariables(row.variables, `devices[${index}].variables`)
  const privacies = normalizeScenePrivacies(row.privacies, `devices[${index}].privacies`)

  return {
    id,
    templateName,
    label,
    position: {
      x: normalizeSceneNumber(
        row.position?.x,
        0,
        `devices[${index}].position.x`,
        -NODE_POSITION_ABS_MAX,
        NODE_POSITION_ABS_MAX
      ),
      y: normalizeSceneNumber(
        row.position?.y,
        0,
        `devices[${index}].position.y`,
        -NODE_POSITION_ABS_MAX,
        NODE_POSITION_ABS_MAX
      )
    },
    state: state || 'Working',
    width: requireIntegerInRange(
      row.width,
      `devices[${index}].width`,
      NODE_WIDTH_RANGE.min,
      NODE_WIDTH_RANGE.max
    ),
    height: requireIntegerInRange(
      row.height,
      `devices[${index}].height`,
      NODE_HEIGHT_RANGE.min,
      NODE_HEIGHT_RANGE.max
    ),
    ...(row.currentStateTrust !== undefined && row.currentStateTrust !== null
      ? { currentStateTrust: normalizeSceneTrust(row.currentStateTrust, `devices[${index}].currentStateTrust`) || undefined }
      : {}),
    ...(row.currentStatePrivacy !== undefined && row.currentStatePrivacy !== null
      ? { currentStatePrivacy: normalizeScenePrivacy(row.currentStatePrivacy, `devices[${index}].currentStatePrivacy`) || undefined }
      : {}),
    ...(variables ? { variables } : {}),
    ...(privacies ? { privacies } : {})
  }
}

const sceneTemplateForDevice = (
  device: Pick<DeviceNode, 'templateName'>,
  templates: DeviceTemplate[]
): DeviceTemplate | undefined => templates.find(template =>
  [template.name, template.manifest?.Name]
    .map(normalizeTemplateLookupName)
    .includes(normalizeTemplateLookupName(device.templateName)))

const sceneTemplateHasStateMachine = (template?: DeviceTemplate): boolean =>
  Boolean(template?.manifest?.Modes?.length && template.manifest?.WorkingStates?.length)

const assertSceneDeviceRuntimeShape = (
  rawDevices: unknown[],
  devices: DeviceNode[],
  templates: DeviceTemplate[]
) => {
  devices.forEach((device, index) => {
    const template = sceneTemplateForDevice(device, templates)
    if (!template) return
    const raw = rawDevices[index] as any
    const rawState = normalizeSceneString(raw?.state, `devices[${index}].state`)
    const hasStateMachine = sceneTemplateHasStateMachine(template)
    if (hasStateMachine && !rawState) {
      throw new Error(t('app.sceneImportStateRequiredForStatefulDevice', { index: index + 1, label: device.label }))
    }
    if (!hasStateMachine && rawState) {
      throw new Error(t('app.sceneImportStateForbiddenForStatelessDevice', { index: index + 1, label: device.label }))
    }
    if (!hasStateMachine && (raw?.currentStateTrust !== undefined || raw?.currentStatePrivacy !== undefined)) {
      throw new Error(t('app.sceneImportStateLabelsForbiddenForStatelessDevice', { index: index + 1, label: device.label }))
    }
  })
}

const normalizeSceneEnvironmentVariables = (value: unknown): ModelEnvironmentVariable[] => {
  if (value === undefined || value === null) return []
  if (!Array.isArray(value)) throw new Error(t('app.sceneImportArrayRequired', { field: 'environmentVariables' }))
  const seenNames = new Set<string>()
  return value.map((item, index) => {
    const row = item as any
    if (!row || typeof row !== 'object' || Array.isArray(row)) {
      throw new Error(t('app.sceneImportObjectRequired', { field: `environmentVariables[${index}]` }))
    }
    assertSceneAllowedFields(row, ['name', 'value', 'trust', 'privacy'], `environmentVariables[${index}]`)
    const name = normalizeSceneString(row.name, `environmentVariables[${index}].name`)
    if (!name) throw new Error(t('app.sceneImportMissingField', { field: `environmentVariables[${index}].name` }))
    if (!Object.prototype.hasOwnProperty.call(row, 'value')) {
      throw new Error(t('app.sceneImportEnvironmentValueRequired', { name }))
    }
    if (seenNames.has(name)) {
      throw new Error(t('app.sceneImportDuplicateEnvironmentVariable', { name }))
    }
    seenNames.add(name)
    const trust = normalizeSceneTrust(row.trust, `environmentVariables[${index}].trust`)
    const privacy = normalizeScenePrivacy(row.privacy, `environmentVariables[${index}].privacy`)
    const normalizedValue = normalizeSceneString(row.value, `environmentVariables[${index}].value`)
    if (!normalizedValue) throw new Error(t('app.sceneImportEnvironmentValueRequired', { name }))
    if (!trust) throw new Error(t('app.sceneImportMissingField', { field: `environmentVariables[${index}].trust` }))
    if (!privacy) throw new Error(t('app.sceneImportMissingField', { field: `environmentVariables[${index}].privacy` }))
    return {
      name,
      value: normalizedValue,
      trust,
      privacy
    }
  })
}

const normalizeSceneRuleSourceType = (value: unknown, field = 'rules.sources.itemType'): RuleSourceItemType => {
  const normalized = normalizeSceneString(value, field).toLowerCase()
  if (normalized === 'api' || normalized === 'variable' || normalized === 'mode' || normalized === 'state') {
    return normalized
  }
  throw new Error(t('app.sceneImportInvalidEnum', { field: 'rules.sources.itemType', value: normalized || t('app.empty') }))
}

const normalizeSceneRules = (value: unknown): RuleForm[] => {
  if (value === undefined || value === null) return []
  if (!Array.isArray(value)) throw new Error(t('app.sceneImportArrayRequired', { field: 'rules' }))
  return value.map((item, index) => {
    const row = item as any
    if (!row || typeof row !== 'object' || Array.isArray(row)) {
      throw new Error(t('app.sceneImportObjectRequired', { field: `rules[${index}]` }))
    }
    rejectSceneInternalField(row, 'id')
    assertSceneAllowedFields(row, ['name', 'sources', 'toId', 'toApi', 'contentDevice', 'content'], `rules[${index}]`)
    const sources = Array.isArray(row.sources) ? row.sources : []
    if (sources.length === 0) throw new Error(t('app.sceneImportMissingField', { field: `rules[${index}].sources` }))
    const name = normalizeSceneString(row.name, `rules[${index}].name`)
    const toId = normalizeSceneString(row.toId, `rules[${index}].toId`)
    const toApi = normalizeSceneString(row.toApi, `rules[${index}].toApi`)
    if (!toId) throw new Error(t('app.sceneImportMissingField', { field: `rules[${index}].toId` }))
    if (!toApi) throw new Error(t('app.sceneImportMissingField', { field: `rules[${index}].toApi` }))
    const contentDevice = normalizeSceneString(row.contentDevice, `rules[${index}].contentDevice`)
    const content = normalizeSceneString(row.content, `rules[${index}].content`)
    return {
      ...(name ? { name } : {}),
      sources: sources.map((source: any, sourceIndex: number) => {
        if (!source || typeof source !== 'object' || Array.isArray(source)) {
          throw new Error(t('app.sceneImportObjectRequired', { field: `rules[${index}].sources[${sourceIndex}]` }))
        }
        assertSceneAllowedFields(
          source,
          ['fromId', 'fromApi', 'itemType', 'relation', 'value'],
          `rules[${index}].sources[${sourceIndex}]`
        )
        const sourceField = `rules[${index}].sources[${sourceIndex}]`
        const itemType = normalizeSceneRuleSourceType(source?.itemType, `${sourceField}.itemType`)
        const fromId = normalizeSceneString(source?.fromId, `${sourceField}.fromId`)
        const fromApi = normalizeSceneString(source?.fromApi, `${sourceField}.fromApi`)
        if (!fromId) throw new Error(t('app.sceneImportMissingField', { field: `rules[${index}].sources[${sourceIndex}].fromId` }))
        if (!fromApi) throw new Error(t('app.sceneImportMissingField', { field: `rules[${index}].sources[${sourceIndex}].fromApi` }))
        if (itemType === 'api' && (
          normalizeSceneString(source?.relation, `${sourceField}.relation`)
          || normalizeSceneString(source?.value, `${sourceField}.value`)
        )) {
          throw new Error(t('app.sceneImportUnexpectedRuleSignalValue', {
            field: `rules[${index}].sources[${sourceIndex}]`
          }))
        }
        const relation = normalizeSceneString(source?.relation, `${sourceField}.relation`)
        const conditionValue = normalizeSceneString(source?.value, `${sourceField}.value`)
        if (itemType !== 'api' && !relation) {
          throw new Error(t('app.sceneImportMissingField', { field: `rules[${index}].sources[${sourceIndex}].relation` }))
        }
        if (itemType !== 'api' && !conditionValue) {
          throw new Error(t('app.sceneImportMissingField', { field: `rules[${index}].sources[${sourceIndex}].value` }))
        }
        const normalizedRelation = itemType === 'api' ? '' : normalizeModelRelation(relation)
        if (itemType !== 'api' && !normalizedRelation) {
          throw new Error(t('app.sceneImportInvalidEnum', {
            field: `rules[${index}].sources[${sourceIndex}].relation`,
            value: relation
          }))
        }
        return {
          fromId,
          fromApi,
          itemType,
          ...(itemType === 'api' ? {} : {
            relation: normalizedRelation,
            value: conditionValue
          })
        }
      }),
      toId,
      toApi,
      ...(contentDevice ? { contentDevice } : {}),
      ...(content ? { content } : {})
    }
  })
}

const normalizeSceneSpecTargetType = (value: unknown, field = 'specs.conditions.targetType') => {
  const normalized = normalizeSceneString(value, field).toLowerCase()
  if (['state', 'mode', 'variable', 'api', 'trust', 'privacy'].includes(normalized)) {
    return normalized as SpecCondition['targetType']
  }
  throw new Error(t('app.sceneImportInvalidEnum', { field: 'specs.conditions.targetType', value: normalized || t('app.empty') }))
}

const normalizeSceneSpecConditions = (
  value: unknown,
  side: SpecCondition['side'],
  field: string,
  idPrefix: string
): SpecCondition[] => {
  if (value === undefined || value === null) return []
  if (!Array.isArray(value)) throw new Error(t('app.sceneImportArrayRequired', { field }))
  return value.map((item, index) => {
    const row = item as any
    if (!row || typeof row !== 'object' || Array.isArray(row)) {
      throw new Error(t('app.sceneImportObjectRequired', { field: `${field}[${index}]` }))
    }
    rejectSceneInternalField(row, 'id')
    rejectSceneInternalField(row, 'side')
    rejectSceneInternalField(row, 'deviceLabel')
    assertSceneAllowedFields(
      row,
      ['deviceId', 'targetType', 'key', 'propertyScope', 'relation', 'value'],
      `${field}[${index}]`
    )
    const conditionField = `${field}[${index}]`
    const deviceId = normalizeSceneString(row.deviceId, `${conditionField}.deviceId`)
    const targetType = normalizeSceneSpecTargetType(row.targetType, `${conditionField}.targetType`)
    const key = normalizeSceneString(row.key, `${conditionField}.key`)
    const propertyScope = normalizeSceneString(row.propertyScope, `${conditionField}.propertyScope`).toLowerCase()
    const isPropertyCondition = targetType === 'trust' || targetType === 'privacy'
    if (!deviceId) throw new Error(t('app.sceneImportMissingField', { field: `${field}[${index}].deviceId` }))
    if (!key) throw new Error(t('app.sceneImportMissingField', { field: `${field}[${index}].key` }))
    if (isPropertyCondition && !['state', 'variable'].includes(propertyScope)) {
      throw new Error(t('app.sceneImportInvalidEnum', {
        field: `${field}[${index}].propertyScope`,
        value: propertyScope || t('app.empty')
      }))
    }
    if (!isPropertyCondition && propertyScope) {
      throw new Error(t('app.sceneImportUnexpectedField', { field: `${field}[${index}].propertyScope` }))
    }
    const relation = normalizeSceneString(row.relation, `${conditionField}.relation`)
    const conditionValue = normalizeSceneString(row.value, `${conditionField}.value`)
    if (!relation) throw new Error(t('app.sceneImportMissingField', { field: `${field}[${index}].relation` }))
    if (!conditionValue) throw new Error(t('app.sceneImportMissingField', { field: `${field}[${index}].value` }))
    const normalizedRelation = normalizeModelRelation(relation)
    if (!normalizedRelation) {
      throw new Error(t('app.sceneImportInvalidEnum', { field: `${field}[${index}].relation`, value: relation }))
    }
    return {
      id: `${idPrefix}_${index + 1}`,
      side,
      deviceId,
      deviceLabel: deviceId,
      targetType,
      key,
      ...(isPropertyCondition ? { propertyScope: propertyScope as 'state' | 'variable' } : {}),
      relation: normalizedRelation,
      value: conditionValue
    }
  })
}

const normalizeSceneSpecs = (value: unknown): Specification[] => {
  if (value === undefined || value === null) return []
  if (!Array.isArray(value)) throw new Error(t('app.sceneImportArrayRequired', { field: 'specs' }))
  return value.map((item, index) => {
    const row = item as any
    if (!row || typeof row !== 'object' || Array.isArray(row)) {
      throw new Error(t('app.sceneImportObjectRequired', { field: `specs[${index}]` }))
    }
    rejectSceneInternalField(row, 'id')
    rejectSceneInternalField(row, 'templateLabel')
    rejectSceneInternalField(row, 'formula')
    rejectSceneInternalField(row, 'devices')
    assertSceneAllowedFields(
      row,
      ['templateId', 'aConditions', 'ifConditions', 'thenConditions'],
      `specs[${index}]`
    )
    const templateId = normalizeSceneString(row.templateId, `specs[${index}].templateId`) as Specification['templateId']
    if (!defaultSpecTemplates.some(template => template.id === templateId)) {
      throw new Error(t('app.sceneImportInvalidEnum', { field: `specs[${index}].templateId`, value: templateId || t('app.empty') }))
    }
    const template = specTemplateDetails.find(candidate => candidate.id === templateId)
    const templateLabel = defaultSpecTemplates.find(candidate => candidate.id === templateId)?.label || templateId
    const aConditions = normalizeSceneSpecConditions(row.aConditions, 'a', `specs[${index}].aConditions`, `spec_${index + 1}_a`)
    const ifConditions = normalizeSceneSpecConditions(row.ifConditions, 'if', `specs[${index}].ifConditions`, `spec_${index + 1}_if`)
    const thenConditions = normalizeSceneSpecConditions(row.thenConditions, 'then', `specs[${index}].thenConditions`, `spec_${index + 1}_then`)
    const conditionsBySide = { a: aConditions, if: ifConditions, then: thenConditions }
    for (const side of ['a', 'if', 'then'] as const) {
      const field = `specs[${index}].${side === 'a' ? 'aConditions' : `${side}Conditions`}`
      const required = template?.requiredSides.includes(side) === true
      if (required && conditionsBySide[side].length === 0) {
        throw new Error(t('app.sceneImportMissingField', { field }))
      }
      if (!required && conditionsBySide[side].length > 0) {
        throw new Error(t('app.sceneImportUnexpectedField', { field }))
      }
    }
    return {
      id: `scene_spec_${index + 1}`,
      templateId,
      templateLabel,
      aConditions,
      ifConditions,
      thenConditions,
      devices: []
    }
  })
}

const normalizeSceneTemplates = (value: unknown): DeviceTemplate[] => {
  if (value === undefined || value === null) return []
  if (!Array.isArray(value)) throw new Error(t('app.sceneImportArrayRequired', { field: 'templates' }))
  return value.map((item, index) => {
    const row = item as any
    if (!row || typeof row !== 'object' || Array.isArray(row)) {
      throw new Error(t('app.sceneImportObjectRequired', { field: `templates[${index}]` }))
    }
    rejectSceneInternalField(row, 'id')
    rejectSceneInternalField(row, 'defaultTemplate')
    assertSceneAllowedFields(row, ['name', 'manifest'], `templates[${index}]`)
    const manifest = row.manifest
    const name = normalizeSceneString(row.name, `templates[${index}].name`)
    if (!name) throw new Error(t('app.sceneImportMissingField', { field: `templates[${index}].name` }))
    if (!manifest || typeof manifest !== 'object' || Array.isArray(manifest)) {
      throw new Error(t('app.sceneImportMissingField', { field: `templates[${index}].manifest` }))
    }
    const manifestName = normalizeSceneString(manifest.Name, `templates[${index}].manifest.Name`)
    if (!manifestName) {
      throw new Error(t('app.sceneImportMissingField', { field: `templates[${index}].manifest.Name` }))
    }
    if (name !== manifestName) {
      throw new Error(t('app.sceneImportTemplateNameMismatch', { name, manifestName }))
    }
    const validation = validateManifest(manifest)
    if (!validation.valid) {
      throw new Error(t('app.sceneImportInvalidTemplateManifest', {
        name,
        reason: validation.msg || t('app.unknownOmissionReason')
      }))
    }
    return {
      name,
      manifest: deepClone(manifest)
    }
  })
}

const assertSceneTemplateCoverage = (scene: Pick<BoardSceneModel, 'templates' | 'devices'>) => {
  const referencedNames = new Map<string, string>()
  scene.devices.forEach(device => {
    referencedNames.set(normalizeTemplateLookupName(device.templateName), device.templateName)
  })

  const snapshotByAlias = new Map<string, DeviceTemplate>()
  const matchedSnapshots = new Set<DeviceTemplate>()
  for (const template of scene.templates) {
    const aliases = [template.name, template.manifest?.Name]
      .map(normalizeTemplateLookupName)
      .filter(Boolean)
    for (const alias of aliases) {
      const previous = snapshotByAlias.get(alias)
      if (previous && previous !== template) {
        throw new Error(t('app.sceneImportDuplicateTemplateSnapshot', { name: template.name || template.manifest?.Name || alias }))
      }
      snapshotByAlias.set(alias, template)
    }
  }

  for (const [key, displayName] of referencedNames) {
    const snapshot = snapshotByAlias.get(key)
    if (!snapshot) {
      throw new Error(t('app.sceneImportMissingTemplates', { names: displayName }))
    }
    matchedSnapshots.add(snapshot)
  }

  const unreferenced = scene.templates
    .filter(template => !matchedSnapshots.has(template))
    .map(template => template.name || template.manifest?.Name)
    .filter(Boolean)
  if (unreferenced.length > 0) {
    throw new Error(t('app.sceneImportUnreferencedTemplates', { names: unreferenced.join(', ') }))
  }
}

const assertSceneEnvironmentCoverage = (
  scene: Pick<BoardSceneModel, 'templates' | 'devices' | 'environmentVariables'>
) => {
  const templatesByAlias = new Map<string, DeviceTemplate>()
  scene.templates.forEach(template => {
    for (const alias of [template.name, template.manifest?.Name]) {
      const key = normalizeTemplateLookupName(alias)
      if (key) templatesByAlias.set(key, template)
    }
  })

  const requiredNames = new Set<string>()
  scene.devices.forEach(device => {
    const template = templatesByAlias.get(normalizeTemplateLookupName(device.templateName))
    const manifest = template?.manifest
    ;(manifest?.InternalVariables || []).forEach(variable => {
      const name = normalizeSceneString(variable?.Name, 'templates[].manifest.InternalVariables[].Name')
      if (name && variable?.IsInside !== true) requiredNames.add(name)
    })
    ;(manifest?.ImpactedVariables || []).forEach(variableName => {
      const name = normalizeSceneString(variableName, 'templates[].manifest.ImpactedVariables[]')
      if (name) requiredNames.add(name)
    })
  })

  const providedNames = new Set(scene.environmentVariables.map(variable => variable.name))
  const missing = [...requiredNames].filter(name => !providedNames.has(name)).sort(compareSceneText)
  const unknown = [...providedNames].filter(name => !requiredNames.has(name)).sort(compareSceneText)
  if (missing.length > 0) {
    throw new Error(t('app.sceneImportMissingEnvironmentVariables', { names: missing.join(', ') }))
  }
  if (unknown.length > 0) {
    throw new Error(t('app.sceneImportUnknownEnvironmentVariables', { names: unknown.join(', ') }))
  }
}

const assertUniqueSceneDeviceIds = (devices: DeviceNode[]) => {
  const seen = new Set<string>()
  const seenModelIds = new Map<string, DeviceNode>()
  const seenLabels = new Set<string>()
  for (const device of devices) {
    if (seen.has(device.id)) {
      throw new Error(t('app.sceneImportDuplicateDevice', { id: device.id }))
    }
    seen.add(device.id)
    const modelId = normalizeNuSmvDeviceName(device.id)
    const previous = seenModelIds.get(modelId)
    if (previous) {
      throw new Error(t('app.sceneImportModelIdentityCollision', {
        first: previous.label,
        second: device.label
      }))
    }
    seenModelIds.set(modelId, device)
    const labelKey = device.label.trim().toLowerCase()
    if (seenLabels.has(labelKey)) {
      throw new Error(t('app.sceneImportDuplicateDeviceLabel', { label: device.label }))
    }
    seenLabels.add(labelKey)
  }
}

const assertSceneReferences = (scene: Pick<BoardSceneModel, 'devices' | 'rules' | 'specs'>) => {
  const deviceIds = new Set(scene.devices.map(device => device.id))
  scene.rules.forEach((rule, ruleIndex) => {
    rule.sources.forEach((source, sourceIndex) => {
      if (!deviceIds.has(source.fromId)) {
        throw new Error(t('app.sceneImportUnknownDeviceRef', { field: `rules[${ruleIndex}].sources[${sourceIndex}].fromId`, id: source.fromId }))
      }
    })
    if (!deviceIds.has(rule.toId)) {
      throw new Error(t('app.sceneImportUnknownDeviceRef', { field: `rules[${ruleIndex}].toId`, id: rule.toId }))
    }
    if (Boolean(rule.contentDevice) !== Boolean(rule.content)) {
      throw new Error(t('app.sceneImportContentPairRequired', { index: ruleIndex + 1 }))
    }
    if (rule.contentDevice && !deviceIds.has(rule.contentDevice)) {
      throw new Error(t('app.sceneImportUnknownDeviceRef', { field: `rules[${ruleIndex}].contentDevice`, id: rule.contentDevice }))
    }
  })

  const checkSpecCondition = (condition: SpecCondition, field: string) => {
    if (!deviceIds.has(condition.deviceId)) {
      throw new Error(t('app.sceneImportUnknownDeviceRef', { field, id: condition.deviceId }))
    }
  }
  scene.specs.forEach((spec, specIndex) => {
    spec.aConditions.forEach((condition, index) => checkSpecCondition(condition, `specs[${specIndex}].aConditions[${index}].deviceId`))
    spec.ifConditions.forEach((condition, index) => checkSpecCondition(condition, `specs[${specIndex}].ifConditions[${index}].deviceId`))
    spec.thenConditions.forEach((condition, index) => checkSpecCondition(condition, `specs[${specIndex}].thenConditions[${index}].deviceId`))
  })
}

const compareSceneText = (left: string, right: string) =>
  left.localeCompare(right, 'en', { numeric: true, sensitivity: 'base' })

const canonicalPlainValue = (value: unknown): unknown => {
  if (Array.isArray(value)) {
    return value.map(item => canonicalPlainValue(item))
  }
  if (value && typeof value === 'object') {
    return Object.keys(value as Record<string, unknown>)
      .sort(compareSceneText)
      .reduce<Record<string, unknown>>((result, key) => {
        const nextValue = canonicalPlainValue((value as Record<string, unknown>)[key])
        if (nextValue !== undefined) result[key] = nextValue
        return result
      }, {})
  }
  return value
}

const sceneJsonKey = (value: unknown) =>
  JSON.stringify(canonicalPlainValue(value))

const sortSceneItems = <T,>(items: T[], key: (item: T) => unknown) =>
  [...items].sort((left, right) => compareSceneText(sceneJsonKey(key(left)), sceneJsonKey(key(right))))

const canonicalSceneDevice = (
  device: DeviceNode,
  index: number,
  templates: DeviceTemplate[]
): PortableSceneDevice => {
  const normalized = normalizeSceneDevice(device, index)
  const variables = sortSceneItems((normalized.variables || []).map(variable => ({
    name: variable.name,
    value: variable.value,
    ...(variable.trust ? { trust: variable.trust } : {})
  })), variable => variable.name)

  const privacies = sortSceneItems((normalized.privacies || []).map(privacy => ({
    name: privacy.name,
    privacy: privacy.privacy
  })), privacy => privacy.name)

  const { state, currentStateTrust, currentStatePrivacy, ...portable } = normalized
  const hasStateMachine = sceneTemplateHasStateMachine(sceneTemplateForDevice(normalized, templates))
  return {
    ...portable,
    ...(hasStateMachine ? {
      state,
      ...(currentStateTrust ? { currentStateTrust } : {}),
      ...(currentStatePrivacy ? { currentStatePrivacy } : {})
    } : {}),
    ...(variables.length > 0 ? { variables } : {}),
    ...(privacies.length > 0 ? { privacies } : {})
  }
}

const canonicalSceneEnvironmentVariable = (
  variable: ModelEnvironmentVariable,
  index: number
): PortableSceneEnvironmentVariable => {
  const field = `environmentVariables[${index}]`
  const name = normalizeSceneString(variable.name, `${field}.name`)
  if (!name) throw new Error(t('app.sceneImportMissingField', { field: `${field}.name` }))
  const value = normalizeSceneString(variable.value, `${field}.value`)
  if (!value) throw new Error(t('app.sceneImportEnvironmentValueRequired', { name: name || t('app.empty') }))
  const trust = normalizeSceneTrust(variable.trust, `${field}.trust`)
  const privacy = normalizeScenePrivacy(variable.privacy, `${field}.privacy`)
  if (!trust) throw new Error(t('app.sceneImportMissingField', { field: `${field}.trust` }))
  if (!privacy) throw new Error(t('app.sceneImportMissingField', { field: `${field}.privacy` }))
  return {
    name,
    value,
    trust,
    privacy
  }
}

const canonicalSceneRule = (rule: RuleForm, ruleIndex: number): PortableSceneRule => {
  const ruleField = `rules[${ruleIndex}]`
  if (!Array.isArray(rule.sources) || rule.sources.length === 0) {
    throw new Error(t('app.sceneImportMissingField', { field: `${ruleField}.sources` }))
  }
  const sources = rule.sources.map((source, sourceIndex) => {
    const sourceField = `${ruleField}.sources[${sourceIndex}]`
    const itemType = normalizeSceneRuleSourceType(source.itemType, `${sourceField}.itemType`)
    const fromId = normalizeSceneString(source.fromId, `${sourceField}.fromId`)
    const fromApi = normalizeSceneString(source.fromApi, `${sourceField}.fromApi`)
    if (!fromId) throw new Error(t('app.sceneImportMissingField', { field: `${sourceField}.fromId` }))
    if (!fromApi) throw new Error(t('app.sceneImportMissingField', { field: `${sourceField}.fromApi` }))
    const relation = normalizeSceneString(source.relation, `${sourceField}.relation`)
    const value = normalizeSceneString(source.value, `${sourceField}.value`)
    if (itemType === 'api' && (relation || value)) {
      throw new Error(t('app.sceneImportUnexpectedRuleSignalValue', { field: sourceField }))
    }
    if (itemType !== 'api' && !relation) {
      throw new Error(t('app.sceneImportMissingField', { field: `${sourceField}.relation` }))
    }
    if (itemType !== 'api' && !value) {
      throw new Error(t('app.sceneImportMissingField', { field: `${sourceField}.value` }))
    }
    const normalizedRelation = itemType === 'api' ? '' : normalizeModelRelation(relation)
    if (itemType !== 'api' && !normalizedRelation) {
      throw new Error(t('app.sceneImportInvalidEnum', { field: `${sourceField}.relation`, value: relation }))
    }
    return {
      fromId,
      fromApi,
      itemType,
      ...(itemType === 'api' ? {} : {
        relation: normalizedRelation,
        value
      })
    }
  })

  const name = normalizeSceneString(rule.name, `${ruleField}.name`)
  const toId = normalizeSceneString(rule.toId, `${ruleField}.toId`)
  const toApi = normalizeSceneString(rule.toApi, `${ruleField}.toApi`)
  if (!toId) throw new Error(t('app.sceneImportMissingField', { field: `${ruleField}.toId` }))
  if (!toApi) throw new Error(t('app.sceneImportMissingField', { field: `${ruleField}.toApi` }))
  const contentDevice = normalizeSceneString(rule.contentDevice, `${ruleField}.contentDevice`)
  const content = normalizeSceneString(rule.content, `${ruleField}.content`)
  if (Boolean(contentDevice) !== Boolean(content)) {
    throw new Error(t('app.sceneImportContentPairRequired', { index: ruleIndex + 1 }))
  }
  return {
    ...(name ? { name } : {}),
    sources,
    toId,
    toApi,
    ...(contentDevice ? { contentDevice } : {}),
    ...(content ? { content } : {})
  }
}

const canonicalSceneSpecCondition = (
  condition: SpecCondition,
  field: string
): PortableSceneCondition => {
  const deviceId = normalizeSceneString(condition.deviceId, `${field}.deviceId`)
  const targetType = normalizeSceneSpecTargetType(condition.targetType, `${field}.targetType`)
  const key = normalizeSceneString(condition.key, `${field}.key`)
  const propertyScope = normalizeSceneString(condition.propertyScope, `${field}.propertyScope`).toLowerCase()
  const relation = normalizeSceneString(condition.relation, `${field}.relation`)
  const value = normalizeSceneString(condition.value, `${field}.value`)
  if (!deviceId) throw new Error(t('app.sceneImportMissingField', { field: `${field}.deviceId` }))
  if (!key) throw new Error(t('app.sceneImportMissingField', { field: `${field}.key` }))
  if (!relation) throw new Error(t('app.sceneImportMissingField', { field: `${field}.relation` }))
  if (!value) throw new Error(t('app.sceneImportMissingField', { field: `${field}.value` }))
  const isPropertyCondition = targetType === 'trust' || targetType === 'privacy'
  if (isPropertyCondition && !['state', 'variable'].includes(propertyScope)) {
    throw new Error(t('app.sceneImportInvalidEnum', { field: `${field}.propertyScope`, value: propertyScope || t('app.empty') }))
  }
  if (!isPropertyCondition && propertyScope) {
    throw new Error(t('app.sceneImportUnexpectedField', { field: `${field}.propertyScope` }))
  }
  const normalizedRelation = normalizeModelRelation(relation)
  if (!normalizedRelation) {
    throw new Error(t('app.sceneImportInvalidEnum', { field: `${field}.relation`, value: relation }))
  }
  return {
    deviceId,
    targetType,
    key,
    ...(isPropertyCondition ? { propertyScope: propertyScope as 'state' | 'variable' } : {}),
    relation: normalizedRelation,
    value
  }
}

const canonicalSceneSpec = (spec: Specification, specIndex: number): PortableSceneSpecification => ({
  templateId: normalizeSceneString(spec.templateId, `specs[${specIndex}].templateId`) as Specification['templateId'],
  aConditions: (spec.aConditions || []).map((condition, index) =>
    canonicalSceneSpecCondition(condition, `specs[${specIndex}].aConditions[${index}]`)),
  ifConditions: (spec.ifConditions || []).map((condition, index) =>
    canonicalSceneSpecCondition(condition, `specs[${specIndex}].ifConditions[${index}]`)),
  thenConditions: (spec.thenConditions || []).map((condition, index) =>
    canonicalSceneSpecCondition(condition, `specs[${specIndex}].thenConditions[${index}]`))
})

const canonicalSceneTemplate = (template: DeviceTemplate, index: number): PortableSceneTemplate => {
  const name = normalizeSceneString(template.name || template.manifest?.Name, `templates[${index}].name`)
  if (!name) throw new Error(t('app.sceneImportMissingField', { field: `templates[${index}].name` }))
  return {
    name,
    manifest: canonicalPlainValue(template.manifest) as DeviceTemplate['manifest']
  }
}

const canonicalizeSceneFile = (scene: BoardSceneModel): PortableSceneFile => ({
  schema: SCENE_FILE_SCHEMA,
  version: SCENE_FILE_VERSION,
  templates: sortSceneItems((scene.templates || []).map(canonicalSceneTemplate), template => template.name),
  devices: sortSceneItems(
    scene.devices.map((device, index) => canonicalSceneDevice(device, index, scene.templates)),
    device => device.id
  ),
  environmentVariables: sortSceneItems(scene.environmentVariables.map(canonicalSceneEnvironmentVariable), variable => variable.name),
  rules: scene.rules.map(canonicalSceneRule),
  specs: scene.specs.map(canonicalSceneSpec)
})

const normalizeSceneFile = (raw: unknown): BoardSceneModel => {
  const payload = raw as any
  if (!payload || typeof payload !== 'object' || Array.isArray(payload)) {
    throw new Error(t('app.sceneImportInvalidFile'))
  }
  assertSceneAllowedFields(
    payload,
    ['schema', 'version', 'templates', 'devices', 'environmentVariables', 'rules', 'specs'],
    ''
  )
  if (payload.schema !== SCENE_FILE_SCHEMA) {
    throw new Error(t('app.sceneImportInvalidFile'))
  }
  if (payload.version !== SCENE_FILE_VERSION) {
    throw new Error(t('app.sceneImportUnsupportedVersion', {
      version: payload.version ?? t('app.empty'),
      supported: SCENE_FILE_VERSION
    }))
  }
  for (const field of ['templates', 'devices', 'environmentVariables', 'rules', 'specs']) {
    if (!Array.isArray(payload[field])) {
      throw new Error(t('app.sceneImportArrayRequired', { field }))
    }
  }
  const templates = normalizeSceneTemplates(payload.templates)
  const devices = payload.devices.map((device: unknown, index: number) => normalizeSceneDevice(device, index))
  assertUniqueSceneDeviceIds(devices)
  assertSceneDeviceRuntimeShape(payload.devices, devices, templates)
  const scene: BoardSceneModel = {
    schema: SCENE_FILE_SCHEMA,
    version: SCENE_FILE_VERSION,
    templates,
    devices,
    environmentVariables: normalizeSceneEnvironmentVariables(payload.environmentVariables),
    rules: normalizeSceneRules(payload.rules),
    specs: normalizeSceneSpecs(payload.specs)
  }
  assertSceneReferences(scene)
  assertSceneTemplateCoverage(scene)
  assertSceneEnvironmentCoverage(scene)
  const labelsByDeviceId = new Map(scene.devices.map(device => [device.id, device.label]))
  scene.specs = scene.specs.map(spec => ({
    ...spec,
    aConditions: spec.aConditions.map(condition => ({
      ...condition,
      deviceLabel: labelsByDeviceId.get(condition.deviceId) || condition.deviceId
    })),
    ifConditions: spec.ifConditions.map(condition => ({
      ...condition,
      deviceLabel: labelsByDeviceId.get(condition.deviceId) || condition.deviceId
    })),
    thenConditions: spec.thenConditions.map(condition => ({
      ...condition,
      deviceLabel: labelsByDeviceId.get(condition.deviceId) || condition.deviceId
    }))
  })).map(spec => ({
    ...spec,
    formula: buildSpecFormula(spec, {
      nodes: scene.devices,
      deviceTemplates: scene.templates
    }),
    devices: buildSpecDeviceRefsFromConditions([
      ...spec.aConditions,
      ...spec.ifConditions,
      ...spec.thenConditions
    ], scene.devices)
  }))
  return scene
}

const getReferencedSceneTemplates = (devices: DeviceNode[]) => {
  const names = new Set(devices.map(device => normalizeTemplateLookupName(device.templateName)).filter(Boolean))
  return deviceTemplates.value
    .filter(template => names.has(normalizeTemplateLookupName(template.name)) || names.has(normalizeTemplateLookupName(template.manifest?.Name)))
    .map(template => ({
      name: template.name || template.manifest.Name,
      manifest: deepClone(template.manifest)
    }))
}

const buildSceneExport = (): PortableSceneFile => {
  const devices = cloneVisibleDeviceNodes()
  const rulesForExport: RuleForm[] = deepClone(rules.value).map(rule => {
    const { id: _id, ...portableRule } = rule
    return portableRule
  })
  const sceneModel: BoardSceneModel = {
    schema: SCENE_FILE_SCHEMA,
    version: SCENE_FILE_VERSION,
    templates: getReferencedSceneTemplates(devices),
    devices,
    environmentVariables: deepClone(environmentVariables.value),
    rules: rulesForExport,
    specs: deepClone(specifications.value)
  }
  assertUniqueSceneDeviceIds(sceneModel.devices)
  assertSceneReferences(sceneModel)
  assertSceneTemplateCoverage(sceneModel)
  assertSceneEnvironmentCoverage(sceneModel)
  const portable = canonicalizeSceneFile(sceneModel)
  normalizeSceneFile(portable)
  return portable
}

const downloadJsonFile = (filename: string, payload: unknown) => {
  const blob = new Blob([JSON.stringify(payload, null, 2)], { type: 'application/json;charset=utf-8' })
  const url = URL.createObjectURL(blob)
  const anchor = document.createElement('a')
  anchor.href = url
  anchor.download = filename
  document.body.appendChild(anchor)
  anchor.click()
  anchor.remove()
  URL.revokeObjectURL(url)
}

const exportScene = () => {
  if (!ensureBoardDataReady()) return
  let scene: PortableSceneFile
  try {
    scene = buildSceneExport()
  } catch (error) {
    ElMessage.error(getSceneErrorMessage(error))
    return
  }
  const timestamp = new Date().toISOString().replace(/[:.]/g, '-')
  downloadJsonFile(`iot-verify-scene-${timestamp}.json`, scene)
  ElMessage.success(t('app.sceneExportStarted', {
    devices: scene.devices.length,
    variables: scene.environmentVariables.length,
    rules: scene.rules.length,
    specs: scene.specs.length
  }))
}

const triggerSceneImport = () => {
  if (isImportingScene.value) return
  if (sceneImportInputRef.value) {
    sceneImportInputRef.value.value = ''
    sceneImportInputRef.value.click()
  }
}

const getSceneErrorMessage = (error: any) => {
  const rawMessage = String(error?.response?.data?.message || error?.message || '')
  const message = localizedErrorMessage(error, t('app.sceneImportFailed'), locale.value)
  if (!error?.response) return message
  const field = rawMessage.match(/\b(?:templates|devices|nodes|environmentVariables|rules|specs)\[\d+](?:\.[A-Za-z0-9_]+)*/)?.[0]
  if (!field) return message
  return `${formatSceneValidationCoordinate(field)}: ${t('app.sceneImportValidationItemInvalid')}`
}

const getStructuredValidationErrors = (error: any): Array<[string, string]> => {
  const errors = error?.response?.data?.data?.errors
  if (!errors || typeof errors !== 'object' || Array.isArray(errors)) return []
  return Object.entries(errors)
    .filter(([field, reason]) => field && typeof reason === 'string' && reason.trim())
    .map(([field, reason]) => [field, String(reason)] as [string, string])
}

const formatSceneValidationCoordinate = (field: string): string => {
  const patterns: Array<[RegExp, string]> = [
    [/^templates\[(\d+)]/, 'sceneImportValidationTemplate'],
    [/^devices\[(\d+)]/, 'sceneImportValidationDevice'],
    [/^nodes\[(\d+)]/, 'sceneImportValidationDevice'],
    [/^environmentVariables\[(\d+)]/, 'sceneImportValidationEnvironment'],
    [/^rules\[(\d+)]/, 'sceneImportValidationRule'],
    [/^specs\[(\d+)]/, 'sceneImportValidationSpecification']
  ]
  for (const [pattern, key] of patterns) {
    const match = field.match(pattern)
    if (match) return t(`app.${key}`, { index: Number(match[1]) + 1 })
  }
  return t('app.sceneImportValidationScene')
}

const showSceneImportError = async (error: any) => {
  const entries = getStructuredValidationErrors(error)
  if (entries.length === 0) {
    ElMessage.error(getSceneErrorMessage(error))
    return
  }
  try {
    await ElMessageBox.alert(
      h('div', { class: 'space-y-3 text-left' }, [
        h('p', { class: 'text-sm text-slate-600' }, t('app.sceneImportValidationSummary', { count: entries.length })),
        ...entries.map(([field, reason]) => h('div', { class: 'border-l-2 border-rose-300 pl-3' }, [
          h('div', { class: 'text-sm font-semibold text-slate-800' }, formatSceneValidationCoordinate(field)),
          h('div', { class: 'mt-0.5 text-sm text-slate-600' }, t('app.sceneImportValidationItemInvalid')),
          h('details', { class: 'mt-1 text-xs text-slate-500' }, [
            h('summary', { class: 'cursor-pointer font-semibold' }, t('app.technicalDetails')),
            h('code', { class: 'mt-1 block break-all text-xs text-slate-400' }, field),
            h('div', { class: 'mt-1 whitespace-pre-wrap break-words' }, reason)
          ])
        ]))
      ]),
      t('app.sceneImportValidationTitle'),
      { type: 'error' }
    )
  } catch {
    // Closing the diagnostic dialog needs no follow-up action.
  }
}

const refreshSceneForReconciliation = async (): Promise<boolean> => {
  const [templatesOk, nodesOk, rulesOk, specsOk] = await Promise.all([
    refreshDeviceTemplates(),
    refreshDevices(),
    refreshRules(),
    refreshSpecifications()
  ])
  const environmentOk = await refreshEnvironmentVariables()
  return templatesOk && nodesOk && rulesOk && specsOk && environmentOk
}

const readBoardReplacementStalePreview = (error: any): BoardReplacementPreview | null => {
  const data = error?.response?.data?.data as Partial<BoardReplacementStaleData> | undefined
  const preview = data?.currentPreview as Partial<BoardReplacementPreview> | undefined
  if (data?.reasonCode !== 'BOARD_REPLACEMENT_STALE' || !preview) return null
  if (typeof preview.impactToken !== 'string' || !preview.impactToken.trim()) return null
  const counts = [
    preview.deviceCount,
    preview.environmentVariableCount,
    preview.ruleCount,
    preview.specificationCount
  ]
  if (!counts.every(value => Number.isSafeInteger(value) && Number(value) >= 0)) return null
  return preview as BoardReplacementPreview
}

const reportBoardReplacementDrift = async (error: any): Promise<boolean> => {
  const preview = readBoardReplacementStalePreview(error)
  if (!preview) return false
  const refreshed = await refreshSceneForReconciliation()
  ElMessage.warning(t(
    refreshed ? 'app.sceneReplacementChangedBeforeApply' : 'app.sceneReplacementChangedRefreshFailed',
    {
      devices: preview.deviceCount,
      variables: preview.environmentVariableCount,
      rules: preview.ruleCount,
      specs: preview.specificationCount
    }
  ))
  return true
}

const currentBoardMatchesScene = (scene: BoardSceneModel): boolean => {
  try {
    return JSON.stringify(buildSceneExport()) === JSON.stringify(canonicalizeSceneFile(scene))
  } catch {
    return false
  }
}

const savedBatchMatchesScene = (
  saved: Awaited<ReturnType<typeof boardApi.saveBoardBatch>>,
  scene: BoardSceneModel
): boolean => {
  try {
    const returnedScene: BoardSceneModel = {
      schema: SCENE_FILE_SCHEMA,
      version: SCENE_FILE_VERSION,
      templates: scene.templates,
      devices: getVisibleDeviceNodes(saved.nodes),
      environmentVariables: saved.environmentVariables,
      rules: saved.rules,
      specs: saved.specs
    }
    return JSON.stringify(canonicalizeSceneFile(returnedScene))
      === JSON.stringify(canonicalizeSceneFile(scene))
  } catch {
    return false
  }
}

const resetSceneSelectionAfterReplacement = async () => {
  dialogVisible.value = false
  focusedNodeId.value = null
  focusedRuleId.value = null
  focusedSpecId.value = null
  await nextTick()
  if (getVisibleDeviceNodes().length > 0) {
    fitNodesToCanvas(getVisibleDeviceNodes())
  }
}

const importScene = async (scene: BoardSceneModel): Promise<boolean> => {
  if (!ensurePlaybackClosedForMutation()) return false
  if (isSceneReplacementInProgress.value) return false
  if (chatStore.state.streaming) {
    ElMessage.warning(t('app.finishAssistantBeforeSceneReplacement'))
    return false
  }
  isImportingScene.value = true
  try {
    await waitForPendingBoardMutations()
    if (!ensureBoardDataReady()) return false
    let replacementPreview: BoardReplacementPreview
    try {
      replacementPreview = await boardApi.previewBoardReplacement()
    } catch (error: any) {
      ElMessage.error(localizedErrorMessage(error, t('app.sceneReplacementPreviewFailed'), locale.value))
      return false
    }
    try {
      await ElMessageBox.confirm(
        t('app.sceneImportConfirmMessage', {
          currentDevices: replacementPreview.deviceCount,
          currentVariables: replacementPreview.environmentVariableCount,
          currentRules: replacementPreview.ruleCount,
          currentSpecs: replacementPreview.specificationCount,
          devices: scene.devices.length,
          variables: scene.environmentVariables.length,
          rules: scene.rules.length,
          specs: scene.specs.length
        }),
        t('app.sceneImportConfirmTitle'),
        {
          type: 'warning',
          customClass: 'scene-replacement-confirm',
          confirmButtonText: t('app.sceneImportConfirmAction'),
          cancelButtonText: t('app.cancel')
        }
      )
    } catch {
      return false
    }

    return await enqueueBoardMutation(async () => {
      let saved: Awaited<ReturnType<typeof boardApi.saveBoardBatch>>
      try {
        saved = await boardApi.saveBoardBatch({
          impactToken: replacementPreview.impactToken,
          nodes: scene.devices,
          environmentVariables: scene.environmentVariables,
          rules: scene.rules,
          specs: scene.specs,
          templateSnapshots: scene.templates
        })
        if (!savedBatchMatchesScene(saved, scene)) {
          throw new Error('Scene replacement response did not match the requested semantic scene')
        }
      } catch (error: any) {
        console.error('场景导入失败', error)
        if (await reportBoardReplacementDrift(error)) return false
        const status = Number(error?.response?.status || 0)
        if (status >= 400 && status < 500) {
          await showSceneImportError(error)
          return false
        }

        const refreshed = await refreshSceneForReconciliation()
        if (!refreshed) {
          ElMessage.warning(t('app.sceneImportOutcomeUnknownRefreshFailed'))
          return false
        }
        if (currentBoardMatchesScene(scene)) {
          await resetSceneSelectionAfterReplacement()
          ElMessage.warning(t('app.sceneImportCurrentMatchesAfterUnconfirmedResponse'))
          return true
        }
        ElMessage.warning(t('app.sceneImportOutcomeUnconfirmedAfterRefresh'))
        return false
      }

      nodes.value = getVisibleDeviceNodes(saved.nodes)
      environmentVariables.value = saved.environmentVariables
      rules.value = saved.rules
      specifications.value = saved.specs
      if (saved.createdTemplates.length > 0) {
        const existingTemplateNames = new Set(deviceTemplates.value.map(template =>
          normalizeTemplateLookupName(template.name || template.manifest?.Name)))
        deviceTemplates.value = [
          ...deviceTemplates.value,
          ...saved.createdTemplates.filter(template => {
            const key = normalizeTemplateLookupName(template.name || template.manifest?.Name)
            if (!key || existingTemplateNames.has(key)) return false
            existingTemplateNames.add(key)
            return true
          })
        ]
      }
      syncRuleDerivedEdges()
      await resetSceneSelectionAfterReplacement()
      const importMessage = saved.createdTemplates.length > 0
        ? t('app.sceneImportSuccessWithTemplates', {
            devices: nodes.value.length,
            variables: environmentVariables.value.length,
            rules: rules.value.length,
            specs: specifications.value.length,
            templates: saved.createdTemplates.length
          })
        : t('app.sceneImportSuccess', {
            devices: nodes.value.length,
            variables: environmentVariables.value.length,
            rules: rules.value.length,
            specs: specifications.value.length
          })
      ElMessage.success(importMessage)
      return true
    })
  } finally {
    isImportingScene.value = false
  }
}

const clearScene = async () => {
  if (!ensurePlaybackClosedForMutation()) return
  if (isClearingScene.value || isImportingScene.value) return
  if (chatStore.state.streaming) {
    ElMessage.warning(t('app.finishAssistantBeforeSceneReplacement'))
    return
  }
  isClearingScene.value = true
  try {
    await waitForPendingBoardMutations()
    if (!ensureBoardDataReady()) return
    let replacementPreview: BoardReplacementPreview
    try {
      replacementPreview = await boardApi.previewBoardReplacement()
    } catch (error: any) {
      ElMessage.error(localizedErrorMessage(error, t('app.sceneReplacementPreviewFailed'), locale.value))
      return
    }
    try {
      await ElMessageBox.confirm(
        t('app.sceneClearConfirmMessage', {
          devices: replacementPreview.deviceCount,
          variables: replacementPreview.environmentVariableCount,
          rules: replacementPreview.ruleCount,
          specs: replacementPreview.specificationCount
        }),
        t('app.sceneClearConfirmTitle'),
        {
          type: 'warning',
          customClass: 'scene-replacement-confirm',
          confirmButtonText: t('app.sceneClearConfirmAction'),
          cancelButtonText: t('app.cancel')
        }
      )
    } catch {
      return
    }

    await enqueueBoardMutation(async () => {
      try {
        const saved = await boardApi.saveBoardBatch({
          impactToken: replacementPreview.impactToken,
          nodes: [],
          environmentVariables: [],
          rules: [],
          specs: [],
          templateSnapshots: []
        })
        if (saved.nodes.length > 0 || saved.environmentVariables.length > 0
          || saved.rules.length > 0 || saved.specs.length > 0) {
          throw new Error('Scene clear response still contained board items')
        }
        nodes.value = getVisibleDeviceNodes(saved.nodes)
        environmentVariables.value = saved.environmentVariables
        rules.value = saved.rules
        specifications.value = saved.specs
        syncRuleDerivedEdges()
        dialogVisible.value = false
        focusedNodeId.value = null
        focusedRuleId.value = null
        focusedSpecId.value = null
        ElMessage.success(t('app.sceneClearSuccess'))
      } catch (error: any) {
        console.error('清空场景失败', error)
        if (await reportBoardReplacementDrift(error)) return
        const status = Number(error?.response?.status || 0)
        if (status >= 400 && status < 500) {
          const message = localizedErrorMessage(error, t('app.sceneClearFailed'), locale.value)
          ElMessage.error(message)
          return
        }
        const refreshed = await refreshSceneForReconciliation()
        if (!refreshed) {
          ElMessage.warning(t('app.sceneClearOutcomeUnknownRefreshFailed'))
          return
        }
        const isEmpty = getVisibleDeviceNodes().length === 0
          && environmentVariables.value.length === 0
          && rules.value.length === 0
          && specifications.value.length === 0
        if (isEmpty) {
          await resetSceneSelectionAfterReplacement()
          ElMessage.warning(t('app.sceneClearCurrentEmptyAfterUnconfirmedResponse'))
        } else {
          ElMessage.warning(t('app.sceneClearOutcomeUnconfirmedAfterRefresh'))
        }
      }
    })
  } finally {
    isClearingScene.value = false
  }
}

const handleSceneImportFile = async (event: Event) => {
  const input = event.target as HTMLInputElement | null
  const file = input?.files?.[0]
  if (!file) return
  try {
    const text = await file.text()
    let raw: unknown
    try {
      raw = JSON.parse(text)
    } catch (error) {
      console.error('场景 JSON 解析失败', error)
      ElMessage.error(t('app.invalidJsonFile'))
      return
    }
    let scene: BoardSceneModel
    try {
      scene = normalizeSceneFile(raw)
    } catch (error) {
      console.error('场景文件校验失败', error)
      ElMessage.error(error instanceof Error && error.message.trim()
        ? error.message
        : t('app.sceneImportFailed'))
      return
    }
    await importScene(scene)
  } catch (error) {
    console.error('读取场景文件失败', error)
    ElMessage.error(getSceneErrorMessage(error))
  } finally {
    if (input) input.value = ''
  }
}

// 2.定义刷新规则的函数（edges 由 rules 动态生成）
const refreshRules = async (): Promise<boolean> => {
  boardDataLoadState.rules = 'loading'
  try {
    // 只获取规则列表
    const rulesData = await boardApi.getRules()
    rules.value = rulesData
    // 动态生成 edges
    syncRuleDerivedEdges()
    boardDataLoadState.rules = 'ready'
    return true
  } catch (e) {
    console.error('加载规则失败', e)
    boardDataLoadState.rules = 'error'
    return false
  }
}

// 3.定义刷新规约的函数
const refreshSpecifications = async (): Promise<boolean> => {
  boardDataLoadState.specs = 'loading'
  try {
    specifications.value = await boardApi.getSpecs()
    boardDataLoadState.specs = 'ready'
    return true
  } catch(e) {
    console.error('加载规约失败', e)
    boardDataLoadState.specs = 'error'
    return false
  }
}

const retryBoardDataLoad = async () => {
  await refreshBoardSnapshot()
  if (isBoardDataReady.value) {
    ElMessage.success(t('app.boardDataReloaded'))
  } else {
    ElMessage.error(t('app.boardDataLoadFailed'))
  }
}

watch([nodes, rules], syncRuleDerivedEdges, { deep: true })

onMounted(async () => {
  updateActionDockViewport()
  window.addEventListener('resize', updateActionDockViewport)

  hydrateFuzzNotificationState()
  const [boardLoaded, , layout, currentModelFingerprint] = await Promise.all([
    refreshBoardSnapshot(),
    loadTaskInbox(false, { showLoading: false }),
    boardApi.getLayout().catch(() => null),
    fuzzingApi.getCurrentModelFingerprint().catch(() => null)
  ])
  if (boardLifecycleDisposed) return
  if (!boardLoaded || !isBoardDataReady.value) {
    ElMessage.error(t('app.boardDataLoadFailed'))
  }
  currentFuzzingModelFingerprint.value = currentModelFingerprint
  taskInboxRefreshTimer = setInterval(() => {
    if (activeBackgroundTaskCount.value > 0
      || trackedFuzzTaskIds.value.length > 0
      || showHistoryPanel.value) {
      void refreshTaskInboxInBackground()
    }
  }, TASK_INBOX_REFRESH_INTERVAL_MS)

  // 监听 AI 推荐的设备添加事件

  persistedWideLayout = layout ?? {
    canvasPan: { x: 0, y: 0 },
    canvasZoom: 1,
    panels: {
      control: {
        collapsed: false,
        width: DEFAULT_CONTROL_PANEL_WIDTH,
        activeSection: 'templates'
      },
      inspector: {
        collapsed: false,
        width: DEFAULT_INSPECTOR_PANEL_WIDTH,
        activeSection: 'devices'
      }
    }
  }
  if (isNarrowViewport()) {
    applyViewportPanelConstraints()
    void nextTick(() => fitNodesToCanvas(getVisibleDeviceNodes()))
  } else if (layout) {
    applyBoardLayout(layout)
  }
  layoutHydrated.value = true

  if (boardLifecycleDisposed) return
  window.addEventListener('keydown', onGlobalKeydown)
})


// Color utilities (matching CanvasBoard colors)
const getCanvasMapColorIndex = (nodeId: string): number => {
  // 为每个节点生成随机但一致的颜色索引
  // 使用节点ID作为种子，确保同一个节点始终有相同颜色
  let hash = 5381
  for (let i = 0; i < nodeId.length; i++) {
    const char = nodeId.charCodeAt(i)
    hash = ((hash << 5) + hash) + char // hash * 33 + char
  }

  // 使用8种颜色，与CanvasBoard.vue保持一致
  return Math.abs(hash) % 8
}

const getCanvasMapColor = (nodeId: string): string => {
  // Return actual color values instead of Tailwind classes
  const colorIndex = getCanvasMapColorIndex(nodeId)
  const colorValues = [
    '#2563eb', '#0891b2', '#0f766e', '#7c3aed',
    '#475569', '#0284c7', '#4f46e5', '#0d9488'
  ] // non-alert map colors; red is reserved for actual warnings elsewhere
  return colorValues[colorIndex] || colorValues[0]
}

const getCanvasMapSize = (): string => {
  // All nodes use the same size for consistency
  return 'size-2'
}

const CANVAS_MAP_WIDTH = 220
const CANVAS_MAP_HEIGHT = 112
const CANVAS_MAP_INSET = 8
const isCanvasMapDragging = ref(false)
let canvasMapDragRect: DOMRect | null = null
let canvasMapDragElement: HTMLElement | null = null
let canvasMapDragPointerId: number | null = null

// Canvas map calculations
const canvasMapData = computed(() => {
  const visibleNodes = getVisibleDeviceNodes()

  if (visibleNodes.length === 0) {
    return {
      dots: [],
      lines: [],
      bounds: null as null | { minX: number; minY: number; maxX: number; maxY: number; width: number; height: number }
    }
  }

  // Calculate canvas bounds
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity

  visibleNodes.forEach(node => {
    const x = node.position.x
    const y = node.position.y
    const width = node.width || DEFAULT_NODE_WIDTH
    const height = node.height || DEFAULT_NODE_HEIGHT

    minX = Math.min(minX, x)
    minY = Math.min(minY, y)
    maxX = Math.max(maxX, x + width)
    maxY = Math.max(maxY, y + height)
  })

  const frame = getVisibleCanvasFrame()
  let visibleWorldWidth = 900
  let visibleWorldHeight = 600
  if (frame && canvasZoom.value > 0) {
    const visibleMinX = (frame.left - canvasPan.value.x) / canvasZoom.value
    const visibleMinY = (frame.top - canvasPan.value.y) / canvasZoom.value
    const visibleMaxX = (frame.left + frame.width - canvasPan.value.x) / canvasZoom.value
    const visibleMaxY = (frame.top + frame.height - canvasPan.value.y) / canvasZoom.value
    visibleWorldWidth = Math.max(1, visibleMaxX - visibleMinX)
    visibleWorldHeight = Math.max(1, visibleMaxY - visibleMinY)
    minX = Math.min(minX, visibleMinX)
    minY = Math.min(minY, visibleMinY)
    maxX = Math.max(maxX, visibleMaxX)
    maxY = Math.max(maxY, visibleMaxY)
  }

  const contentWidth = Math.max(1, maxX - minX)
  const contentHeight = Math.max(1, maxY - minY)
  const paddingX = Math.max(260, visibleWorldWidth * 0.75, contentWidth * 0.16)
  const paddingY = Math.max(180, visibleWorldHeight * 0.75, contentHeight * 0.16)
  minX -= paddingX
  minY -= paddingY
  maxX += paddingX
  maxY += paddingY

  const canvasWidth = maxX - minX
  const canvasHeight = maxY - minY

  // Convert node positions to mini map coordinates
  const dots = visibleNodes.map((node) => {
    const nodeX = canvasWidth > 0
      ? CANVAS_MAP_INSET + ((node.position.x - minX) / canvasWidth) * (CANVAS_MAP_WIDTH - CANVAS_MAP_INSET * 2)
      : CANVAS_MAP_WIDTH / 2
    const nodeY = canvasHeight > 0
      ? CANVAS_MAP_INSET + ((node.position.y - minY) / canvasHeight) * (CANVAS_MAP_HEIGHT - CANVAS_MAP_INSET * 2)
      : CANVAS_MAP_HEIGHT / 2

    return {
      id: node.id,
      x: Math.max(CANVAS_MAP_INSET / 2, Math.min(CANVAS_MAP_WIDTH - CANVAS_MAP_INSET - 4, nodeX)),
      y: Math.max(CANVAS_MAP_INSET / 2, Math.min(CANVAS_MAP_HEIGHT - CANVAS_MAP_INSET - 4, nodeY)),
      size: getCanvasMapSize(),
      color: getCanvasMapColor(node.id)
    }
  })

  // Create node lookup map for easy access
  const nodeMap = new Map(dots.map(dot => [dot.id, dot]))

  // Generate lines for rule-derived visible edges.
  const lines = allEdges.value.flatMap((edge) => {
    const fromDot = nodeMap.get(edge.from)
    const toDot = nodeMap.get(edge.to)

    if (!fromDot || !toDot) return []

    // Check if bidirectional
    const isBidirectional = edges.value.some(e =>
      (e.from === edge.to && e.to === edge.from)
    )

    let offsetY = 0

    if (isBidirectional) {
      // For bidirectional edges, offset vertically
      const [node1, node2] = [edge.from, edge.to].sort()
      const isFirstDirection = (edge.from === node1 && edge.to === node2)
      offsetY = isFirstDirection ? -8 : 8 // Offset above/below
    }

    return [{
      id: edge.id,
      fromId: edge.from,
      x1: fromDot.x + 4, // Center of dot (assuming 8px diameter)
      y1: fromDot.y + 4 + offsetY,
      x2: toDot.x + 4,
      y2: toDot.y + 4 + offsetY,
      color: getCanvasMapColor(edge.from),
      isBidirectional
    }]
  })

  return {
    dots,
    lines,
    bounds: { minX, minY, maxX, maxY, width: canvasWidth, height: canvasHeight }
  }
})

const canvasMapDots = computed(() => canvasMapData.value.dots)
const canvasMapLines = computed(() => canvasMapData.value.lines)
const canvasMapViewBox = computed(() => `0 0 ${CANVAS_MAP_WIDTH} ${CANVAS_MAP_HEIGHT}`)

const getNodeBounds = (targetNodes: DeviceNode[] = nodes.value) => {
  if (targetNodes.length === 0) return null
  return targetNodes.reduce((bounds, node) => {
    const x = node.position.x
    const y = node.position.y
    const width = node.width || DEFAULT_NODE_WIDTH
    const height = node.height || DEFAULT_NODE_HEIGHT
    return {
      minX: Math.min(bounds.minX, x),
      minY: Math.min(bounds.minY, y),
      maxX: Math.max(bounds.maxX, x + width),
      maxY: Math.max(bounds.maxY, y + height)
    }
  }, {
    minX: Infinity,
    minY: Infinity,
    maxX: -Infinity,
    maxY: -Infinity
  })
}

const getCanvasInnerOffset = () => {
  const canvas = document.querySelector('.canvas') as HTMLElement | null
  if (!canvas) return { x: 0, y: 64 }
  const style = getComputedStyle(canvas)
  return {
    x: Number.parseFloat(style.paddingLeft || '0') || 0,
    y: Number.parseFloat(style.paddingTop || '0') || 0
  }
}

const getVisibleCanvasFrame = () => {
  const canvasEl = document.querySelector('.canvas-container')
  if (!canvasEl) return null
  const rect = canvasEl.getBoundingClientRect()
  const leftInset = boardPanels.control.collapsed ? 64 : boardPanels.control.width
  const actionRailInset = actionDockReservedWidth.value + (isActionDockPackedMode.value ? 8 : 16)
  const rightInset = (boardPanels.inspector.collapsed ? 48 : boardPanels.inspector.width) + actionRailInset
  const canvasOffset = getCanvasInnerOffset()
  const topInset = canvasOffset.y
  const timelineVisible = simulationAnimationState.value.visible || traceAnimationState.value.visible
  const bottomInset = timelineVisible
    ? Math.min(260, Math.max(160, window.innerHeight * 0.28))
    : 24
  const availableWidth = Math.max(240, rect.width - leftInset - rightInset)
  const availableHeight = Math.max(180, rect.height - topInset - bottomInset)
  return {
    left: leftInset - canvasOffset.x,
    top: 0,
    width: availableWidth,
    height: availableHeight
  }
}

const getVisibleCanvasCenterWorld = () => {
  const frame = getVisibleCanvasFrame()
  if (!frame || canvasZoom.value <= 0) return null
  return {
    x: (frame.left + frame.width / 2 - canvasPan.value.x) / canvasZoom.value,
    y: (frame.top + frame.height / 2 - canvasPan.value.y) / canvasZoom.value
  }
}

const clampCanvasMapValue = (value: number, min: number, max: number) =>
  Math.min(max, Math.max(min, value))

const worldToCanvasMapPoint = (worldX: number, worldY: number) => {
  const bounds = canvasMapData.value.bounds
  if (!bounds) return null
  const innerWidth = CANVAS_MAP_WIDTH - CANVAS_MAP_INSET * 2
  const innerHeight = CANVAS_MAP_HEIGHT - CANVAS_MAP_INSET * 2
  return {
    x: CANVAS_MAP_INSET + ((worldX - bounds.minX) / Math.max(1, bounds.width)) * innerWidth,
    y: CANVAS_MAP_INSET + ((worldY - bounds.minY) / Math.max(1, bounds.height)) * innerHeight
  }
}

const canvasMapPointToWorld = (mapX: number, mapY: number) => {
  const bounds = canvasMapData.value.bounds
  if (!bounds) return null
  const innerWidth = CANVAS_MAP_WIDTH - CANVAS_MAP_INSET * 2
  const innerHeight = CANVAS_MAP_HEIGHT - CANVAS_MAP_INSET * 2
  const normalizedX = (clampCanvasMapValue(mapX, CANVAS_MAP_INSET, CANVAS_MAP_WIDTH - CANVAS_MAP_INSET) - CANVAS_MAP_INSET) / innerWidth
  const normalizedY = (clampCanvasMapValue(mapY, CANVAS_MAP_INSET, CANVAS_MAP_HEIGHT - CANVAS_MAP_INSET) - CANVAS_MAP_INSET) / innerHeight
  return {
    x: bounds.minX + normalizedX * bounds.width,
    y: bounds.minY + normalizedY * bounds.height
  }
}

const canvasMapPointFromEvent = (event: PointerEvent, rect?: DOMRect | null) => {
  const currentTarget = event.currentTarget
  const rectToUse = rect ?? (currentTarget instanceof HTMLElement ? currentTarget.getBoundingClientRect() : null)
  if (!rectToUse || rectToUse.width <= 0 || rectToUse.height <= 0) return null
  return {
    x: ((event.clientX - rectToUse.left) / rectToUse.width) * CANVAS_MAP_WIDTH,
    y: ((event.clientY - rectToUse.top) / rectToUse.height) * CANVAS_MAP_HEIGHT
  }
}

const panCanvasToWorldCenter = (worldX: number, worldY: number) => {
  const frame = getVisibleCanvasFrame()
  if (!frame) return
  canvasPan.value = {
    x: frame.left + frame.width / 2 - worldX * canvasZoom.value,
    y: frame.top + frame.height / 2 - worldY * canvasZoom.value
  }
}

const focusDeviceNodeOnCanvas = (
  node: DeviceNode,
  options: { ensureReadable?: boolean } = {}
) => {
  const width = node.width || DEFAULT_NODE_WIDTH
  const height = node.height || DEFAULT_NODE_HEIGHT

  if (options.ensureReadable) {
    const isCompactOnScreen = width * canvasZoom.value < 92 || height * canvasZoom.value < 74
    if (isCompactOnScreen) {
      canvasZoom.value = Math.min(MAX_ZOOM, Math.max(canvasZoom.value, 1))
    }
  }

  panCanvasToWorldCenter(
    node.position.x + width / 2,
    node.position.y + height / 2
  )
  focusedNodeId.value = node.id
  focusedRuleId.value = null
  focusedSpecId.value = null
  void nextTick(() => {
    const escaped = typeof CSS !== 'undefined' && typeof CSS.escape === 'function'
      ? CSS.escape(node.id)
      : node.id.replace(/["\\]/g, '\\$&')
    document.querySelector<HTMLElement>(`[data-node-id="${escaped}"]`)?.focus({ preventScroll: true })
  })
}

const focusCreatedDeviceNode = async (node?: DeviceNode | null) => {
  if (!node) return
  boardPanels.inspector.activeSection = 'devices'
  await nextTick()
  focusDeviceNodeOnCanvas(node, { ensureReadable: true })
}

const focusRuleOnCanvas = async (ruleId?: string | null) => {
  if (!ruleId) return
  focusedRuleId.value = ruleId
  focusedNodeId.value = null
  focusedSpecId.value = null
  boardPanels.inspector.activeSection = 'rules'

  const relatedEdges = edges.value.filter(edge => edge.ruleId === ruleId)
  const relatedNodeIds = new Set<string>()
  for (const edge of relatedEdges) {
    relatedNodeIds.add(edge.from)
    relatedNodeIds.add(edge.to)
  }
  const relatedNodes = getVisibleDeviceNodes().filter(node => relatedNodeIds.has(node.id))
  if (relatedNodes.length > 0) {
    fitNodesToCanvas(relatedNodes)
  }

  await nextTick()
  const escaped = typeof CSS !== 'undefined' && typeof CSS.escape === 'function'
    ? CSS.escape(ruleId)
    : ruleId.replace(/["\\]/g, '\\$&')
  document.querySelector<HTMLElement>(`[data-rule-id="${escaped}"]`)?.focus({ preventScroll: true })
}

const focusSpecInInspector = async (specId?: string | null) => {
  if (!specId) return
  focusedSpecId.value = specId
  focusedNodeId.value = null
  focusedRuleId.value = null
  boardPanels.inspector.activeSection = 'specs'
  await nextTick()
  const escaped = typeof CSS !== 'undefined' && typeof CSS.escape === 'function'
    ? CSS.escape(specId)
    : specId.replace(/["\\]/g, '\\$&')
  document.querySelector<HTMLElement>(`[data-spec-id="${escaped}"]`)?.focus({ preventScroll: true })
}

const canvasMapViewportRect = computed(() => {
  const bounds = canvasMapData.value.bounds
  const frame = getVisibleCanvasFrame()
  if (!bounds || !frame || canvasZoom.value <= 0) return null

  const visibleMinX = (frame.left - canvasPan.value.x) / canvasZoom.value
  const visibleMinY = (frame.top - canvasPan.value.y) / canvasZoom.value
  const visibleMaxX = (frame.left + frame.width - canvasPan.value.x) / canvasZoom.value
  const visibleMaxY = (frame.top + frame.height - canvasPan.value.y) / canvasZoom.value
  const topLeft = worldToCanvasMapPoint(visibleMinX, visibleMinY)
  const bottomRight = worldToCanvasMapPoint(visibleMaxX, visibleMaxY)
  if (!topLeft || !bottomRight) return null

  const minX = clampCanvasMapValue(Math.min(topLeft.x, bottomRight.x), CANVAS_MAP_INSET, CANVAS_MAP_WIDTH - CANVAS_MAP_INSET)
  const minY = clampCanvasMapValue(Math.min(topLeft.y, bottomRight.y), CANVAS_MAP_INSET, CANVAS_MAP_HEIGHT - CANVAS_MAP_INSET)
  const maxX = clampCanvasMapValue(Math.max(topLeft.x, bottomRight.x), CANVAS_MAP_INSET, CANVAS_MAP_WIDTH - CANVAS_MAP_INSET)
  const maxY = clampCanvasMapValue(Math.max(topLeft.y, bottomRight.y), CANVAS_MAP_INSET, CANVAS_MAP_HEIGHT - CANVAS_MAP_INSET)

  return {
    x: minX,
    y: minY,
    width: Math.max(4, maxX - minX),
    height: Math.max(4, maxY - minY)
  }
})

const navigateCanvasMap = (event: PointerEvent, rect?: DOMRect | null) => {
  const point = canvasMapPointFromEvent(event, rect)
  if (!point) return
  const world = canvasMapPointToWorld(point.x, point.y)
  if (!world) return
  panCanvasToWorldCenter(world.x, world.y)
}

const onCanvasMapPointerDown = (event: PointerEvent) => {
  if (!canvasMapData.value.bounds) return
  event.preventDefault()
  isCanvasMapDragging.value = true

  const target = event.currentTarget as HTMLElement
  canvasMapDragElement = target
  canvasMapDragRect = target.getBoundingClientRect()
  canvasMapDragPointerId = event.pointerId
  navigateCanvasMap(event, canvasMapDragRect)
  try { target.setPointerCapture(event.pointerId) } catch {}
  window.addEventListener('pointermove', onCanvasMapPointerMove)
  window.addEventListener('pointerup', onCanvasMapPointerUp)
}

const onCanvasMapPointerMove = (event: PointerEvent) => {
  if (!isCanvasMapDragging.value) return
  navigateCanvasMap(event, canvasMapDragRect)
}

const onCanvasMapPointerUp = () => {
  isCanvasMapDragging.value = false
  if (canvasMapDragElement && canvasMapDragPointerId !== null) {
    try { canvasMapDragElement.releasePointerCapture(canvasMapDragPointerId) } catch {}
  }
  canvasMapDragElement = null
  canvasMapDragRect = null
  canvasMapDragPointerId = null
  window.removeEventListener('pointermove', onCanvasMapPointerMove)
  window.removeEventListener('pointerup', onCanvasMapPointerUp)
}

const fitNodesToCanvas = (targetNodes: DeviceNode[] = nodes.value) => {
  const bounds = getNodeBounds(targetNodes)
  const frame = getVisibleCanvasFrame()
  if (!bounds || !frame) {
    ElMessage.info({ message: t('app.noDevicesOnCanvas'), type: 'info' })
    return
  }

  const padding = 72
  const contentWidth = Math.max(1, bounds.maxX - bounds.minX)
  const contentHeight = Math.max(1, bounds.maxY - bounds.minY)
  const zoom = Math.min(
    MAX_ZOOM,
    Math.max(
      MIN_ZOOM,
      Math.min(
        (frame.width - padding * 2) / contentWidth,
        (frame.height - padding * 2) / contentHeight
      )
    )
  )
  const centerX = (bounds.minX + bounds.maxX) / 2
  const centerY = (bounds.minY + bounds.maxY) / 2
  canvasZoom.value = Number.isFinite(zoom) ? zoom : 1
  canvasPan.value = {
    x: frame.left + frame.width / 2 - centerX * canvasZoom.value,
    y: frame.top + frame.height / 2 - centerY * canvasZoom.value
  }
}

const fitToContent = () => {
  fitNodesToCanvas(getVisibleDeviceNodes())
}

const handleCreateDevice = async (data: {
  template: DeviceTemplate
  customName: string
  runtime?: DeviceRuntimeConfig
  complete: (saved: boolean) => void
}) => {
  if (!ensurePlaybackClosedForMutation()) {
    data.complete(false)
    return
  }
  if (!ensureBoardDataReady(['nodes', 'templates'])) {
    data.complete(false)
    return
  }
  return enqueueBoardMutation(async () => {
    let saved = false
    let requestedNode: DeviceNode | null = null
    try {
      const { template, customName, runtime } = data
      const requestedLabel = customName.trim()
      const uniqueLabel = getUniqueLabel(requestedLabel, getVisibleDeviceNodes())
      if (uniqueLabel !== requestedLabel) {
        ElMessage.warning(t('app.deviceNameAlreadyExists'))
        return
      }
      const node: DeviceNode = {
        id: createDeviceInstanceId(getVisibleDeviceNodes()),
        templateName: template.manifest.Name,
        label: uniqueLabel,
        position: getNextNodePosition(),
        state: template.manifest.InitState || 'Working',
        width: DEFAULT_NODE_WIDTH,
        height: DEFAULT_NODE_HEIGHT,
        ...(runtime || {})
      }
      requestedNode = node
      const mutation = await boardApi.addNodes([node])
      nodes.value = getVisibleDeviceNodes(mutation.currentNodes)
      environmentVariables.value = mutation.environmentVariables
      reportEnvironmentChanges(mutation.environmentChanges)
      const created = mutation.affectedDevices[0]
      await focusCreatedDeviceNode(created)
      ElMessage.success(t('app.deviceAddedWithName', { name: created.label }))
      saved = true
    } catch (error: any) {
      if (!isDefinitiveMutationRejection(error) && requestedNode) {
        const [nodesRefreshed, environmentRefreshed] = await Promise.all([
          refreshDevices(),
          refreshEnvironmentVariables()
        ])
        const created = nodes.value.find(candidate => candidate.id === requestedNode?.id)
        if (nodesRefreshed && environmentRefreshed && created) {
          await focusCreatedDeviceNode(created)
          ElMessage.warning(t('app.deviceCreateOutcomeRefreshed', { name: created.label }))
          saved = true
          return
        }
      }
      ElMessage.error(localizedErrorMessage(error, t('app.saveNodesFailed'), locale.value))
    } finally {
      data.complete(saved)
    }
  })
}

const handleCreateDevices = async (data: {
  items: Array<{ template: DeviceTemplate, customName: string, runtime?: DeviceRuntimeConfig }>
  environmentVariables?: ModelEnvironmentVariable[]
  complete: (saved: boolean) => void
}) => {
  if (!ensurePlaybackClosedForMutation()) {
    data.complete(false)
    return
  }
  if (!ensureBoardDataReady(['nodes', 'templates', 'environment'])) {
    data.complete(false)
    return
  }
  return enqueueBoardMutation(async () => {
    let savedSuccessfully = false
    const items = Array.isArray(data.items) ? data.items : []

    if (items.length === 0) {
      ElMessage.warning(t('app.noDevicesToCreate'))
      data.complete(false)
      return
    }
    if (items.some(item => !item?.template?.manifest?.Name || !item.customName?.trim())) {
      ElMessage.warning(t('app.deviceBatchContainsInvalidItems'))
      data.complete(false)
      return
    }

    const createdNodes: DeviceNode[] = []
    const occupiedNodes = [...getVisibleDeviceNodes()]
    const nameConflicts: string[] = []

    for (const item of items) {
      const requestedLabel = item.customName.trim()
      const uniqueLabel = getUniqueLabel(requestedLabel, occupiedNodes)
      if (uniqueLabel !== requestedLabel) {
        nameConflicts.push(`${requestedLabel} -> ${uniqueLabel}`)
      }
      const node: DeviceNode = {
        id: createDeviceInstanceId(occupiedNodes),
        templateName: item.template.manifest.Name,
        label: uniqueLabel,
        position: getNextNodePosition(occupiedNodes),
        state: item.template.manifest.InitState || 'Working',
        width: DEFAULT_NODE_WIDTH,
        height: DEFAULT_NODE_HEIGHT,
        ...(item.runtime || {})
      }
      occupiedNodes.push(node)
      createdNodes.push(node)
    }

    if (nameConflicts.length > 0) {
      ElMessage.warning(t('app.deviceBatchNameConflictBlocked', {
        changes: nameConflicts.join(', ')
      }))
      data.complete(false)
      return
    }

    try {
      const mutation = await boardApi.addNodes(createdNodes, data.environmentVariables || [])
      nodes.value = getVisibleDeviceNodes(mutation.currentNodes)
      environmentVariables.value = mutation.environmentVariables
      reportEnvironmentChanges(mutation.environmentChanges)
      syncRuleDerivedEdges()
      const lastCreated = mutation.affectedDevices[mutation.affectedDevices.length - 1]
      await focusCreatedDeviceNode(lastCreated)
      ElMessage.success(t('app.devicesAddedWithCount', { count: createdNodes.length }))
      savedSuccessfully = true
    } catch (error: any) {
      console.error('批量创建设备或环境变量保存失败', error)
      if (!isDefinitiveMutationRejection(error)) {
        const [nodesRefreshed, environmentRefreshed] = await Promise.all([
          refreshDevices(),
          refreshEnvironmentVariables()
        ])
        const allPresent = createdNodes.length > 0
          && createdNodes.every(created => nodes.value.some(candidate => candidate.id === created.id))
        if (nodesRefreshed && environmentRefreshed && allPresent) {
          const lastCreated = nodes.value.find(candidate => candidate.id === createdNodes[createdNodes.length - 1].id)
          if (lastCreated) await focusCreatedDeviceNode(lastCreated)
          ElMessage.warning(t('app.devicesCreateOutcomeRefreshed', { count: createdNodes.length }))
          savedSuccessfully = true
          return
        }
      }
      const fallbackMessage = data.environmentVariables?.length
        ? t('app.saveEnvironmentFailed')
        : t('app.saveNodesFailed')
      ElMessage.error(localizedErrorMessage(error, fallbackMessage, locale.value))
    } finally {
      data.complete(savedSuccessfully)
    }
  })
}

const openRuleBuilder = () => {
  if (!ensurePlaybackClosedForMutation()) return
  openControlSection('rules')
  ruleBuilderVisible.value = true
}

const handleAddSpec = async (data: { 
  templateId: string, 
  devices: Array<{deviceId: string, deviceLabel: string, selectedApis: string[]}>, 
  formula: string,
  aConditions: SpecCondition[],
  ifConditions: SpecCondition[],
  thenConditions: SpecCondition[],
  complete: (saved: boolean) => void
}) => {
  if (!ensurePlaybackClosedForMutation()) {
    data.complete(false)
    return
  }
  let saved = false
  let attemptedSpec: Specification | null = null
  try {
    await enqueueBoardMutation(async () => {
      try {
        if (!ensureBoardDataReady(['nodes', 'templates', 'specs'])) return
        const { templateId, aConditions, ifConditions, thenConditions } = data
        const specTemplate = defaultSpecTemplates.find(t => t.id === templateId)
        const templateLabel = specTemplate?.label || templateId

        const newSpec: Specification = {
          id: 'spec_' + Date.now(),
          templateId: templateId as any,
          templateLabel,
          aConditions: aConditions || [],
          ifConditions: ifConditions || [],
          thenConditions: thenConditions || []
        }
        attemptedSpec = newSpec
        newSpec.formula = buildSpecFormula(newSpec, {
          nodes: nodes.value,
          deviceTemplates: deviceTemplates.value
        })
        newSpec.devices = buildSpecDeviceRefsFromConditions([
          ...(aConditions || []),
          ...(ifConditions || []),
          ...(thenConditions || [])
        ])

        if (specifications.value.some(spec => isSameSpecification(spec, newSpec))) {
          ElMessage.warning(t('app.specDuplicate'))
          return
        }

        const mutation = await boardApi.addSpec(newSpec)
        specifications.value = mutation.currentItems
        const createdSpec = mutation.affectedItem
        await focusSpecInInspector(createdSpec?.id)
        ElMessage.success(t('app.specificationAddedSuccessfully'))
        saved = true
      } catch (error: any) {
        console.error('[Board] Failed to add specification:', error)
        if (!isDefinitiveMutationRejection(error) && attemptedSpec) {
          const refreshed = await refreshSpecifications()
          if (refreshed && specifications.value.some(spec => isSameSpecification(spec, attemptedSpec!))) {
            ElMessage.warning(t('app.specCreateOutcomeRefreshed'))
            saved = true
            return
          }
        }
        ElMessage.error(extractApiErrorMessage(error, t('app.saveSpecsFailed')))
      }
    })
  } finally {
    data.complete(saved)
  }
}

const getNextNodePosition = (occupiedNodes: DeviceNode[] = nodes.value): { x: number; y: number } => {
  // 将节点放置在画布网格中央附近，确保无重叠
  const count = occupiedNodes.length

  // 基础节点尺寸（用于碰撞检测）
  const nodeWidth = DEFAULT_NODE_WIDTH
  const nodeHeight = DEFAULT_NODE_HEIGHT
  const minSpacing = 20 // 最小间距

  // 计算网格位置（以中心为原点）
  const cols = NODE_GRID_COLS
  const col = count % cols
  const row = Math.floor(count / cols)

  // 中心偏移：让第一个节点在中心，后面围绕中心排列
  const offsetCol = col - Math.floor(cols / 2)
  const offsetRow = row

  // 计算屏幕坐标
  const screenCenterX = window.innerWidth / 2
  const screenCenterY = window.innerHeight / 2

  // 应用偏移
  let screenX = screenCenterX + offsetCol * NODE_SPACING_X
  let screenY = screenCenterY + offsetRow * NODE_SPACING_Y

  // 碰撞检测和位置调整
  let attempts = 0
  const maxAttempts = 50

  while (attempts < maxAttempts) {
    // 转换到世界坐标
    const worldX = (screenX - canvasPan.value.x) / canvasZoom.value
    const worldY = (screenY - canvasPan.value.y) / canvasZoom.value

    // 检查与其他节点的重叠
    const hasOverlap = occupiedNodes.some(node => {
      const dx = Math.abs(node.position.x - worldX)
      const dy = Math.abs(node.position.y - worldY)
      const minDistanceX = (node.width + nodeWidth) / 2 + minSpacing
      const minDistanceY = (node.height + nodeHeight) / 2 + minSpacing

      return dx < minDistanceX && dy < minDistanceY
    })

    if (!hasOverlap) {
      // 找到合适位置
      return { x: worldX, y: worldY }
    }

    // 位置被占用，向外扩展查找
    attempts++
    const angle = (attempts * 137.5) * (Math.PI / 180) // 黄金角
    const radius = Math.sqrt(attempts) * Math.max(NODE_SPACING_X, NODE_SPACING_Y) / 2

    screenX = screenCenterX + Math.cos(angle) * radius
    screenY = screenCenterY + Math.sin(angle) * radius
  }

  // 如果找不到合适位置，使用随机偏移
  const randomAngle = Math.random() * 2 * Math.PI
  const randomRadius = 100 + Math.random() * 200
  screenX = screenCenterX + Math.cos(randomAngle) * randomRadius
  screenY = screenCenterY + Math.sin(randomAngle) * randomRadius

  const finalX = (screenX - canvasPan.value.x) / canvasZoom.value
  const finalY = (screenY - canvasPan.value.y) / canvasZoom.value

  return { x: finalX, y: finalY }
}

onBeforeUnmount(() => {
  boardLifecycleDisposed = true
  layoutSaveFeedbackSuppressed = true
  pollingAborted.value = true
  stopTraceAnimation()
  ruleRecommendationRequestEpoch += 1
  if (ruleRecommendationRequestId.value) void boardApi.cancelRecommendation(ruleRecommendationRequestId.value)
  ruleRecommendationAbortController.value?.abort()
  ruleRecommendationAbortController.value = null
  deviceRecommendationRequestEpoch += 1
  if (deviceRecommendationRequestId.value) void boardApi.cancelRecommendation(deviceRecommendationRequestId.value)
  deviceRecommendationAbortController.value?.abort()
  deviceRecommendationAbortController.value = null
  specRecommendationRequestEpoch += 1
  if (specRecommendationRequestId.value) void boardApi.cancelRecommendation(specRecommendationRequestId.value)
  specRecommendationAbortController.value?.abort()
  specRecommendationAbortController.value = null
  scenarioRecommendationRequestEpoch += 1
  if (scenarioRecommendationRequestId.value) void boardApi.cancelRecommendation(scenarioRecommendationRequestId.value)
  scenarioRecommendationAbortController.value?.abort()
  scenarioRecommendationAbortController.value = null
  if (recommendationProgressTimer) {
    clearInterval(recommendationProgressTimer)
    recommendationProgressTimer = null
  }
  if (taskInboxRefreshTimer) {
    clearInterval(taskInboxRefreshTimer)
    taskInboxRefreshTimer = null
  }
  void flushPendingBoardLayout({ silent: true })
  window.removeEventListener('keydown', onGlobalKeydown)
  window.removeEventListener('resize', updateActionDockViewport)
  window.removeEventListener('pointermove', onCanvasPointerMove)
  window.removeEventListener('pointerup', onCanvasPointerUp)
  window.removeEventListener('pointermove', onCanvasMapPointerMove)
  window.removeEventListener('pointerup', onCanvasMapPointerUp)
  canvasMapDragElement = null
  canvasMapDragRect = null
  canvasMapDragPointerId = null
})

const refreshDevicesFromChat = async () => enqueueBoardMutation(() => refreshDevices())
const refreshEnvironmentFromChat = async () => enqueueBoardMutation(() => refreshEnvironmentVariables())
const refreshRulesFromChat = async () => enqueueBoardMutation(() => refreshRules())
const refreshSpecificationsFromChat = async () => enqueueBoardMutation(() => refreshSpecifications())
const refreshTemplatesFromChat = async () => enqueueBoardMutation(() => refreshDeviceTemplates())
const refreshRunHistoryFromChat = async () => refreshRunHistory()
const refreshAllBoardStateFromChat = async () => enqueueBoardMutation(() => refreshAllBoardState())

const getChatSuggestionContext = () => {
  const visibleNodes = getVisibleDeviceNodes()
  const labelsById = new Map(visibleNodes.map(node => [node.id, node.label]))
  const displayDevice = (deviceId?: string) =>
    (deviceId ? labelsById.get(deviceId) : undefined) || t('app.unknownModelItem')

  return {
    deviceCount: visibleNodes.length,
    ruleCount: rules.value.length,
    specCount: specifications.value.length,
    templateCount: deviceTemplates.value.length,
    devices: visibleNodes.slice(0, 8).map(node => ({
      label: node.label,
      templateName: node.templateName
    })),
    rules: rules.value.slice(0, 6).map((rule, index) => ({
      name: rule.name?.trim() || t('app.ruleNumber', { number: index + 1 }),
      description: `${(rule.sources || []).map(source => displayDevice(source.fromId)).join(' + ')} -> ${displayDevice(rule.toId)}.${rule.toApi || t('app.unknownModelItem')}`
    })),
    specs: specifications.value.slice(0, 6).map((spec, index) => ({
      name: getSpecResultDisplayTitle(spec, index),
      formulaPreview: buildSpecFormula(spec, {
        nodes: nodes.value,
        deviceTemplates: deviceTemplates.value
      })
    })),
    templates: deviceTemplates.value
      .map(template => template.manifest?.Name || template.name)
      .filter(Boolean)
      .slice(0, 10)
  }
}

defineExpose({
  refreshDevices: refreshDevicesFromChat,
  refreshEnvironmentVariables: refreshEnvironmentFromChat,
  refreshRules: refreshRulesFromChat,
  refreshSpecifications: refreshSpecificationsFromChat,
  refreshDeviceTemplates: refreshTemplatesFromChat,
  refreshRunHistory: refreshRunHistoryFromChat,
  refreshAllBoardState: refreshAllBoardStateFromChat,
  getChatSuggestionContext,
  isChatInteractionLocked: () => isSceneReplacementInProgress.value || isModelPlaybackActive.value
})

// ==== Verification Logic ====
const isVerifying = ref(false)
const verificationResult = ref<any>(null)
const verificationError = ref<string | null>(null)

type RunSubmission<T> = { request: T; signature: string; taskId?: number }

const activeVerificationSubmission = ref<RunSubmission<VerificationRequest> | null>(null)
const activeSimulationSubmission = ref<RunSubmission<SimulationRequest> | null>(null)

const attachLocalRunSubmission = <T extends Record<string, any>, R>(
  result: T,
  submission: RunSubmission<R> | null
): T => submission ? { ...result, localRunSubmission: submission } : result

const compareRunToCurrentBoard = (result: any, kind: 'verification' | 'simulation'): RunBoardComparison => {
  const submission = result?.localRunSubmission as RunSubmission<VerificationRequest | SimulationRequest> | undefined
  if (!submission) return 'NOT_COMPARED'
  try {
    const request = kind === 'verification'
      ? buildVerificationRequestPayload({
          nodes: nodes.value,
          deviceTemplates: deviceTemplates.value,
          environmentVariables: environmentVariables.value,
          rules: rules.value,
          specifications: specifications.value,
          isAttack: submission.request.isAttack,
          attackBudget: submission.request.attackBudget,
          enablePrivacy: submission.request.enablePrivacy
        })
      : buildSimulationRequestPayload({
          nodes: nodes.value,
          deviceTemplates: deviceTemplates.value,
          environmentVariables: environmentVariables.value,
          rules: rules.value,
          steps: (submission.request as SimulationRequest).steps,
          isAttack: submission.request.isAttack,
          attackBudget: submission.request.attackBudget,
          enablePrivacy: submission.request.enablePrivacy
        })
    return buildModelRunSignature(request, deviceTemplates.value) === submission.signature
      ? 'UNCHANGED'
      : 'CHANGED'
  } catch {
    return 'UNAVAILABLE'
  }
}

const submissionForTask = <T,>(submission: RunSubmission<T> | null, taskId: number): RunSubmission<T> | null =>
  submission?.taskId === taskId ? submission : null

// ==== Rule Recommendation Logic ====
const isRecommendingRules = ref(false)
const isRecommendingDevices = ref(false)
const isRecommendingSpecs = ref(false)
const isRecommendingScenario = ref(false)
const ruleRecommendations = ref<RuleRecommendation[]>([])
const ruleRecommendationMessage = ref('')
const localizedRecommendationText = (value: unknown, fallback = ''): string =>
  localizedTextOrFallback(value, fallback, locale.value)
const ruleRecommendationFilteredCount = ref(0)
const ruleRecommendationFilteredItems = ref<RecommendationFilteredItem[]>([])
const ruleRecommendationAdjustedItems = ref<RecommendationAdjustmentItem[]>([])
const ruleRecommendationRawCandidateCount = ref(0)
const ruleRecommendationInspectedCount = ref(0)
const ruleRecommendationTruncatedCount = ref(0)
const appliedRuleRecommendations = ref<Set<number>>(new Set())
const applyingRuleRecommendations = ref<Set<number>>(new Set())
const showRecommendationPanel = ref(false)
const ruleRecommendationRequested = ref(false)
const ruleRecommendationFilters = reactive({
  maxRecommendations: 5,
  category: 'all',
  userRequirement: ''
})
const ruleRecommendationAbortController = ref<AbortController | null>(null)
const ruleRecommendationRequestId = ref<string | null>(null)
let ruleRecommendationRequestEpoch = 0
const ruleRecommendationCategories = [
  { labelKey: 'app.recommendationCategoryAll', value: 'all' },
  { labelKey: 'app.recommendationCategorySecurity', value: 'security' },
  { labelKey: 'app.recommendationCategoryEnergySaving', value: 'energy_saving' },
  { labelKey: 'app.recommendationCategoryComfort', value: 'comfort' },
  { labelKey: 'app.recommendationCategoryAutomation', value: 'automation' }
]

const validateRecommendationCount = (value: unknown, field = t('app.maxRecommendationsField')): number =>
  optionalIntegerInRange(value, field, 5, 1, 10)

const formatRecommendationFilteredType = (type: unknown): string => {
  switch (String(type || '').toLowerCase()) {
    case 'device':
      return t('app.filteredCandidateDevice')
    case 'rule':
      return t('app.filteredCandidateRule')
    case 'spec':
    case 'specification':
      return t('app.filteredCandidateSpecification')
    case 'environment':
    case 'environmentVariable':
      return t('app.filteredCandidateEnvironment')
    default:
      return t('app.filteredCandidateItem')
  }
}

const formatRecommendationFilteredItem = (item: RecommendationFilteredItem): string => {
  const index = item.index || '?'
  const reason = localizedRecommendationText(
    item.reason,
    t('app.recommendationFilteredUnknownReason')
  )
  const type = formatRecommendationFilteredType(item.type)
  const label = item.label?.trim()
  return label
    ? t('app.recommendationFilteredReasonWithLabel', { type, index, label, reason })
    : t('app.recommendationFilteredReason', { type, index, reason })
}

const formatScenarioAdjustmentValue = (key: string, value: unknown): string | null => {
  if (key === 'suggestedLabel') return t('app.scenarioDefaultSuggestedLabel', { value })
  if (key === 'state') return t('app.scenarioDefaultInitialState', { value })
  if (key === 'currentStateTrust') return t('app.scenarioDefaultStateTrust', { value: t(`app.${value}`) })
  if (key === 'currentStatePrivacy') return t('app.scenarioDefaultStatePrivacy', { value: t(`app.${value}`) })
  if (key === 'value') return t('app.scenarioDefaultEnvironmentValue', { value })
  if (key === 'trust') return t('app.scenarioDefaultEnvironmentTrust', { value: t(`app.${value}`) })
  if (key === 'privacy') return t('app.scenarioDefaultEnvironmentPrivacy', { value: t(`app.${value}`) })
  if (key.startsWith('variables.') && key.endsWith('.trust')) {
    const variable = key.slice('variables.'.length, -'.trust'.length)
    return t('app.scenarioDefaultVariableTrust', { variable, value: t(`app.${value}`) })
  }
  if (key.startsWith('variables.') && key.endsWith('.value')) {
    const variable = key.slice('variables.'.length, -'.value'.length)
    return t('app.scenarioDefaultVariableValue', { variable, value })
  }
  if (key.startsWith('privacies.') && key.endsWith('.privacy')) {
    const variable = key.slice('privacies.'.length, -'.privacy'.length)
    return t('app.scenarioDefaultVariablePrivacy', { variable, value: t(`app.${value}`) })
  }
  return null
}

const formatRecommendationAdjustmentItem = (item: RecommendationAdjustmentItem): string => {
  const reason = localizedRecommendationText(
    item.reason,
    t('app.recommendationAdjustedUnknownReason')
  )
  const label = item.label?.trim() || formatRecommendationFilteredType(item.type)
  const values = Object.entries(item.appliedValues || {})
    .map(([key, value]) => formatScenarioAdjustmentValue(key, value))
    .filter((value): value is string => Boolean(value))
  const hasLayoutDefaults = Object.keys(item.appliedValues || {})
    .some(key => key === 'position' || key.startsWith('position.') || key === 'width' || key === 'height')
  if (hasLayoutDefaults) values.push(t('app.scenarioDefaultCanvasLayout'))
  return t('app.recommendationAdjustedReason', {
    label,
    reason,
    values: values.length > 0 ? t('app.recommendationAdjustedValues', { values: values.join('；') }) : ''
  })
}

const specificationExists = (recommendation: any): boolean => {
  const key = buildSpecificationSemanticKey(recommendation)
  return specifications.value.some(spec => buildSpecificationSemanticKey(spec) === key)
}

const buildSpecDeviceRefsFromConditions = (
  conditions: SpecCondition[],
  lookupNodes: DeviceNode[] = nodes.value
) => {
  const byDevice = new Map<string, { deviceId: string; deviceLabel: string; selectedApis: string[] }>()
  conditions.forEach(condition => {
    if (!condition.deviceId) return
    const existing = byDevice.get(condition.deviceId)
    if (existing) {
      if (condition.targetType === 'api' && condition.key && !existing.selectedApis.includes(condition.key)) {
        existing.selectedApis.push(condition.key)
      }
      return
    }
    const node = lookupNodes.find(candidate => candidate.id === condition.deviceId)
    byDevice.set(condition.deviceId, {
      deviceId: condition.deviceId,
      deviceLabel: condition.deviceLabel || node?.label || condition.deviceId,
      selectedApis: condition.targetType === 'api' && condition.key ? [condition.key] : []
    })
  })
  return Array.from(byDevice.values())
}

type RecommendationPanelKind = 'rule' | 'device' | 'spec' | 'scenario'

const recommendationStopRequestsInFlight = new Set<RecommendationPanelKind>()

const stopActiveRecommendation = async (
  kind: RecommendationPanelKind,
  requestIdRef: Ref<string | null>,
  abortControllerRef: Ref<AbortController | null>,
  setRunning: (running: boolean) => void,
  cancelledMessageKey: string,
  options: { showMessage?: boolean } = {}
) => {
  if (recommendationStopRequestsInFlight.has(kind)) return
  recommendationStopRequestsInFlight.add(kind)
  const requestId = requestIdRef.value
  const controller = abortControllerRef.value
  controller?.abort()
  if (abortControllerRef.value === controller) abortControllerRef.value = null
  try {
    if (requestId) await boardApi.cancelRecommendation(requestId)
    if (requestIdRef.value === requestId) requestIdRef.value = null
    setRunning(false)
    if (options.showMessage !== false) {
      ElMessage.info(t(cancelledMessageKey))
    }
  } catch (error) {
    console.error('Failed to cancel recommendation request:', error)
    if (requestId && requestIdRef.value === requestId) setRunning(true)
    ElMessage.warning(t('app.recommendationStopRequestMayStillBeRunning'))
  } finally {
    recommendationStopRequestsInFlight.delete(kind)
  }
}

const getRunningRecommendationKind = (): RecommendationPanelKind | null => {
  if (isRecommendingScenario.value) return 'scenario'
  if (isRecommendingRules.value) return 'rule'
  if (isRecommendingDevices.value) return 'device'
  if (isRecommendingSpecs.value) return 'spec'
  return null
}

const isAnyRecommendationRunning = (): boolean => getRunningRecommendationKind() !== null

const recommendationProgressElapsed = ref(0)
const recommendationProgressStage = ref<InteractiveOperationStage>('QUEUED')
const recommendationProgressRequestId = ref<string | null>(null)
let recommendationProgressTimer: ReturnType<typeof setInterval> | null = null
let recommendationProgressRefreshInFlight = false
const refreshRecommendationProgress = async (kind: RecommendationPanelKind) => {
  if (recommendationProgressRefreshInFlight) return
  const requestId = recommendationProgressRequestId.value
  if (!requestId) return
  recommendationProgressRefreshInFlight = true
  try {
    const status = await boardApi.getRecommendationStatus(requestId)
    if (getRunningRecommendationKind() === kind && recommendationProgressRequestId.value === requestId) {
      recommendationProgressStage.value = status.stage
    }
  } catch {
    // Registration and completion can race with this read; the main request remains authoritative.
  } finally {
    recommendationProgressRefreshInFlight = false
  }
}
watch(() => getRunningRecommendationKind(), kind => {
  if (recommendationProgressTimer) {
    clearInterval(recommendationProgressTimer)
    recommendationProgressTimer = null
  }
  recommendationProgressElapsed.value = 0
  recommendationProgressStage.value = 'QUEUED'
  if (!kind) {
    recommendationProgressRequestId.value = null
    return
  }
  const startedAt = Date.now()
  void refreshRecommendationProgress(kind)
  recommendationProgressTimer = setInterval(() => {
    recommendationProgressElapsed.value = Math.floor((Date.now() - startedAt) / 1000)
    void refreshRecommendationProgress(kind)
  }, 1000)
})

const isAnyRecommendationPanelVisible = (): boolean =>
  showRecommendationPanel.value ||
  showDeviceRecommendationPanel.value ||
  showSpecRecommendationPanel.value ||
  showScenarioRecommendationPanel.value

const isRecommendationRunningForAnother = (kind: RecommendationPanelKind): boolean => {
  const runningKind = getRunningRecommendationKind()
  return runningKind !== null && runningKind !== kind
}

const canOpenRecommendationPanel = (kind: RecommendationPanelKind): boolean => {
  if (simulationAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCurrentSimulationFirst'), type: 'warning' })
    return false
  }
  if (traceAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCounterexampleFirst'), type: 'warning' })
    return false
  }
  if (isRecommendationRunningForAnother(kind)) {
    ElMessage.warning({ message: t('app.recommendationGenerationInProgress'), type: 'warning' })
    return false
  }
  return true
}

const resetRuleRecommendationResults = () => {
  ruleRecommendations.value = []
  ruleRecommendationMessage.value = ''
  ruleRecommendationFilteredCount.value = 0
  ruleRecommendationFilteredItems.value = []
  ruleRecommendationAdjustedItems.value = []
  ruleRecommendationRawCandidateCount.value = 0
  ruleRecommendationInspectedCount.value = 0
  ruleRecommendationTruncatedCount.value = 0
  appliedRuleRecommendations.value.clear()
  applyingRuleRecommendations.value.clear()
  ruleRecommendationRequested.value = false
}

const resetDeviceRecommendationResults = () => {
  deviceRecommendations.value = []
  deviceRecommendationMessage.value = ''
  deviceRecommendationFilteredCount.value = 0
  deviceRecommendationFilteredItems.value = []
  deviceRecommendationAdjustedItems.value = []
  deviceRecommendationRawCandidateCount.value = 0
  deviceRecommendationInspectedCount.value = 0
  deviceRecommendationTruncatedCount.value = 0
  appliedDeviceRecommendations.value.clear()
  applyingDeviceRecommendations.value.clear()
  deviceRecommendationRequested.value = false
}

const resetSpecRecommendationResults = () => {
  specRecommendations.value = []
  specRecommendationMessage.value = ''
  specRecommendationFilteredCount.value = 0
  specRecommendationFilteredItems.value = []
  specRecommendationRawCandidateCount.value = 0
  specRecommendationInspectedCount.value = 0
  specRecommendationTruncatedCount.value = 0
  appliedSpecRecommendations.value.clear()
  applyingSpecRecommendations.value.clear()
  specRecommendationRequested.value = false
}

const resetScenarioRecommendationResults = () => {
  scenarioRecommendationResult.value = null
  scenarioRecommendationMessage.value = ''
  scenarioRecommendationRequested.value = false
}

function closeResultSurfaces() {
  fuzzingResultRequestEpoch += 1
  verificationResult.value = null
  verificationError.value = null
  simulationResult.value = null
  simulationError.value = null
  fuzzingResult.value = null
  fuzzingError.value = null
  fuzzingResultLoading.value = false
  showFuzzingResultDialog.value = false
}

const openRuleRecommendationPanel = (): boolean => {
  if (showRecommendationPanel.value) return true
  if (!canOpenRecommendationPanel('rule')) return false
  closeResultSurfaces()
  closeHistoryPanel()
  showSimulationPanel.value = false
  showVerificationPanel.value = false
  showFuzzingPanel.value = false
  closeDeviceRecommendationPanel()
  closeSpecRecommendationPanel()
  closeScenarioRecommendationPanel()
  resetRuleRecommendationResults()
  showRecommendationPanel.value = true
  return true
}

const openDeviceRecommendationPanel = (): boolean => {
  if (showDeviceRecommendationPanel.value) return true
  if (!canOpenRecommendationPanel('device')) return false
  closeResultSurfaces()
  closeHistoryPanel()
  showSimulationPanel.value = false
  showVerificationPanel.value = false
  showFuzzingPanel.value = false
  closeRecommendationPanel()
  closeSpecRecommendationPanel()
  closeScenarioRecommendationPanel()
  resetDeviceRecommendationResults()
  showDeviceRecommendationPanel.value = true
  return true
}

const openSpecRecommendationPanel = (): boolean => {
  if (showSpecRecommendationPanel.value) return true
  if (!canOpenRecommendationPanel('spec')) return false
  closeResultSurfaces()
  closeHistoryPanel()
  showSimulationPanel.value = false
  showVerificationPanel.value = false
  showFuzzingPanel.value = false
  closeRecommendationPanel()
  closeDeviceRecommendationPanel()
  closeScenarioRecommendationPanel()
  resetSpecRecommendationResults()
  showSpecRecommendationPanel.value = true
  return true
}

const openScenarioRecommendationPanel = (): boolean => {
  if (showScenarioRecommendationPanel.value) return true
  if (!canOpenRecommendationPanel('scenario')) return false
  closeResultSurfaces()
  closeHistoryPanel()
  showSimulationPanel.value = false
  showVerificationPanel.value = false
  showFuzzingPanel.value = false
  closeRecommendationPanel()
  closeDeviceRecommendationPanel()
  closeSpecRecommendationPanel()
  closeScenarioRecommendationPanel()
  resetScenarioRecommendationResults()
  showScenarioRecommendationPanel.value = true
  return true
}

const fetchRuleRecommendations = async () => {
  if (isRecommendingRules.value) {
    ruleRecommendationRequestEpoch += 1
    await stopActiveRecommendation(
      'rule',
      ruleRecommendationRequestId,
      ruleRecommendationAbortController,
      running => { isRecommendingRules.value = running },
      'app.ruleRecommendationCancelled'
    )
    return
  }
  if (!ensureBoardDataReady(['nodes', 'templates', 'rules'])) return

  if (showRecommendationPanel.value) {
    if (!canOpenRecommendationPanel('rule')) return
  } else if (!openRuleRecommendationPanel()) {
    return
  }

  isRecommendingRules.value = true
  ruleRecommendationRequested.value = true
  ruleRecommendations.value = []
  ruleRecommendationMessage.value = ''
  ruleRecommendationFilteredCount.value = 0
  ruleRecommendationFilteredItems.value = []
  ruleRecommendationAdjustedItems.value = []
  ruleRecommendationRawCandidateCount.value = 0
  ruleRecommendationInspectedCount.value = 0
  ruleRecommendationTruncatedCount.value = 0
  appliedRuleRecommendations.value.clear()
  applyingRuleRecommendations.value.clear()
  const requestEpoch = ++ruleRecommendationRequestEpoch
  const controller = new AbortController()
  const requestId = crypto.randomUUID()
  ruleRecommendationAbortController.value = controller
  ruleRecommendationRequestId.value = requestId
  recommendationProgressRequestId.value = requestId
  try {
    const response = await rulesApi.recommendRules(
      validateRecommendationCount(ruleRecommendationFilters.maxRecommendations),
      ruleRecommendationFilters.category,
      locale.value,
      ruleRecommendationFilters.userRequirement,
      requestId,
      controller.signal
    )
    if (requestEpoch !== ruleRecommendationRequestEpoch) return
    ruleRecommendations.value = response.recommendations
    ruleRecommendationMessage.value = localizedRecommendationText(
      response.message,
      t('app.recommendationsFound', { count: response.count })
    )
    ruleRecommendationFilteredCount.value = response.filteredCount
    ruleRecommendationFilteredItems.value = response.filteredItems
    ruleRecommendationAdjustedItems.value = response.adjustedItems
    ruleRecommendationRawCandidateCount.value = response.rawCandidateCount
    ruleRecommendationInspectedCount.value = response.inspectedCount
    ruleRecommendationTruncatedCount.value = response.truncatedCount
  } catch (error: any) {
    if (requestEpoch !== ruleRecommendationRequestEpoch) return
    // 如果是取消请求，不显示错误
    if (error.name === 'CanceledError' || error.code === 'ERR_CANCELED') {
      return
    }
    console.error('Failed to fetch rule recommendations:', error)
    ElMessage.error(extractRecommendationErrorMessage(error, t('app.failedToFetchRuleRecommendations')))
  } finally {
    if (requestEpoch === ruleRecommendationRequestEpoch) {
      isRecommendingRules.value = false
      if (ruleRecommendationAbortController.value === controller) {
        ruleRecommendationAbortController.value = null
      }
      if (ruleRecommendationRequestId.value === requestId) ruleRecommendationRequestId.value = null
    }
  }
}

// 关闭推荐面板
const closeRecommendationPanel = () => {
  ruleRecommendationRequestEpoch += 1
  void stopActiveRecommendation(
    'rule',
    ruleRecommendationRequestId,
    ruleRecommendationAbortController,
    running => { isRecommendingRules.value = running },
    'app.ruleRecommendationCancelled',
    { showMessage: false }
  )
  showRecommendationPanel.value = false
  resetRuleRecommendationResults()
}

// ==== Device Recommendation Logic ====
const deviceRecommendations = ref<DeviceRecommendation[]>([])
const deviceRecommendationMessage = ref('')
const deviceRecommendationFilteredCount = ref(0)
const deviceRecommendationFilteredItems = ref<RecommendationFilteredItem[]>([])
const deviceRecommendationAdjustedItems = ref<RecommendationAdjustmentItem[]>([])
const deviceRecommendationRawCandidateCount = ref(0)
const deviceRecommendationInspectedCount = ref(0)
const deviceRecommendationTruncatedCount = ref(0)
const appliedDeviceRecommendations = ref<Set<number>>(new Set())
const applyingDeviceRecommendations = ref<Set<number>>(new Set())
const showDeviceRecommendationPanel = ref(false)
const deviceRecommendationAbortController = ref<AbortController | null>(null)
const deviceRecommendationRequestId = ref<string | null>(null)
const deviceRecommendationRequested = ref(false)
const deviceRecommendationFilters = reactive({
  maxRecommendations: 5,
  userRequirement: ''
})
let deviceRecommendationRequestEpoch = 0

// ==== Specification Recommendation Logic ====
const specRecommendations = ref<SpecificationRecommendation[]>([])
const specRecommendationMessage = ref('')
const specRecommendationFilteredCount = ref(0)
const specRecommendationFilteredItems = ref<RecommendationFilteredItem[]>([])
const specRecommendationRawCandidateCount = ref(0)
const specRecommendationInspectedCount = ref(0)
const specRecommendationTruncatedCount = ref(0)
const appliedSpecRecommendations = ref<Set<number>>(new Set())
const applyingSpecRecommendations = ref<Set<number>>(new Set())
const showSpecRecommendationPanel = ref(false)
const specRecommendationAbortController = ref<AbortController | null>(null)
const specRecommendationRequestId = ref<string | null>(null)
const specRecommendationRequested = ref(false)
const specRecommendationFilters = reactive({
  maxRecommendations: 5,
  category: 'all',
  userRequirement: ''
})
let specRecommendationRequestEpoch = 0
const specRecommendationCategories = [
  { labelKey: 'app.recommendationCategoryAll', value: 'all' },
  { labelKey: 'app.recommendationCategorySafety', value: 'safety' },
  { labelKey: 'app.recommendationCategoryResponse', value: 'response' },
  { labelKey: 'app.recommendationCategoryConsistency', value: 'consistency' },
  { labelKey: 'app.recommendationCategoryPrivacy', value: 'privacy' }
]

// ==== Coupled Scenario Recommendation Logic ====
const showScenarioRecommendationPanel = ref(false)
const scenarioRecommendationAbortController = ref<AbortController | null>(null)
const scenarioRecommendationRequestId = ref<string | null>(null)
const scenarioRecommendationRequested = ref(false)
const scenarioRecommendationMessage = ref('')
const scenarioRecommendationResult = ref<ScenarioRecommendationResult | null>(null)
const scenarioRecommendationFilters = reactive({
  maxDevices: 6,
  maxRules: 5,
  maxSpecs: 5,
  userRequirement: ''
})
let scenarioRecommendationRequestEpoch = 0
const recommendedScenarioScene = computed(() => scenarioRecommendationResult.value?.scene || null)

const fetchDeviceRecommendations = async () => {
  if (isRecommendingDevices.value) {
    deviceRecommendationRequestEpoch += 1
    await stopActiveRecommendation(
      'device',
      deviceRecommendationRequestId,
      deviceRecommendationAbortController,
      running => { isRecommendingDevices.value = running },
      'app.deviceRecommendationCancelled'
    )
    return
  }
  if (!ensureBoardDataReady(['nodes', 'templates'])) return

  if (showDeviceRecommendationPanel.value) {
    if (!canOpenRecommendationPanel('device')) return
  } else if (!openDeviceRecommendationPanel()) {
    return
  }
  
  isRecommendingDevices.value = true
  deviceRecommendationRequested.value = true
  deviceRecommendations.value = []
  deviceRecommendationMessage.value = ''
  deviceRecommendationFilteredCount.value = 0
  deviceRecommendationFilteredItems.value = []
  deviceRecommendationAdjustedItems.value = []
  deviceRecommendationRawCandidateCount.value = 0
  deviceRecommendationInspectedCount.value = 0
  deviceRecommendationTruncatedCount.value = 0
  appliedDeviceRecommendations.value.clear()
  applyingDeviceRecommendations.value.clear()
  const requestEpoch = ++deviceRecommendationRequestEpoch
  const controller = new AbortController()
  const requestId = crypto.randomUUID()
  deviceRecommendationAbortController.value = controller
  deviceRecommendationRequestId.value = requestId
  recommendationProgressRequestId.value = requestId
  
  try {
    const response = await boardApi.recommendRelatedDevices(
      validateRecommendationCount(deviceRecommendationFilters.maxRecommendations),
      locale.value,
      deviceRecommendationFilters.userRequirement,
      requestId,
      controller.signal
    )
    if (requestEpoch !== deviceRecommendationRequestEpoch) return
    deviceRecommendations.value = response.recommendations
    deviceRecommendationMessage.value = localizedRecommendationText(
      response.message,
      t('app.recommendationsFound', { count: response.count })
    )
    deviceRecommendationFilteredCount.value = response.filteredCount
    deviceRecommendationFilteredItems.value = response.filteredItems
    deviceRecommendationAdjustedItems.value = response.adjustedItems
    deviceRecommendationRawCandidateCount.value = response.rawCandidateCount
    deviceRecommendationInspectedCount.value = response.inspectedCount
    deviceRecommendationTruncatedCount.value = response.truncatedCount
  } catch (error: any) {
    if (requestEpoch !== deviceRecommendationRequestEpoch) return
    if (error.name === 'CanceledError' || error.code === 'ERR_CANCELED') {
      return
    }
    console.error('Failed to fetch device recommendations:', error)
    ElMessage.error(extractRecommendationErrorMessage(error, t('app.failedToFetchDeviceRecommendations')))
  } finally {
    if (requestEpoch === deviceRecommendationRequestEpoch) {
      isRecommendingDevices.value = false
      if (deviceRecommendationAbortController.value === controller) {
        deviceRecommendationAbortController.value = null
      }
      if (deviceRecommendationRequestId.value === requestId) deviceRecommendationRequestId.value = null
    }
  }
}

// 关闭设备推荐面板
const closeDeviceRecommendationPanel = () => {
  deviceRecommendationRequestEpoch += 1
  void stopActiveRecommendation(
    'device',
    deviceRecommendationRequestId,
    deviceRecommendationAbortController,
    running => { isRecommendingDevices.value = running },
    'app.deviceRecommendationCancelled',
    { showMessage: false }
  )
  showDeviceRecommendationPanel.value = false
  resetDeviceRecommendationResults()
}

// 获取规约推荐
const fetchSpecRecommendations = async () => {
  if (isRecommendingSpecs.value) {
    specRecommendationRequestEpoch += 1
    await stopActiveRecommendation(
      'spec',
      specRecommendationRequestId,
      specRecommendationAbortController,
      running => { isRecommendingSpecs.value = running },
      'app.specificationRecommendationCancelled'
    )
    return
  }
  if (!ensureBoardDataReady(['nodes', 'templates', 'rules', 'specs'])) return

  if (showSpecRecommendationPanel.value) {
    if (!canOpenRecommendationPanel('spec')) return
  } else if (!openSpecRecommendationPanel()) {
    return
  }

  isRecommendingSpecs.value = true
  specRecommendationRequested.value = true
  specRecommendations.value = []
  specRecommendationMessage.value = ''
  specRecommendationFilteredCount.value = 0
  specRecommendationFilteredItems.value = []
  specRecommendationRawCandidateCount.value = 0
  specRecommendationInspectedCount.value = 0
  specRecommendationTruncatedCount.value = 0
  appliedSpecRecommendations.value.clear()
  applyingSpecRecommendations.value.clear()
  const requestEpoch = ++specRecommendationRequestEpoch
  const controller = new AbortController()
  const requestId = crypto.randomUUID()
  specRecommendationAbortController.value = controller
  specRecommendationRequestId.value = requestId
  recommendationProgressRequestId.value = requestId

  try {
    const response = await boardApi.recommendSpecifications(
      validateRecommendationCount(specRecommendationFilters.maxRecommendations),
      specRecommendationFilters.category,
      locale.value,
      specRecommendationFilters.userRequirement,
      requestId,
      controller.signal
    )
    if (requestEpoch !== specRecommendationRequestEpoch) return
    specRecommendations.value = response.recommendations
    specRecommendationMessage.value = localizedRecommendationText(
      response.message,
      t('app.recommendationsFound', { count: response.count })
    )
    specRecommendationFilteredCount.value = response.filteredCount
    specRecommendationFilteredItems.value = response.filteredItems
    specRecommendationRawCandidateCount.value = response.rawCandidateCount
    specRecommendationInspectedCount.value = response.inspectedCount
    specRecommendationTruncatedCount.value = response.truncatedCount
  } catch (error: any) {
    if (requestEpoch !== specRecommendationRequestEpoch) return
    if (error.name === 'CanceledError' || error.code === 'ERR_CANCELED') {
      return
    }
    console.error('Failed to fetch specification recommendations:', error)
    ElMessage.error(extractRecommendationErrorMessage(error, t('app.failedToFetchSpecificationRecommendations')))
  } finally {
    if (requestEpoch === specRecommendationRequestEpoch) {
      isRecommendingSpecs.value = false
      if (specRecommendationAbortController.value === controller) {
        specRecommendationAbortController.value = null
      }
      if (specRecommendationRequestId.value === requestId) specRecommendationRequestId.value = null
    }
  }
}

// 关闭规约推荐面板
const closeSpecRecommendationPanel = () => {
  specRecommendationRequestEpoch += 1
  void stopActiveRecommendation(
    'spec',
    specRecommendationRequestId,
    specRecommendationAbortController,
    running => { isRecommendingSpecs.value = running },
    'app.specificationRecommendationCancelled',
    { showMessage: false }
  )
  showSpecRecommendationPanel.value = false
  resetSpecRecommendationResults()
}

const fetchScenarioRecommendation = async () => {
  if (isRecommendingScenario.value) {
    scenarioRecommendationRequestEpoch += 1
    await stopActiveRecommendation(
      'scenario',
      scenarioRecommendationRequestId,
      scenarioRecommendationAbortController,
      running => { isRecommendingScenario.value = running },
      'app.scenarioRecommendationCancelled'
    )
    return
  }
  if (!ensureBoardDataReady()) return

  if (showScenarioRecommendationPanel.value) {
    if (!canOpenRecommendationPanel('scenario')) return
  } else if (!openScenarioRecommendationPanel()) {
    return
  }

  isRecommendingScenario.value = true
  scenarioRecommendationRequested.value = true
  scenarioRecommendationResult.value = null
  scenarioRecommendationMessage.value = ''
  const requestEpoch = ++scenarioRecommendationRequestEpoch
  const controller = new AbortController()
  const requestId = crypto.randomUUID()
  scenarioRecommendationAbortController.value = controller
  scenarioRecommendationRequestId.value = requestId
  recommendationProgressRequestId.value = requestId

  try {
    const response = await boardApi.recommendScenario({
      maxDevices: validateRecommendationCount(scenarioRecommendationFilters.maxDevices, t('app.maxDevicesField')),
      maxRules: validateRecommendationCount(scenarioRecommendationFilters.maxRules, t('app.maxRulesField')),
      maxSpecs: validateRecommendationCount(scenarioRecommendationFilters.maxSpecs, t('app.maxSpecsField')),
      language: locale.value,
      userRequirement: scenarioRecommendationFilters.userRequirement
    }, requestId, controller.signal)
    if (requestEpoch !== scenarioRecommendationRequestEpoch) return

    const rawScene = response.scene
    const scene = rawScene && Array.isArray(rawScene.devices) && rawScene.devices.length > 0
      ? normalizeSceneFile(rawScene)
      : null
    scenarioRecommendationResult.value = {
      message: localizedRecommendationText(
        response.message,
        t('app.recommendationsFound', { count: response.count })
      ),
      count: response.count,
      requestedCount: response.requestedCount,
      validatedCount: response.validatedCount,
      filteredCount: response.filteredCount,
      filteredItems: response.filteredItems,
      adjustedCount: response.adjustedCount,
      adjustedItems: response.adjustedItems,
      rawCandidateCount: response.rawCandidateCount,
      inspectedCount: response.inspectedCount,
      truncatedCount: response.truncatedCount,
      scenarioName: response.scenarioName,
      rationale: response.rationale,
      verificationReady: response.verificationReady,
      readinessIssues: response.readinessIssues,
      scene
    }
    scenarioRecommendationMessage.value = localizedRecommendationText(
      response.message,
      t('app.recommendationsFound', { count: response.count })
    )
  } catch (error: any) {
    if (requestEpoch !== scenarioRecommendationRequestEpoch) return
    if (error.name === 'CanceledError' || error.code === 'ERR_CANCELED') {
      return
    }
    console.error('Failed to fetch scenario recommendation:', error)
    ElMessage.error(extractRecommendationErrorMessage(error, t('app.failedToFetchScenarioRecommendation')))
  } finally {
    if (requestEpoch === scenarioRecommendationRequestEpoch) {
      isRecommendingScenario.value = false
      if (scenarioRecommendationAbortController.value === controller) {
        scenarioRecommendationAbortController.value = null
      }
      if (scenarioRecommendationRequestId.value === requestId) scenarioRecommendationRequestId.value = null
    }
  }
}

const closeScenarioRecommendationPanel = () => {
  scenarioRecommendationRequestEpoch += 1
  void stopActiveRecommendation(
    'scenario',
    scenarioRecommendationRequestId,
    scenarioRecommendationAbortController,
    running => { isRecommendingScenario.value = running },
    'app.scenarioRecommendationCancelled',
    { showMessage: false }
  )
  showScenarioRecommendationPanel.value = false
  resetScenarioRecommendationResults()
}

const applyRecommendedScenario = async () => {
  if (!ensurePlaybackClosedForMutation()) return
  const scene = recommendedScenarioScene.value
  if (!scene) {
    ElMessage.warning(t('app.noScenarioToApply'))
    return
  }
  const imported = await importScene(scene)
  if (imported) {
    closeScenarioRecommendationPanel()
  }
}

const exportRecommendedScenario = () => {
  const scene = recommendedScenarioScene.value
  if (!scene) {
    ElMessage.warning(t('app.noScenarioToApply'))
    return
  }
  const timestamp = new Date().toISOString().replace(/[:.]/g, '-')
  const portableScene = canonicalizeSceneFile(scene)
  downloadJsonFile(`iot-verify-ai-scenario-${timestamp}.json`, portableScene)
  ElMessage.success(t('app.sceneExportStarted', {
    devices: scene.devices.length,
    variables: scene.environmentVariables.length,
    rules: scene.rules.length,
    specs: scene.specs.length
  }))
}

const formatScenarioDeviceLabel = (deviceId: string): string => {
  const device = recommendedScenarioScene.value?.devices.find(candidate => candidate.id === deviceId)
  return device?.label || t('app.unknownModelItem')
}

const scenarioDeviceHasStateMachine = (device: DeviceNode): boolean => {
  const template = recommendedScenarioScene.value?.templates.find(candidate => {
    const candidateName = candidate.manifest?.Name || candidate.name
    return candidateName?.trim().toLocaleLowerCase() === device.templateName.trim().toLocaleLowerCase()
  })
  return Boolean(template?.manifest?.Modes?.length && template.manifest.WorkingStates?.length)
}

const formatScenarioRuleSource = (source: RuleForm['sources'][number]): string => {
  const device = formatScenarioDeviceLabel(source.fromId)
  if (source.itemType === 'api') return `${device}.${source.fromApi}`
  return `${device}.${source.fromApi} ${source.relation || '='} ${source.value ?? ''}`.trim()
}

const formatScenarioRuleAction = (rule: RuleForm): string => {
  const action = `${formatScenarioDeviceLabel(rule.toId)}.${rule.toApi}`
  if (!rule.contentDevice || !rule.content) return action
  return `${action} · ${t('app.copyFrom')} ${formatScenarioDeviceLabel(rule.contentDevice)}.${rule.content}`
}

const formatScenarioSpecFormula = (spec: Specification): string =>
  buildSpecFormula(spec, {
    nodes: recommendedScenarioScene.value?.devices || [],
    deviceTemplates: recommendedScenarioScene.value?.templates || []
  })

const recommendedSpecTemplateLabel = (templateId: unknown): string => {
  const id = String(templateId ?? '')
  const detail = specTemplateDetails.find(template => template.id === id)
  return detail?.labelKey ? t(detail.labelKey) : detail?.label || id || t('app.customSpecification')
}

// 应用规约推荐 - 将推荐的规约添加到画布
const applySpecRecommendation = async (recommendation: SpecificationRecommendation, index: number) => {
  if (!ensurePlaybackClosedForMutation()) return
  if (!ensureBoardDataReady(['nodes', 'templates', 'specs'])) return
  if (appliedSpecRecommendations.value.has(index)) {
    ElMessage.warning(t('app.recommendationAlreadyApplied'))
    return
  }
  if (applyingSpecRecommendations.value.has(index)) return
  const recommendationEpoch = specRecommendationRequestEpoch

  // Reject an invalid recommendation before issuing the targeted create request.
  const rawTemplateId = recommendation.templateId
  if (typeof rawTemplateId !== 'string' || !/^[1-7]$/.test(rawTemplateId)) {
    ElMessage.warning({
      message: t('app.invalidRecommendedTemplateId', { templateId: rawTemplateId ?? '' }),
      type: 'warning'
    })
    return
  }
  const templateId = rawTemplateId as SpecTemplateId
  const conditionIdPrefix = `rec_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`
  let aConditions: SpecCondition[]
  let ifConditions: SpecCondition[]
  let thenConditions: SpecCondition[]
  try {
    aConditions = materializeSpecificationRecommendationConditions(
      recommendation.aConditions, 'a', index => `${conditionIdPrefix}_a_${index}`)
    ifConditions = materializeSpecificationRecommendationConditions(
      recommendation.ifConditions, 'if', index => `${conditionIdPrefix}_if_${index}`)
    thenConditions = materializeSpecificationRecommendationConditions(
      recommendation.thenConditions, 'then', index => `${conditionIdPrefix}_then_${index}`)
  } catch (error) {
    const field = error instanceof RecommendationCandidateError ? error.field : t('app.unknownModelItem')
    ElMessage.warning(t('app.recommendationInvalidFieldNoChange', { field }))
    return
  }

  // 构建规约数据
  const templateLabel = recommendedSpecTemplateLabel(templateId)
  const newSpec = {
    id: 'spec_' + Date.now() + '_' + Math.random().toString(36).substr(2, 9),
    templateId,
    templateLabel,
    aConditions,
    ifConditions,
    thenConditions,
    devices: buildSpecDeviceRefsFromConditions([...aConditions, ...ifConditions, ...thenConditions]),
    formula: buildSpecFormula({
      templateId,
      templateLabel,
      aConditions,
      ifConditions,
      thenConditions
    }, {
      nodes: nodes.value,
      deviceTemplates: deviceTemplates.value
    })
  }

  if (specificationExists(newSpec)) {
    ElMessage.warning(t('app.specDuplicate'))
    return
  }

  // 获取现有规约
  applyingSpecRecommendations.value.add(index)
  try {
    await enqueueBoardMutation(async () => {
      try {
        const mutation = await boardApi.addSpec(newSpec)
        specifications.value = mutation.currentItems
        if (recommendationEpoch === specRecommendationRequestEpoch) {
          appliedSpecRecommendations.value.add(index)
        }
        ElMessage.success(t('app.specificationAddedSuccessfully'))
      } catch (error: any) {
        console.error('Failed to save specification:', error)
        if (!isDefinitiveMutationRejection(error)) {
          const refreshed = await refreshSpecifications()
          if (refreshed && specifications.value.some(spec => isSameSpecification(spec, newSpec))) {
            if (recommendationEpoch === specRecommendationRequestEpoch) {
              appliedSpecRecommendations.value.add(index)
            }
            ElMessage.warning(t('app.specCreateOutcomeRefreshed'))
            return
          }
        }
        ElMessage.error(extractApiErrorMessage(error, t('app.failedToSaveSpecification')))
      }
    })
  } finally {
    if (recommendationEpoch === specRecommendationRequestEpoch) {
      applyingSpecRecommendations.value.delete(index)
    }
  }
}

const recommendedDeviceLabel = (recommendation: DeviceRecommendation): string | null =>
  typeof recommendation?.suggestedLabel === 'string' && recommendation.suggestedLabel.trim()
    ? recommendation.suggestedLabel.trim()
    : null

type RecommendedDeviceRuntimeResult = {
  runtime?: DeviceRuntimeConfig
  error?: string
}

const buildRecommendedDeviceRuntime = (recommendation: DeviceRecommendation): RecommendedDeviceRuntimeResult => {
  const runtime: DeviceRuntimeConfig = {}
  const invalidField = (field: string): RecommendedDeviceRuntimeResult => ({
    error: t('app.deviceRecommendationInvalidRuntime', { field })
  })
  const hasField = (field: string) => Object.prototype.hasOwnProperty.call(recommendation || {}, field)

  let state = ''
  if (hasField('initialState')) {
    if (typeof recommendation.initialState !== 'string' || !recommendation.initialState.trim()) {
      return invalidField('initialState')
    }
    state = recommendation.initialState.trim()
  }
  if (state) {
    runtime.state = state
  }
  let trust = ''
  if (hasField('currentStateTrust')) {
    if (typeof recommendation.currentStateTrust !== 'string') return invalidField('currentStateTrust')
    trust = recommendation.currentStateTrust.trim()
    if (!TRUST_OPTIONS.includes(trust as any)) return invalidField('currentStateTrust')
  }
  if (trust) {
    runtime.currentStateTrust = trust as DeviceRuntimeConfig['currentStateTrust']
  }
  let statePrivacy = ''
  if (hasField('currentStatePrivacy')) {
    if (typeof recommendation.currentStatePrivacy !== 'string') return invalidField('currentStatePrivacy')
    statePrivacy = recommendation.currentStatePrivacy.trim()
    if (!PRIVACY_OPTIONS.includes(statePrivacy as any)) return invalidField('currentStatePrivacy')
  }
  if (statePrivacy) {
    runtime.currentStatePrivacy = statePrivacy as DeviceRuntimeConfig['currentStatePrivacy']
  }

  if (hasField('initialVariables') && !Array.isArray(recommendation.initialVariables)) {
    return invalidField('initialVariables')
  }
  const variables: NonNullable<DeviceRuntimeConfig['variables']> = []
  const variableNames = new Set<string>()
  for (const [index, variable] of (recommendation?.initialVariables || []).entries()) {
    if (!variable || typeof variable !== 'object' || Array.isArray(variable)) {
      return invalidField(`initialVariables[${index}]`)
    }
    if (typeof variable.name !== 'string' || typeof variable.value !== 'string') {
      return invalidField(`initialVariables[${index}]`)
    }
    const name = variable.name.trim()
    const value = variable.value.trim()
    if (!name || !value || variableNames.has(name)) return invalidField(`initialVariables[${index}]`)
    variableNames.add(name)
    let variableTrust = ''
    if (Object.prototype.hasOwnProperty.call(variable, 'trust')) {
      if (typeof variable.trust !== 'string') return invalidField(`initialVariables[${index}].trust`)
      variableTrust = variable.trust.trim()
      if (!TRUST_OPTIONS.includes(variableTrust as any)) return invalidField(`initialVariables[${index}].trust`)
    }
    variables.push({
      name,
      value,
      ...(variableTrust ? { trust: variableTrust as any } : {})
    })
  }
  if (variables.length) {
    runtime.variables = variables
  }

  if (hasField('initialPrivacies') && !Array.isArray(recommendation.initialPrivacies)) {
    return invalidField('initialPrivacies')
  }
  const privacies: NonNullable<DeviceRuntimeConfig['privacies']> = []
  const privacyNames = new Set<string>()
  for (const [index, privacy] of (recommendation?.initialPrivacies || []).entries()) {
    if (!privacy || typeof privacy !== 'object' || Array.isArray(privacy)) {
      return invalidField(`initialPrivacies[${index}]`)
    }
    if (typeof privacy.name !== 'string' || typeof privacy.privacy !== 'string') {
      return invalidField(`initialPrivacies[${index}]`)
    }
    const name = privacy.name.trim()
    const value = privacy.privacy.trim()
    if (!name || privacyNames.has(name) || !PRIVACY_OPTIONS.includes(value as any)) {
      return invalidField(`initialPrivacies[${index}]`)
    }
    privacyNames.add(name)
    privacies.push({ name, privacy: value as any })
  }
  if (privacies.length) {
    runtime.privacies = privacies
  }

  return { runtime: Object.keys(runtime).length > 0 ? runtime : undefined }
}

// 应用设备推荐 - 将推荐的设备添加到画布
const applyDeviceRecommendation = async (recommendation: DeviceRecommendation, index: number) => {
  if (!ensurePlaybackClosedForMutation()) return
  if (appliedDeviceRecommendations.value.has(index)) {
    ElMessage.warning(t('app.recommendationAlreadyApplied'))
    return
  }
  if (applyingDeviceRecommendations.value.has(index)) return
  const recommendationEpoch = deviceRecommendationRequestEpoch

  const templateName = typeof recommendation.templateName === 'string'
    ? recommendation.templateName.trim()
    : ''
  if (!templateName) {
    ElMessage.error(t('app.recommendationInvalidFieldNoChange', { field: 'templateName' }))
    return
  }

  const template = findTemplateByAnyName(templateName)
  
  if (!template) {
    ElMessage.error(t('app.templateNotFoundWithName', { name: templateName }))
    return
  }
  
  const center = getVisibleCanvasCenterWorld()
  if (!center) return

  const label = recommendedDeviceLabel(recommendation)
  if (!label) {
    ElMessage.error(t('app.recommendationInvalidFieldNoChange', { field: 'suggestedLabel' }))
    return
  }
  const runtimeResult = buildRecommendedDeviceRuntime(recommendation)
  if (runtimeResult.error) {
    ElMessage.warning(runtimeResult.error)
    return
  }
  const runtime = runtimeResult.runtime
  const runtimeError = validateDeviceRuntimeConfig(template, runtime, t, { variableScope: 'local' })
  if (runtimeError) {
    ElMessage.warning(runtimeError)
    return
  }
  const availableLabel = getUniqueLabel(label, getVisibleDeviceNodes())
  let confirmedLabel = label
  if (availableLabel !== label) {
    try {
      await ElMessageBox.confirm(
        t('app.deviceRecommendationNameConflictConfirm', { from: label, to: availableLabel }),
        t('app.deviceRecommendationNameConflictTitle'),
        {
          type: 'warning',
          confirmButtonText: t('app.confirm'),
          cancelButtonText: t('app.cancel'),
          appendTo: 'body',
          lockScroll: false
        }
      )
      confirmedLabel = availableLabel
    } catch (error: any) {
      if (error !== 'cancel' && error !== 'close') {
        console.error('Recommended device name confirmation failed:', error)
      }
      return
    }
  }
  
  // createDeviceInstanceAt 内部已保存并在失败时回滚+抛错，这里只需处理成功/失败提示。
  applyingDeviceRecommendations.value.add(index)
  try {
    const outcome = await createDeviceInstanceAt(template, center, confirmedLabel, runtime)
    if (recommendationEpoch === deviceRecommendationRequestEpoch) {
      appliedDeviceRecommendations.value.add(index)
    }
    if (outcome.responseConfirmed) {
      ElMessage.success(t('app.deviceAddedWithName', { name: outcome.device.label }))
    }
  } catch {
    // createDeviceInstanceAt already displayed the server failure.
  } finally {
    if (recommendationEpoch === deviceRecommendationRequestEpoch) {
      applyingDeviceRecommendations.value.delete(index)
    }
  }
}

// ==== Simulation Logic ====
const isSimulating = ref(false)
const simulationResult = ref<any>(null)
const simulationError = ref<string | null>(null)
// Result of the last successful simulation, kept so its logs / raw NuSMV output stay reachable while
// the timeline is open. The result dialog only auto-opens on error; on success we go straight to the
// timeline (by design) and let the user open the logs on demand via openSimulationLogs().
const lastSimulationResult = ref<any>(null)

// Simulation form state (moved from ControlCenter)
const simulationForm = reactive({
  steps: 10,
  isAttack: false,
  attackBudget: 1,
  enablePrivacy: false,
  isAsync: true,
  saveToHistory: true
})

const SIMULATION_STEPS_MIN = 1
const SIMULATION_STEPS_MAX = 100

const normalizeSimulationStepsControlValue = (value: unknown): number => {
  const numeric = typeof value === 'number' ? value : Number(value)
  if (!Number.isFinite(numeric)) return 10
  return Math.min(SIMULATION_STEPS_MAX, Math.max(SIMULATION_STEPS_MIN, Math.round(numeric)))
}

const setSimulationSteps = (value: unknown) => {
  simulationForm.steps = normalizeSimulationStepsControlValue(value)
}

const adjustSimulationSteps = (delta: number) => {
  setSimulationSteps(normalizeSimulationStepsControlValue(simulationForm.steps) + delta)
}

const commitSimulationStepsInput = (event: Event) => {
  const input = event.currentTarget as HTMLInputElement
  setSimulationSteps(input.value)
  input.value = String(simulationForm.steps)
}

// Verification form state (similar to simulation)
const verificationForm = reactive({
  isAttack: false,
  attackBudget: 1,
  enablePrivacy: false,
  isAsync: true
})

// The bounded counterexample explorer is intentionally background-only. The first-level controls describe the
// search budget; population/seed remain advanced inputs so the formal run controls
// stay visually distinct from heuristic exploration.
const fuzzingForm = reactive<{
  explorationMode: FuzzingExplorationMode
  targetSelectionMode: 'ALL' | 'EXPLICIT'
  targetSpecIds: string[]
  maxIterations: number
  pathLength: number
  populationSize: number
  seed: number | null
}>({
  explorationMode: 'BOARD_SNAPSHOT',
  targetSelectionMode: 'ALL',
  targetSpecIds: [],
  maxIterations: 500,
  pathLength: 20,
  populationSize: 10,
  seed: null
})
const fuzzingWatchedTask = ref<FuzzingTaskSummary | null>(null)

const knownFuzzEligibleSpecifications = computed(() =>
  specifications.value.filter(isKnownFuzzingSpecificationSupported))

const normalizedFuzzTargetSpecIds = computed(() => {
  const eligibleIds = new Set(knownFuzzEligibleSpecifications.value.map(spec => spec.id))
  return fuzzingForm.targetSpecIds.filter(id => eligibleIds.has(id))
})

const invalidFuzzTargetSpecIds = computed(() => {
  const eligibleIds = new Set(knownFuzzEligibleSpecifications.value.map(spec => spec.id))
  return fuzzingForm.targetSelectionMode === 'EXPLICIT'
    ? fuzzingForm.targetSpecIds.filter(id => !eligibleIds.has(id))
    : []
})

const availableFuzzTargetCount = computed(() => knownFuzzEligibleSpecifications.value.length)
const fuzzingPreviewPrerequisitesReady = computed(() =>
  isBoardDataReady.value
  && nodes.value.length > 0
  && availableFuzzTargetCount.value > 0)

const fuzzingContentCommandUnsupported = computed(() => rules.value.some(rule =>
  Boolean(rule.contentDevice?.trim()) || Boolean(rule.content?.trim())
))

const fuzzingLocalConfigurationError = computed(() => {
  if (invalidFuzzTargetSpecIds.value.length > 0) {
    return t('app.fuzzTargetSelectionChanged', { count: invalidFuzzTargetSpecIds.value.length })
  }
  const issue = getFuzzingConfigurationIssue({
    ...fuzzingForm,
    targetSpecIds: normalizedFuzzTargetSpecIds.value
  }, availableFuzzTargetCount.value)
  if (!issue) return ''
  if (issue.code === 'INVALID_INTEGER_FIELD') {
    const labels = {
      maxIterations: t('app.fuzzMaxIterations'),
      pathLength: t('app.fuzzPathLength'),
      populationSize: t('app.fuzzPopulationSize'),
      seed: t('app.fuzzSeed')
    }
    return t('app.fuzzIntegerFieldRange', {
      field: labels[issue.field],
      minimum: issue.minimum.toLocaleString(),
      maximum: issue.maximum.toLocaleString()
    })
  }
  if (issue.code === 'TARGET_SELECTION_REQUIRED') {
    return t('app.fuzzTargetSelectionRequired', {
      count: issue.availableSpecCount,
      limit: issue.limit
    })
  }
  if (issue.code === 'TOO_MANY_TARGETS') {
    return t('app.fuzzTooManyTargetSpecifications', { limit: issue.limit })
  }
  return ''
})

const ATTACK_BUDGET_HARD_MAX = 50
const boardAttackSurface = computed(() => analyzeBoardAttackSurface(
  nodes.value,
  rules.value,
  resolveTemplateForNode
))
const attackBudgetMax = computed(() => Math.min(
  ATTACK_BUDGET_HARD_MAX,
  boardAttackSurface.value.totalPointCount
))
const attackSurfacePointCount = computed(() => boardAttackSurface.value.totalPointCount)
const attackBudgetIsCapped = computed(() => attackSurfacePointCount.value > ATTACK_BUDGET_HARD_MAX)

const hasModeledAttackEffect = computed(() => boardAttackSurface.value.totalPointCount > 0)

const attackConfigurationError = (enabled: boolean, budget: unknown): string => {
  const issue = getAttackSelectionIssue(enabled, budget, attackBudgetMax.value)
  if (issue === 'NO_MODELED_EFFECT') return t('app.attackNoModeledEffect')
  if (issue === 'INVALID_BUDGET') {
    return t('app.attackBudgetSelectionInvalid', {
      selected: String(budget),
      limit: attackBudgetMax.value
    })
  }
  return ''
}

const verificationAttackConfigurationError = computed(() =>
  attackConfigurationError(verificationForm.isAttack, verificationForm.attackBudget))
const simulationAttackConfigurationError = computed(() =>
  attackConfigurationError(simulationForm.isAttack, simulationForm.attackBudget))

const boardRunBlockedReason = computed(() => {
  if (isSceneReplacementInProgress.value) return t('app.sceneReplacementInProgress')
  if (failedBoardDataKeys.value.length > 0) return t('app.boardDataLoadFailed')
  if (!isBoardDataReady.value) return t('app.loading')
  return ''
})
const verificationRunBlockedReason = computed(() =>
  boardRunBlockedReason.value || verificationAttackConfigurationError.value)
const simulationRunBlockedReason = computed(() =>
  boardRunBlockedReason.value || simulationAttackConfigurationError.value)

const hasPrivacySpecification = computed(() => specifications.value.some(spec =>
  [spec.aConditions, spec.ifConditions, spec.thenConditions]
    .some(conditions => (conditions || []).some(condition => condition.targetType === 'privacy'))
))

watch(hasPrivacySpecification, required => {
  if (required) verificationForm.enablePrivacy = true
}, { immediate: true })

const validateAttackBudget = (value: unknown) => {
  const issue = getAttackSelectionIssue(true, value, attackBudgetMax.value)
  if (issue === 'NO_MODELED_EFFECT') throw new Error(t('app.attackNoModeledEffect'))
  if (issue === 'INVALID_BUDGET') {
    throw new Error(t('app.attackBudgetSelectionInvalid', {
      selected: String(value),
      limit: attackBudgetMax.value
    }))
  }
  return value as number
}

const validateSimulationSteps = (value: unknown) =>
  requireIntegerInRange(value, t('app.simulationSteps'), 1, 100)

// 异步验证任务状态
const asyncVerificationTask = ref<{
  taskId: number | null
  progress: number
  status: string
}>({
  taskId: null,
  progress: 0,
  status: t('app.taskInitializing')
})
const asyncVerificationActive = ref(false)
const cancellingVerificationTask = ref(false)
const verificationCancelRequested = ref(false)

const asyncFuzzingTask = ref<{
  taskId: number | null
  progress: number
  status: string
}>({
  taskId: null,
  progress: 0,
  status: t('app.taskInitializing')
})
const isFuzzing = ref(false)
const asyncFuzzingActive = ref(false)
const cancellingFuzzingTask = ref(false)
const fuzzingCancelRequested = ref(false)
const showFuzzingPanel = ref(false)
const showFuzzingResultDialog = ref(false)
const fuzzingResult = ref<FuzzingRun | null>(null)
const fuzzingError = ref<string | null>(null)
const fuzzingSettingsNotice = ref<string | null>(null)
const fuzzingResultLoading = ref(false)
const activeFuzzingFinding = ref<FuzzingFinding | null>(null)
let fuzzingResultRequestEpoch = 0
const fuzzingWorkloadPreview = ref<FuzzWorkloadPreview | null>(null)
const fuzzingWorkloadPreviewLoading = ref(false)
const fuzzingWorkloadPreviewError = ref<string | null>(null)
const fuzzingWorkloadPreviewSemanticKey = ref<string | null>(null)
let fuzzingWorkloadPreviewEpoch = 0
let fuzzingWorkloadPreviewTimer: ReturnType<typeof setTimeout> | null = null
const paperDomainPreview = ref<FuzzPaperDomainPreview | null>(null)
const paperDomainPreviewLoading = ref(false)
const paperDomainPreviewError = ref<string | null>(null)
const paperDomainPreviewSemanticKey = ref<string | null>(null)
const paperDomainStaleRecoveryActive = ref(false)
let paperDomainPreviewEpoch = 0
let paperDomainPreviewTimer: ReturnType<typeof setTimeout> | null = null

const paperDomainSemanticKey = computed(() => JSON.stringify({
  deviceTemplates: deviceTemplates.value,
  devices: nodes.value.map(device => ({
    id: device.id,
    templateName: device.templateName,
    label: device.label,
    state: device.state,
    currentStateTrust: device.currentStateTrust,
    currentStatePrivacy: device.currentStatePrivacy,
    variables: device.variables,
    privacies: device.privacies
  })),
  environmentVariables: environmentVariables.value,
  rules: rules.value,
  specifications: specifications.value
}))

const fuzzingWorkloadSemanticKey = computed(() => JSON.stringify({
  board: paperDomainSemanticKey.value,
  maxIterations: fuzzingForm.maxIterations,
  pathLength: fuzzingForm.pathLength,
  populationSize: fuzzingForm.populationSize
}))

const validFuzzingBudgetFields = () => [
  [fuzzingForm.maxIterations, FUZZ_ITERATIONS_MIN, FUZZ_ITERATIONS_MAX],
  [fuzzingForm.pathLength, FUZZ_PATH_LENGTH_MIN, FUZZ_PATH_LENGTH_MAX],
  [fuzzingForm.populationSize, FUZZ_POPULATION_MIN, FUZZ_POPULATION_MAX]
].every(([value, minimum, maximum]) => Number.isInteger(value)
  && value >= minimum
  && value <= maximum)

const fuzzingWorkloadReady = computed(() => {
  const preview = fuzzingWorkloadPreview.value
  return !!preview
    && !fuzzingWorkloadPreviewLoading.value
    && !fuzzingWorkloadPreviewError.value
    && fuzzingWorkloadPreviewSemanticKey.value === fuzzingWorkloadSemanticKey.value
    && preview.maxIterations === fuzzingForm.maxIterations
    && preview.pathLength === fuzzingForm.pathLength
    && preview.populationSize === fuzzingForm.populationSize
})

const fuzzingWorkload = computed(() => fuzzingWorkloadReady.value
  ? fuzzingWorkloadPreview.value?.estimatedWorkload
  : undefined)

const fuzzingWorkloadLimit = computed(() => fuzzingWorkloadReady.value
  ? fuzzingWorkloadPreview.value?.workloadLimit
  : undefined)

const validPaperPathLength = () => Number.isInteger(fuzzingForm.pathLength)
  && fuzzingForm.pathLength >= 1
  && fuzzingForm.pathLength <= FUZZ_PATH_LENGTH_MAX

const invalidatePaperDomainPreview = (clearError = true) => {
  if (paperDomainPreviewTimer) {
    clearTimeout(paperDomainPreviewTimer)
    paperDomainPreviewTimer = null
  }
  paperDomainPreviewEpoch += 1
  paperDomainPreview.value = null
  paperDomainPreviewSemanticKey.value = null
  paperDomainPreviewLoading.value = false
  if (clearError) paperDomainPreviewError.value = null
}

const paperDomainReady = computed(() => {
  if (fuzzingForm.explorationMode !== 'PAPER_COMPATIBLE') return true
  const preview = paperDomainPreview.value
  return !!preview
    && !paperDomainPreviewLoading.value
    && !paperDomainPreviewError.value
    && preview.pathLength === fuzzingForm.pathLength
    && paperDomainPreviewSemanticKey.value === paperDomainSemanticKey.value
    && isValidFuzzPaperDomainFingerprint(preview.modelFingerprint)
})

const paperDomainConfigurationError = computed(() =>
  fuzzingForm.explorationMode === 'PAPER_COMPATIBLE'
    && fuzzingPreviewPrerequisitesReady.value
    && !paperDomainReady.value
    ? t('app.fuzzPaperDomainRequired')
    : '')

const fuzzingWorkloadConfigurationError = computed(() => {
  const preview = fuzzingWorkloadReady.value ? fuzzingWorkloadPreview.value : null
  if (!preview?.accepted) {
    if (!preview) return ''
    return t('app.fuzzWorkloadExceeded', {
      workload: preview.estimatedWorkload.toLocaleString(),
      limit: preview.workloadLimit.toLocaleString()
    })
  }
  return ''
})

const effectiveFuzzingConfigurationError = computed(() =>
  fuzzingLocalConfigurationError.value
  || fuzzingWorkloadConfigurationError.value
  || paperDomainConfigurationError.value)

const refreshPaperDomainPreview = async () => {
  if (paperDomainPreviewTimer) {
    clearTimeout(paperDomainPreviewTimer)
    paperDomainPreviewTimer = null
  }
  if (fuzzingForm.explorationMode !== 'PAPER_COMPATIBLE'
    || !validPaperPathLength()
    || !fuzzingPreviewPrerequisitesReady.value) {
    invalidatePaperDomainPreview()
    return
  }
  const requestedPathLength = fuzzingForm.pathLength
  const requestedSemanticKey = paperDomainSemanticKey.value
  const requestEpoch = ++paperDomainPreviewEpoch
  paperDomainPreview.value = null
  paperDomainPreviewSemanticKey.value = null
  paperDomainPreviewLoading.value = true
  paperDomainPreviewError.value = null
  try {
    const preview = await fuzzingApi.previewPaperDomain(requestedPathLength)
    if (requestEpoch !== paperDomainPreviewEpoch
      || fuzzingForm.explorationMode !== 'PAPER_COMPATIBLE'
      || fuzzingForm.pathLength !== requestedPathLength
      || paperDomainSemanticKey.value !== requestedSemanticKey) return
    paperDomainPreview.value = preview
    paperDomainPreviewSemanticKey.value = requestedSemanticKey
    if (paperDomainStaleRecoveryActive.value) {
      paperDomainStaleRecoveryActive.value = false
      fuzzingError.value = null
    }
  } catch (error: any) {
    if (requestEpoch !== paperDomainPreviewEpoch) return
    paperDomainPreview.value = null
    paperDomainPreviewSemanticKey.value = null
    paperDomainPreviewError.value = extractApiErrorMessage(
      error,
      t('app.fuzzPaperDomainPreviewFailed')
    )
  } finally {
    if (requestEpoch === paperDomainPreviewEpoch) paperDomainPreviewLoading.value = false
  }
}

const schedulePaperDomainPreview = () => {
  if (paperDomainPreviewTimer) clearTimeout(paperDomainPreviewTimer)
  paperDomainPreviewTimer = setTimeout(() => {
    paperDomainPreviewTimer = null
    void refreshPaperDomainPreview()
  }, 250)
}

const invalidateFuzzingWorkloadPreview = (clearError = true) => {
  if (fuzzingWorkloadPreviewTimer) {
    clearTimeout(fuzzingWorkloadPreviewTimer)
    fuzzingWorkloadPreviewTimer = null
  }
  fuzzingWorkloadPreviewEpoch += 1
  fuzzingWorkloadPreview.value = null
  fuzzingWorkloadPreviewSemanticKey.value = null
  fuzzingWorkloadPreviewLoading.value = false
  if (clearError) fuzzingWorkloadPreviewError.value = null
}

const refreshFuzzingWorkloadPreview = async () => {
  if (fuzzingWorkloadPreviewTimer) {
    clearTimeout(fuzzingWorkloadPreviewTimer)
    fuzzingWorkloadPreviewTimer = null
  }
  if (!showFuzzingPanel.value
    || !validFuzzingBudgetFields()
    || !fuzzingPreviewPrerequisitesReady.value) {
    invalidateFuzzingWorkloadPreview()
    return
  }
  const request = {
    maxIterations: fuzzingForm.maxIterations,
    pathLength: fuzzingForm.pathLength,
    populationSize: fuzzingForm.populationSize
  }
  const requestedSemanticKey = fuzzingWorkloadSemanticKey.value
  const requestEpoch = ++fuzzingWorkloadPreviewEpoch
  fuzzingWorkloadPreview.value = null
  fuzzingWorkloadPreviewSemanticKey.value = null
  fuzzingWorkloadPreviewLoading.value = true
  fuzzingWorkloadPreviewError.value = null
  try {
    const preview = await fuzzingApi.previewWorkload(request)
    if (requestEpoch !== fuzzingWorkloadPreviewEpoch
      || fuzzingWorkloadSemanticKey.value !== requestedSemanticKey) return
    fuzzingWorkloadPreview.value = preview
    fuzzingWorkloadPreviewSemanticKey.value = requestedSemanticKey
  } catch (error: any) {
    if (requestEpoch !== fuzzingWorkloadPreviewEpoch) return
    fuzzingWorkloadPreview.value = null
    fuzzingWorkloadPreviewSemanticKey.value = null
    fuzzingWorkloadPreviewError.value = extractApiErrorMessage(
      error,
      t('app.fuzzWorkloadPreviewFailed')
    )
  } finally {
    if (requestEpoch === fuzzingWorkloadPreviewEpoch) {
      fuzzingWorkloadPreviewLoading.value = false
    }
  }
}

const scheduleFuzzingWorkloadPreview = () => {
  if (fuzzingWorkloadPreviewTimer) clearTimeout(fuzzingWorkloadPreviewTimer)
  fuzzingWorkloadPreviewTimer = setTimeout(() => {
    fuzzingWorkloadPreviewTimer = null
    void refreshFuzzingWorkloadPreview()
  }, 250)
}

watch(
  [
    showFuzzingPanel,
    () => fuzzingForm.explorationMode,
    () => fuzzingForm.pathLength,
    paperDomainSemanticKey,
    fuzzingPreviewPrerequisitesReady
  ],
  ([visible, mode]) => {
    invalidatePaperDomainPreview()
    if (mode !== 'PAPER_COMPATIBLE' && paperDomainStaleRecoveryActive.value) {
      paperDomainStaleRecoveryActive.value = false
      fuzzingError.value = null
    }
    if (visible
      && mode === 'PAPER_COMPATIBLE'
      && validPaperPathLength()
      && fuzzingPreviewPrerequisitesReady.value) {
      schedulePaperDomainPreview()
    }
  },
  { flush: 'sync' }
)

watch(
  [showFuzzingPanel, fuzzingWorkloadSemanticKey, fuzzingPreviewPrerequisitesReady],
  ([visible]) => {
    invalidateFuzzingWorkloadPreview()
    if (visible && validFuzzingBudgetFields() && fuzzingPreviewPrerequisitesReady.value) {
      scheduleFuzzingWorkloadPreview()
    }
  },
  { flush: 'sync' }
)

onBeforeUnmount(() => {
  invalidatePaperDomainPreview()
  invalidateFuzzingWorkloadPreview()
  taskInboxRequests.invalidate()
  verificationHistoryRequests.invalidate()
  simulationHistoryRequests.invalidate()
  fuzzingHistoryRequests.invalidate()
  historyDetailRequests.invalidate()
})

const currentFuzzingModelFingerprint = ref<string | null>(null)

const refreshCurrentFuzzingModelFingerprint = async (): Promise<string | null> => {
  try {
    const fingerprint = await fuzzingApi.getCurrentModelFingerprint()
    if (!boardLifecycleDisposed) currentFuzzingModelFingerprint.value = fingerprint
    return fingerprint
  } catch {
    if (!boardLifecycleDisposed) currentFuzzingModelFingerprint.value = null
    return null
  }
}

const currentFuzzingBoardScope = computed(() => ({
  deviceCount: nodes.value.length,
  ruleCount: rules.value.length,
  specificationCount: specifications.value.length,
  environmentVariableCount: environmentVariables.value.length,
  deviceTemplateCount: new Set(nodes.value
    .map(device => device.templateName?.trim())
    .filter((name): name is string => Boolean(name))).size,
  modelFingerprint: currentFuzzingModelFingerprint.value
}))

const fuzzRunHasBoardDrift = (run: AvailableFuzzingRunSummary | FuzzingRun): boolean => {
  const snapshot = run.modelSnapshot
  const current = currentFuzzingBoardScope.value
  if (snapshot.modelFingerprint && current.modelFingerprint) {
    return snapshot.modelFingerprint !== current.modelFingerprint
  }
  if (snapshot.modelFingerprint && !current.modelFingerprint) {
    return true
  }
  return snapshot.deviceCount !== current.deviceCount
    || snapshot.ruleCount !== current.ruleCount
    || snapshot.specificationCount !== current.specificationCount
    || snapshot.environmentVariableCount !== current.environmentVariableCount
    || snapshot.deviceTemplateCount !== current.deviceTemplateCount
}

const fuzzingResultBoardDrifted = computed(() => {
  const run = fuzzingResult.value
  return run ? fuzzRunHasBoardDrift(run) : false
})

type HistoryLayer = 'tasks' | 'results'
type HistoryResultFilter = 'all' | 'verification' | 'fuzzing' | 'simulation'
type HistoryResultSource = Exclude<HistoryResultFilter, 'all'>

const verificationTasks = ref<VerificationTaskSummary[]>([])
const fuzzingTasks = ref<FuzzingTaskSummary[]>([])
const simulationTasks = ref<SimulationTaskSummary[]>([])
const verificationRuns = ref<VerificationRunSummary[]>([])
const fuzzingRuns = ref<FuzzingRunSummary[]>([])
const simulationRuns = ref<SimulationTraceSummary[]>([])
const FUZZ_TASK_INBOX_PAGE_SIZE = 100
const FUZZ_RUN_HISTORY_PAGE_SIZE = 25
const fuzzingRunsPage = ref(0)
const fuzzingRunsHasMore = ref(false)
const loadingMoreFuzzingRuns = ref(false)
const taskInboxRequests = createPagedRequestCoordinator()
const verificationHistoryRequests = createPagedRequestCoordinator()
const simulationHistoryRequests = createPagedRequestCoordinator()
const fuzzingHistoryRequests = createPagedRequestCoordinator()
const historyDetailRequests = createPagedRequestCoordinator()
let historyPanelIntentEpoch = 0
let fuzzingHistoryAppendPromise: Promise<boolean> | null = null
const showHistoryPanel = ref(false)
const activeHistoryLayer = ref<HistoryLayer>('tasks')
const activeHistoryResultFilter = ref<HistoryResultFilter>('all')
const loadingTaskHistory = ref(false)
const loadingResultHistory = ref(false)
const pendingTaskActionKeys = ref<Set<string>>(new Set())
const historyResultErrors = reactive<Record<HistoryResultSource, string | null>>({
  verification: null,
  fuzzing: null,
  simulation: null
})
let taskInboxRefreshTimer: ReturnType<typeof setInterval> | null = null
let taskInboxBackgroundRefreshPromise: Promise<boolean> | null = null
let taskInboxLoadingEpoch = 0
let historyResultsLoadingEpoch = 0
const fuzzRunRecoveryAttempts = new Map<number, number>()
const fuzzRunRecoveryNextAttemptAt = new Map<number, number>()
const fuzzRunRecoveryRequests = new Map<number, Promise<FuzzingRun>>()

const historyActionLocked = computed(() =>
  traceAnimationState.value.visible ||
  simulationAnimationState.value.visible ||
  isAnimationLocked.value
)

const isCurrentHistoryPanelIntent = (
  epoch: number,
  layer: HistoryLayer,
  filter?: HistoryResultFilter
) => !boardLifecycleDisposed
  && epoch === historyPanelIntentEpoch
  && showHistoryPanel.value
  && activeHistoryLayer.value === layer
  && (filter === undefined || activeHistoryResultFilter.value === filter)

const taskActionKey = (
  action: 'cancel' | 'dismiss',
  kind: 'verification' | 'fuzzing' | 'simulation',
  taskId: number
) => `${action}:${kind}:${taskId}`

const withTaskActionLock = async (
  key: string,
  action: () => Promise<void>
): Promise<void> => {
  if (pendingTaskActionKeys.value.has(key)) return
  pendingTaskActionKeys.value = new Set(pendingTaskActionKeys.value).add(key)
  try {
    await action()
  } finally {
    const next = new Set(pendingTaskActionKeys.value)
    next.delete(key)
    pendingTaskActionKeys.value = next
  }
}

const isActiveTaskStatus = (status?: string) => status === 'PENDING' || status === 'RUNNING'

const normalizeTaskProgress = (value?: number | null, fallback = 0): number => {
  const numeric = typeof value === 'number' ? value : fallback
  if (!Number.isFinite(numeric)) return fallback
  return Math.min(100, Math.max(0, Math.round(numeric)))
}

const taskSummaryTimestamp = (value?: string) => {
  if (!value) return 0
  const parsed = new Date(value).getTime()
  return Number.isNaN(parsed) ? 0 : parsed
}

const fuzzNotificationStorageKey = () =>
  fuzzNotificationStorageKeyForUser(currentUser.value?.userId)

const persistFuzzNotificationState = () => {
  try {
    localStorage.setItem(fuzzNotificationStorageKey(), JSON.stringify({
      unread: unreadFuzzNotifications.value.slice(0, 100),
      trackedTaskIds: trackedFuzzTaskIds.value.slice(0, 100)
    }))
  } catch {
    // Notification persistence is best-effort; task/run history remains authoritative.
  }
}

const clearFuzzRunRecoveryState = (taskId: number) => {
  fuzzRunRecoveryAttempts.delete(taskId)
  fuzzRunRecoveryNextAttemptAt.delete(taskId)
}

const scheduleFuzzRunRecovery = (taskId: number): number => {
  const attempt = fuzzRunRecoveryAttempts.get(taskId) ?? 0
  const delay = fuzzRunRetryDelayMs(attempt)
  fuzzRunRecoveryAttempts.set(taskId, attempt + 1)
  fuzzRunRecoveryNextAttemptAt.set(taskId, Date.now() + delay)
  return delay
}

const canAttemptFuzzRunRecovery = (taskId: number) =>
  Date.now() >= (fuzzRunRecoveryNextAttemptAt.get(taskId) ?? 0)

const loadFuzzRunSingleFlight = (taskId: number, runId = taskId): Promise<FuzzingRun> => {
  const existing = fuzzRunRecoveryRequests.get(taskId)
  if (existing) return existing
  const request = fuzzingApi.getRun(runId)
  fuzzRunRecoveryRequests.set(taskId, request)
  void request.finally(() => {
    if (fuzzRunRecoveryRequests.get(taskId) === request) {
      fuzzRunRecoveryRequests.delete(taskId)
    }
  }).catch(() => undefined)
  return request
}

const hydrateFuzzNotificationState = () => {
  try {
    const parsed = JSON.parse(localStorage.getItem(fuzzNotificationStorageKey()) || '{}')
    const unread = Array.isArray(parsed.unread) ? parsed.unread : []
    unreadFuzzNotifications.value = unread.filter((item: any) =>
      Number.isSafeInteger(item?.taskId)
      && item.taskId > 0
      && (item.kind === 'COMPLETED' || item.kind === 'FAILED' || item.kind === 'UNAVAILABLE')
      && typeof item.createdAt === 'string').slice(0, 100)
    trackedFuzzTaskIds.value = (Array.isArray(parsed.trackedTaskIds) ? parsed.trackedTaskIds : [])
      .filter((id: unknown) => Number.isSafeInteger(id) && Number(id) > 0)
      .map(Number)
      .filter((id: number, index: number, values: number[]) => values.indexOf(id) === index)
      .slice(0, 100)
  } catch {
    unreadFuzzNotifications.value = []
    trackedFuzzTaskIds.value = []
  }
}

const trackFuzzTask = (taskId: number) => {
  if (!trackedFuzzTaskIds.value.includes(taskId)) {
    clearFuzzRunRecoveryState(taskId)
    trackedFuzzTaskIds.value = [taskId, ...trackedFuzzTaskIds.value].slice(0, 100)
    persistFuzzNotificationState()
  }
}

const untrackFuzzTask = (taskId: number) => {
  clearFuzzRunRecoveryState(taskId)
  if (!trackedFuzzTaskIds.value.includes(taskId)) return
  trackedFuzzTaskIds.value = trackedFuzzTaskIds.value.filter(id => id !== taskId)
  persistFuzzNotificationState()
}

const markFuzzNotificationUnread = (notification: FuzzUnreadNotification): boolean => {
  if (notification.kind === 'COMPLETED'
    && notification.runId
    && showFuzzingResultDialog.value
    && fuzzingResult.value?.id === notification.runId) {
    unreadFuzzNotifications.value = unreadFuzzNotifications.value
      .filter(item => item.taskId !== notification.taskId)
    untrackFuzzTask(notification.taskId)
    persistFuzzNotificationState()
    return false
  }
  unreadFuzzNotifications.value = [
    notification,
    ...unreadFuzzNotifications.value.filter(item => item.taskId !== notification.taskId)
  ].slice(0, 100)
  untrackFuzzTask(notification.taskId)
  persistFuzzNotificationState()
  return true
}

const clearFuzzNotifications = (kind?: FuzzUnreadNotification['kind'], taskId?: number) => {
  unreadFuzzNotifications.value = unreadFuzzNotifications.value.filter(item => {
    if (taskId !== undefined && item.taskId !== taskId && item.runId !== taskId) return true
    if (kind && item.kind !== kind) return true
    return false
  })
  persistFuzzNotificationState()
}

const clearVisibleFuzzResultNotifications = () => {
  const visibleRunIds = new Set(fuzzingRuns.value.map(run => run.id))
  unreadFuzzNotifications.value = unreadFuzzNotifications.value.filter(notification =>
    !(['COMPLETED', 'UNAVAILABLE'].includes(notification.kind)
      && visibleRunIds.has(notification.runId ?? notification.taskId)))
  persistFuzzNotificationState()
}

const withUnreadFuzzUnavailablePlaceholders = (runs: FuzzingRunSummary[]): FuzzingRunSummary[] => {
  const knownIds = new Set(runs.map(run => run.id))
  const placeholders: FuzzingRunSummary[] = unreadFuzzNotifications.value
    .filter(notification => notification.kind === 'UNAVAILABLE' && !knownIds.has(notification.taskId))
    .map(notification => ({
      id: notification.taskId,
      createdAt: notification.createdAt,
      completedAt: notification.createdAt,
      findingCount: 0,
      findings: [],
      dataAvailable: false,
      unavailableReasonCode: 'RESULT_UNAVAILABLE'
    }))
  return [...placeholders, ...runs]
}

const mergeTaskSummariesPreservingExcluded = <T extends { id?: number; createdAt?: string }>(
  current: T[],
  incoming: T[],
  excludedIds: number[]
): T[] => {
  if (excludedIds.length === 0) return incoming
  const excluded = new Set(excludedIds)
  const preserved = current.filter(task => task.id !== undefined && excluded.has(task.id))
  const merged = [
    ...preserved,
    ...incoming.filter(task => task.id === undefined || !excluded.has(task.id))
  ]
  return merged.sort((a, b) => taskSummaryTimestamp(b.createdAt) - taskSummaryTimestamp(a.createdAt))
}

const watchedVerificationTaskIds = computed(() => {
  const taskId = asyncVerificationTask.value.taskId
  return isVerifying.value && asyncVerificationActive.value && taskId ? [taskId] : []
})

const watchedSimulationTaskIds = computed(() => {
  const taskId = asyncSimulationTask.value.taskId
  return isSimulating.value && asyncSimulationActive.value && taskId ? [taskId] : []
})

const watchedFuzzingTaskIds = computed(() => {
  const taskId = asyncFuzzingTask.value.taskId
  return isFuzzing.value && asyncFuzzingActive.value && taskId ? [taskId] : []
})

const activeVerificationTasks = computed(() =>
  verificationTasks.value.filter(task => isActiveTaskStatus(task.status))
)

const activeSimulationTasks = computed(() =>
  simulationTasks.value.filter(task => isActiveTaskStatus(task.status))
)

const activeFuzzingTasks = computed(() =>
  fuzzingTasks.value.filter(task => isActiveTaskStatus(task.status))
)

const activeBackgroundTaskCount = computed(() =>
  activeVerificationTasks.value.length + activeSimulationTasks.value.length + activeFuzzingTasks.value.length
)

const miniTaskItems = computed(() => {
  const items: Array<{
    key: string
    kind: 'verification' | 'fuzzing' | 'simulation'
    id: number
    label: string
    status: string
    progress: number
  }> = []

  const currentVerificationId = asyncVerificationTask.value.taskId
  if (isVerifying.value && asyncVerificationActive.value && currentVerificationId) {
    items.push({
      key: `verification-${currentVerificationId}`,
      kind: 'verification',
      id: currentVerificationId,
      label: t('app.verification'),
      status: asyncVerificationTask.value.status,
      progress: normalizeTaskProgress(asyncVerificationTask.value.progress)
    })
  }
  for (const task of activeVerificationTasks.value) {
    if (task.id === currentVerificationId) continue
    items.push({
      key: `verification-${task.id}`,
      kind: 'verification',
      id: task.id,
      label: t('app.verification'),
      status: formatTaskProgressStage(task.progressStage, task.status),
      progress: normalizeTaskProgress(task.progress)
    })
  }

  const currentFuzzingId = asyncFuzzingTask.value.taskId
  if (isFuzzing.value && asyncFuzzingActive.value && currentFuzzingId) {
    items.push({
      key: `fuzzing-${currentFuzzingId}`,
      kind: 'fuzzing',
      id: currentFuzzingId,
      label: t('app.fuzzSearch'),
      status: asyncFuzzingTask.value.status,
      progress: normalizeTaskProgress(asyncFuzzingTask.value.progress)
    })
  }
  for (const task of activeFuzzingTasks.value) {
    if (task.id === currentFuzzingId) continue
    items.push({
      key: `fuzzing-${task.id}`,
      kind: 'fuzzing',
      id: task.id,
      label: t('app.fuzzSearch'),
      status: formatTaskProgressStage(task.progressStage, task.status),
      progress: normalizeTaskProgress(task.progress)
    })
  }

  const currentSimulationId = asyncSimulationTask.value.taskId
  if (isSimulating.value && asyncSimulationActive.value && currentSimulationId) {
    items.push({
      key: `simulation-${currentSimulationId}`,
      kind: 'simulation',
      id: currentSimulationId,
      label: t('app.simulation'),
      status: asyncSimulationTask.value.status,
      progress: normalizeTaskProgress(asyncSimulationTask.value.progress)
    })
  }
  for (const task of activeSimulationTasks.value) {
    if (task.id === currentSimulationId) continue
    items.push({
      key: `simulation-${task.id}`,
      kind: 'simulation',
      id: task.id,
      label: t('app.simulation'),
      status: formatTaskProgressStage(task.progressStage, task.status),
      progress: normalizeTaskProgress(task.progress)
    })
  }

  return items
})

const invalidateTaskInboxRequests = () => {
  taskInboxRequests.invalidate()
  taskInboxBackgroundRefreshPromise = null
  taskInboxLoadingEpoch += 1
  loadingTaskHistory.value = false
}

const upsertVerificationTaskSummary = (task: Partial<VerificationTaskSummary> & { id?: number }) => {
  if (!task.id) return
  invalidateTaskInboxRequests()
  const existing = verificationTasks.value.findIndex(item => item.id === task.id)
  const next = task as VerificationTaskSummary
  verificationTasks.value = existing >= 0
    ? verificationTasks.value.map(item => item.id === task.id ? { ...item, ...next } : item)
    : [next, ...verificationTasks.value]
}

const upsertSimulationTaskSummary = (task: Partial<SimulationTaskSummary> & { id?: number }) => {
  if (!task.id) return
  invalidateTaskInboxRequests()
  const existing = simulationTasks.value.findIndex(item => item.id === task.id)
  const next = task as SimulationTaskSummary
  simulationTasks.value = existing >= 0
    ? simulationTasks.value.map(item => item.id === task.id ? { ...item, ...next } : item)
    : [next, ...simulationTasks.value]
}

const upsertFuzzingTaskSummary = (task: Partial<FuzzingTaskSummary> & { id?: number }) => {
  if (!task.id) return
  invalidateTaskInboxRequests()
  const existing = fuzzingTasks.value.findIndex(item => item.id === task.id)
  const next = task as FuzzingTaskSummary
  fuzzingTasks.value = existing >= 0
    ? fuzzingTasks.value.map(item => item.id === task.id ? { ...item, ...next } : item)
    : [next, ...fuzzingTasks.value]
}

type TaskInboxBatch<T> = {
  tasks: T[]
  excludedIds: number[]
}

const fetchVerificationTasks = async (): Promise<TaskInboxBatch<VerificationTaskSummary>> => {
  const excludedIds = [...watchedVerificationTaskIds.value]
  const tasks = await boardApi.getTasks(excludedIds)
  return { tasks: tasks || [], excludedIds }
}

const fetchSimulationTasks = async (): Promise<TaskInboxBatch<SimulationTaskSummary>> => {
  const excludedIds = [...watchedSimulationTaskIds.value]
  const tasks = await simulationApi.getTasks(excludedIds)
  return { tasks: tasks || [], excludedIds }
}

const reconcileTrackedFuzzTasks = async (
  tasks: FuzzingTaskSummary[],
  excludedIds: number[],
  isCurrent: () => boolean
) => {
  if (!isCurrent()) return
  const unavailableTaskIds: number[] = []
  tasks.filter(task => isActiveTaskStatus(task.status)).forEach(task => trackFuzzTask(task.id))
  const excluded = new Set(excludedIds)
  const byId = new Map(tasks.map(task => [task.id, task]))
  const completedCandidates: Array<{ taskId: number; task?: FuzzingTaskSummary }> = []

  for (const taskId of [...trackedFuzzTaskIds.value]) {
    if (excluded.has(taskId)) continue
    const task = byId.get(taskId)
    if (task && isActiveTaskStatus(task.status)) continue
    if (task?.status === 'CANCELLED') {
      untrackFuzzTask(taskId)
      continue
    }
    if (task?.status === 'FAILED') {
      markFuzzNotificationUnread({
        taskId,
        kind: 'FAILED',
        createdAt: task.completedAt || task.createdAt
      })
      continue
    }
    if (canAttemptFuzzRunRecovery(taskId)) completedCandidates.push({ taskId, task })
  }

  // A bounded batch avoids turning a restored list of task IDs into a request burst.
  await Promise.all(completedCandidates.slice(0, 4).map(async ({ taskId, task }) => {
    let resolvedTask = task
    try {
      // Completed tasks are omitted from the inbox, but an active task can also be
      // absent because the inbox is paged. Resolve status before treating absence as completion.
      if (!resolvedTask) {
        resolvedTask = await fuzzingApi.getTask(taskId)
        if (!isCurrent()) return
      }
      if (!isCurrent() || isActiveTaskStatus(resolvedTask.status)) return
      if (resolvedTask.status === 'CANCELLED') {
        untrackFuzzTask(taskId)
        return
      }
      if (resolvedTask.status === 'FAILED') {
        markFuzzNotificationUnread({
          taskId,
          kind: 'FAILED',
          createdAt: resolvedTask.completedAt || resolvedTask.createdAt
        })
        return
      }
      const run = await loadFuzzRunSingleFlight(taskId, resolvedTask.runId ?? taskId)
      if (!isCurrent()) return
      clearFuzzRunRecoveryState(taskId)
      markFuzzNotificationUnread({
        taskId,
        runId: run.id,
        kind: 'COMPLETED',
        outcome: run.outcome,
        createdAt: run.completedAt
      })
    } catch (error: any) {
      if (!isCurrent()) return
      if (classifyTrackedFuzzRunError(error) === 'RETRY') {
        scheduleFuzzRunRecovery(taskId)
        return
      }
      const createdAt = resolvedTask?.completedAt
        || resolvedTask?.createdAt
        || new Date().toISOString()
      upsertFuzzingRunSummary({
        id: taskId,
        explorationMode: resolvedTask?.explorationMode,
        createdAt,
        completedAt: resolvedTask?.completedAt,
        findingCount: 0,
        findings: [],
        dataAvailable: false,
        unavailableReasonCode: 'RESULT_UNAVAILABLE'
      })
      markFuzzNotificationUnread({
        taskId,
        runId: taskId,
        kind: 'UNAVAILABLE',
        createdAt
      })
      unavailableTaskIds.push(taskId)
    }
  }))
  if (isCurrent() && unavailableTaskIds.length > 0) {
    ElMessage.error({
      message: t('app.fuzzTrackedRunsUnavailable', { count: unavailableTaskIds.length }),
      type: 'error',
      duration: 6500
    })
  }
}

const fetchFuzzingTasks = async (): Promise<TaskInboxBatch<FuzzingTaskSummary>> => {
  const excludedIds = [...watchedFuzzingTaskIds.value]
  const tasks = await fuzzingApi.getTasks(excludedIds, 0, FUZZ_TASK_INBOX_PAGE_SIZE)
  return { tasks: tasks || [], excludedIds }
}

const loadTaskInbox = async (
  showError = true,
  options: { showLoading?: boolean } = {}
): Promise<boolean> => {
  if (boardLifecycleDisposed) return false
  const showLoading = options.showLoading ?? true
  const token = taskInboxRequests.beginReplace()
  const loadingEpoch = ++taskInboxLoadingEpoch
  if (showLoading) loadingTaskHistory.value = true
  try {
    const [verification, simulation, fuzzing] = await Promise.all([
      fetchVerificationTasks(),
      fetchSimulationTasks(),
      fetchFuzzingTasks()
    ])
    if (!taskInboxRequests.isCurrent(token)) return true
    await reconcileTrackedFuzzTasks(
      fuzzing.tasks,
      fuzzing.excludedIds,
      () => taskInboxRequests.isCurrent(token)
    )
    if (!taskInboxRequests.isCurrent(token)) return true
    verificationTasks.value = mergeTaskSummariesPreservingExcluded(
      verificationTasks.value,
      verification.tasks,
      verification.excludedIds
    )
    simulationTasks.value = mergeTaskSummariesPreservingExcluded(
      simulationTasks.value,
      simulation.tasks,
      simulation.excludedIds
    )
    fuzzingTasks.value = mergeTaskSummariesPreservingExcluded(
      fuzzingTasks.value,
      fuzzing.tasks,
      fuzzing.excludedIds
    )
    return true
  } catch (e: any) {
    if (!taskInboxRequests.isCurrent(token)) return true
    console.error('Failed to load async tasks:', e)
    if (showError) {
      ElMessage.error({
        message: extractApiErrorMessage(e, t('app.failedToLoadTasks')),
        type: 'error'
      })
    }
    return false
  } finally {
    if (loadingEpoch === taskInboxLoadingEpoch) loadingTaskHistory.value = false
    taskInboxRequests.finish(token)
  }
}

const refreshTaskInboxInBackground = (): Promise<boolean> => {
  if (boardLifecycleDisposed) return Promise.resolve(false)
  if (taskInboxBackgroundRefreshPromise) return taskInboxBackgroundRefreshPromise
  const refresh = loadTaskInbox(false, { showLoading: false })
  taskInboxBackgroundRefreshPromise = refresh
  void refresh.finally(() => {
    if (taskInboxBackgroundRefreshPromise === refresh) {
      taskInboxBackgroundRefreshPromise = null
    }
  })
  return refresh
}

const loadVerificationRuns = async (showError = true): Promise<boolean> => {
  if (boardLifecycleDisposed) return false
  const token = verificationHistoryRequests.beginReplace()
  try {
    const runs = await boardApi.getVerificationRuns()
    if (!verificationHistoryRequests.isCurrent(token)) return true
    verificationRuns.value = runs || []
    historyResultErrors.verification = null
    return true
  } catch (e: any) {
    if (!verificationHistoryRequests.isCurrent(token)) return true
    console.error('Failed to load verification run history:', e)
    historyResultErrors.verification = localizedErrorMessage(
      e,
      t('app.failedToLoadVerificationHistory'),
      locale.value
    )
    if (showError) {
      ElMessage.error({ message: t('app.failedToLoadVerificationHistory'), type: 'error' })
    }
    return false
  } finally {
    verificationHistoryRequests.finish(token)
  }
}

const loadSimulationRuns = async (showError = true): Promise<boolean> => {
  if (boardLifecycleDisposed) return false
  const token = simulationHistoryRequests.beginReplace()
  try {
    const runs = await simulationApi.getUserSimulations()
    if (!simulationHistoryRequests.isCurrent(token)) return true
    simulationRuns.value = runs || []
    historyResultErrors.simulation = null
    return true
  } catch (e: any) {
    if (!simulationHistoryRequests.isCurrent(token)) return true
    console.error('Failed to load simulation run history:', e)
    historyResultErrors.simulation = localizedErrorMessage(
      e,
      t('app.failedToLoadSimulationHistory'),
      locale.value
    )
    if (showError) {
      ElMessage.error({ message: t('app.failedToLoadSimulationHistory'), type: 'error' })
    }
    return false
  } finally {
    simulationHistoryRequests.finish(token)
  }
}

const executeFuzzingRunsRequest = async (
  token: PagedRequestToken,
  showError = true,
  page = 0,
  append = false
): Promise<boolean> => {
  try {
    const [runs] = await Promise.all([
      fuzzingApi.getRuns(page, FUZZ_RUN_HISTORY_PAGE_SIZE),
      refreshCurrentFuzzingModelFingerprint()
    ])
    if (!fuzzingHistoryRequests.isCurrent(token)) return true
    if (append) {
      const existingIds = new Set(fuzzingRuns.value.map(run => run.id))
      fuzzingRuns.value = [
        ...fuzzingRuns.value,
        ...runs.filter(run => !existingIds.has(run.id))
      ]
    } else {
      fuzzingRuns.value = withUnreadFuzzUnavailablePlaceholders(runs)
    }
    historyResultErrors.fuzzing = null
    fuzzingRunsPage.value = page
    fuzzingRunsHasMore.value = runs.length === FUZZ_RUN_HISTORY_PAGE_SIZE
    return true
  } catch (e: any) {
    if (!fuzzingHistoryRequests.isCurrent(token)) return true
    console.error('Failed to load fuzzing run history:', e)
    historyResultErrors.fuzzing = localizedErrorMessage(
      e,
      t('app.failedToLoadFuzzingHistory'),
      locale.value
    )
    if (showError) {
      ElMessage.error({
        message: extractApiErrorMessage(e, t('app.failedToLoadFuzzingHistory')),
        type: 'error'
      })
    }
    return false
  } finally {
    fuzzingHistoryRequests.finish(token)
  }
}

const loadFuzzingRuns = (
  showError = true,
  options: { page?: number; append?: boolean } = {}
): Promise<boolean> => {
  if (boardLifecycleDisposed) return Promise.resolve(false)
  const page = options.page ?? 0
  const append = options.append === true
  if (append && fuzzingHistoryAppendPromise) return fuzzingHistoryAppendPromise

  const token = append
    ? fuzzingHistoryRequests.beginAppend()
    : fuzzingHistoryRequests.beginReplace()
  if (!token) return Promise.resolve(true)

  if (!append) return executeFuzzingRunsRequest(token, showError, page, false)

  loadingMoreFuzzingRuns.value = true
  let trackedRequest: Promise<boolean>
  trackedRequest = executeFuzzingRunsRequest(token, showError, page, true)
    .finally(() => {
      if (fuzzingHistoryAppendPromise === trackedRequest) {
        fuzzingHistoryAppendPromise = null
        loadingMoreFuzzingRuns.value = false
      }
    })
  fuzzingHistoryAppendPromise = trackedRequest
  return trackedRequest
}

const loadMoreFuzzingRuns = async () => {
  if (boardLifecycleDisposed || loadingMoreFuzzingRuns.value || !fuzzingRunsHasMore.value) return
  await loadFuzzingRuns(true, { page: fuzzingRunsPage.value + 1, append: true })
}

const loadHistoryResults = async (showError = true): Promise<boolean> => {
  if (boardLifecycleDisposed) return false
  const loadingEpoch = ++historyResultsLoadingEpoch
  loadingResultHistory.value = true
  try {
    const results = await Promise.all([
      loadVerificationRuns(false),
      loadSimulationRuns(false),
      loadFuzzingRuns(false)
    ])
    const failedSources = [
      !results[0] ? t('app.verificationRunResult') : null,
      !results[1] ? t('app.simulationRunResult') : null,
      !results[2] ? t('app.fuzzRunResult') : null
    ].filter((source): source is string => Boolean(source))
    if (failedSources.length > 0 && showError) {
      ElMessage.error({
        message: t('app.failedToLoadRunResultSources', {
          sources: failedSources.join(locale.value.toLowerCase().startsWith('zh') ? '、' : ', ')
        }),
        type: 'error'
      })
    }
    return results.every(Boolean)
  } finally {
    if (loadingEpoch === historyResultsLoadingEpoch) loadingResultHistory.value = false
  }
}

const refreshRunHistory = async (): Promise<boolean> => {
  const results = await Promise.all([
    loadTaskInbox(false, { showLoading: false }),
    loadHistoryResults(false)
  ])
  return results.every(Boolean)
}

const refreshAllBoardState = async (): Promise<boolean> => {
  const results = await Promise.all([
    refreshSceneForReconciliation(),
    refreshRunHistory()
  ])
  return results.every(Boolean)
}

const refreshHistoryLayer = async (layer: HistoryLayer = activeHistoryLayer.value): Promise<boolean> => {
  historyDetailRequests.invalidate()
  if (layer === 'tasks') {
    return loadTaskInbox()
  }
  return loadHistoryResults()
}

const setHistoryLayer = async (layer: HistoryLayer) => {
  const intentEpoch = ++historyPanelIntentEpoch
  historyDetailRequests.invalidate()
  activeHistoryLayer.value = layer
  const loaded = await refreshHistoryLayer(layer)
  if (!loaded || !isCurrentHistoryPanelIntent(intentEpoch, layer)) return
  if (layer === 'results') {
    if (activeHistoryResultFilter.value === 'all' || activeHistoryResultFilter.value === 'fuzzing') {
      clearVisibleFuzzResultNotifications()
    }
  } else {
    clearFuzzNotifications('FAILED')
  }
}

const setHistoryResultFilter = async (filter: HistoryResultFilter) => {
  const intentEpoch = ++historyPanelIntentEpoch
  historyDetailRequests.invalidate()
  activeHistoryResultFilter.value = filter
  if (showHistoryPanel.value
    && activeHistoryLayer.value === 'results'
    && (filter === 'all' || filter === 'fuzzing')) {
    const loaded = await loadFuzzingRuns(true)
    if (loaded && isCurrentHistoryPanelIntent(intentEpoch, 'results', filter)) {
      clearVisibleFuzzResultNotifications()
    }
  }
}

const closeHistoryPanel = (invalidatePendingDetail = true) => {
  historyPanelIntentEpoch += 1
  if (invalidatePendingDetail) historyDetailRequests.invalidate()
  showHistoryPanel.value = false
}

const toggleHistoryPanel = async (layer: HistoryLayer = activeHistoryLayer.value) => {
  if (showHistoryPanel.value && activeHistoryLayer.value === layer) {
    closeHistoryPanel()
    return
  }
  if (isModelPlaybackActive.value) {
    ElMessage.warning({ message: t('app.playbackReadOnlyCloseFirst'), type: 'warning' })
    return
  }
  if (isAnyRecommendationRunning()) {
    ElMessage.warning({ message: t('app.recommendationGenerationInProgress'), type: 'warning' })
    return
  }

  closeResultSurfaces()
  showSimulationPanel.value = false
  showVerificationPanel.value = false
  showFuzzingPanel.value = false
  closeRecommendationPanel()
  closeDeviceRecommendationPanel()
  closeSpecRecommendationPanel()
  closeScenarioRecommendationPanel()

  const intentEpoch = ++historyPanelIntentEpoch
  historyDetailRequests.invalidate()
  activeHistoryLayer.value = layer
  showHistoryPanel.value = true
  const loaded = await refreshHistoryLayer(layer)
  if (!loaded || !isCurrentHistoryPanelIntent(intentEpoch, layer)) return
  if (layer === 'results') {
    if (activeHistoryResultFilter.value === 'all' || activeHistoryResultFilter.value === 'fuzzing') {
      clearVisibleFuzzResultNotifications()
    }
  } else {
    clearFuzzNotifications('FAILED')
  }
}

const formatRunTimestamp = (value?: string): string => {
  if (!value) return t('app.unknown')
  const date = new Date(value)
  if (Number.isNaN(date.getTime())) return value
  return date.toLocaleString(locale.value.toLowerCase().startsWith('zh') ? 'zh-CN' : 'en-US')
}

const refreshHistoryTasks = () => {
  historyDetailRequests.invalidate()
  return loadTaskInbox()
}

const refreshHistoryResults = () => {
  historyDetailRequests.invalidate()
  return loadHistoryResults()
}

const deleteVerificationRun = async (run: VerificationRunSummary) => {
  const runId = run.id
  historyDetailRequests.invalidate()
  try {
    await ElMessageBox.confirm(
      t('app.deleteVerificationRunMessage', {
        time: formatRunTimestamp(run.completedAt),
        counterexamples: run.counterexampleCount
      }),
      t('app.deleteVerificationRunTitle'),
      {
        confirmButtonText: t('app.delete'),
        cancelButtonText: t('app.cancel'),
        type: 'warning',
        appendTo: 'body',
        lockScroll: false
      }
    )
    await boardApi.deleteVerificationRun(runId)
    if (boardLifecycleDisposed) return
    verificationHistoryRequests.invalidate()
    verificationRuns.value = verificationRuns.value.filter(item => item.id !== runId)
    ElMessage.success({ message: t('app.verificationRunDeleted'), type: 'success' })
  } catch (e: any) {
    if (e === 'cancel' || e === 'close') return
    if (boardLifecycleDisposed) return
    console.error('Failed to delete verification run:', e)
    const refreshed = await loadVerificationRuns(false)
    if (boardLifecycleDisposed) return
    if (refreshed && !verificationRuns.value.some(item => item.id === runId)) {
      ElMessage.warning({ message: t('app.verificationRunDeleteOutcomeRefreshed'), type: 'warning' })
      return
    }
    ElMessage.error({
      message: localizedErrorMessage(e, t('app.failedToDeleteVerificationRun'), locale.value),
      type: 'error'
    })
  }
}

const openVerificationRun = async (runId: number) => {
  const requestToken = historyDetailRequests.beginReplace()
  try {
    const run = await boardApi.getVerificationRun(runId)
    if (!historyDetailRequests.isCurrent(requestToken) || boardLifecycleDisposed) return
    const traces = run.outcome === 'VIOLATED'
      ? await boardApi.getVerificationRunTraces(runId)
      : []
    if (!historyDetailRequests.isCurrent(requestToken) || boardLifecycleDisposed) return
    verificationResult.value = attachLocalRunSubmission(
      buildVerificationResultFromRun(run, traces),
      null
    )
    closeHistoryPanel(false)
  } catch (e: any) {
    if (!historyDetailRequests.isCurrent(requestToken) || boardLifecycleDisposed) return
    console.error('Failed to load verification run:', e)
    ElMessage.error({ message: extractApiErrorMessage(e, t('app.failedToLoadVerificationRun')), type: 'error' })
  } finally {
    historyDetailRequests.finish(requestToken)
  }
}

const watchVerificationTask = async (taskId: number) => {
  if (isVerifying.value) {
    if (asyncVerificationTask.value.taskId === taskId) {
      showVerificationPanel.value = true
    } else {
      ElMessage.info({ message: t('app.taskWatchAlreadyActive'), type: 'info' })
    }
    closeHistoryPanel()
    return
  }
  const taskSummary = verificationTasks.value.find(task => task.id === taskId)
  isVerifying.value = true
  asyncVerificationActive.value = true
  verificationCancelRequested.value = false
  cancellingVerificationTask.value = false
  asyncVerificationTask.value = {
    taskId,
    progress: normalizeTaskProgress(taskSummary?.progress),
    status: formatTaskProgressStage(taskSummary?.progressStage, taskSummary?.status) || t('app.taskInitializing')
  }
  closeHistoryPanel()
  try {
    await pollAsyncVerification(taskId, { presentResult: true })
  } catch (error: any) {
    if (!isPollingAbortedError(error)) {
      const message = extractApiErrorMessage(error, t('app.verificationFailed'))
      if (isAsyncTaskCancelledError(error)) {
        verificationError.value = null
        ElMessage.info({ message: t('app.verificationCancelled'), type: 'info' })
      } else {
        verificationError.value = message
        ElMessage.error({ message, type: 'error' })
      }
    }
  } finally {
    isVerifying.value = false
    asyncVerificationActive.value = false
    cancellingVerificationTask.value = false
    verificationCancelRequested.value = false
    if (!boardLifecycleDisposed) {
      await loadTaskInbox(false, { showLoading: false })
    }
  }
}

const watchSimulationTask = async (taskId: number) => {
  if (isSimulating.value) {
    if (asyncSimulationTask.value.taskId === taskId) {
      showSimulationPanel.value = true
    } else {
      ElMessage.info({ message: t('app.taskWatchAlreadyActive'), type: 'info' })
    }
    closeHistoryPanel()
    return
  }
  const taskSummary = simulationTasks.value.find(task => task.id === taskId)
  isSimulating.value = true
  asyncSimulationActive.value = true
  simulationCancelRequested.value = false
  cancellingSimulationTask.value = false
  asyncSimulationTask.value = {
    taskId,
    progress: normalizeTaskProgress(taskSummary?.progress),
    status: formatTaskProgressStage(taskSummary?.progressStage, taskSummary?.status) || t('app.taskInitializing')
  }
  closeHistoryPanel()
  try {
    const result = attachLocalRunSubmission(
      await pollAsyncSimulation(taskId),
      submissionForTask(activeSimulationSubmission.value, taskId)
    )
    lastSimulationResult.value = result
    if (result.traceId) {
      simulationHistoryRequests.invalidate()
      simulationRuns.value = [
        {
          id: result.traceId,
          requestedSteps: result.requestedSteps,
          steps: result.steps,
          modelComplete: isSimulationModelComplete(result),
          disabledRuleCount: getSimulationDisabledRuleCount(result),
          generationIssues: getGenerationIssues(result),
          isAttack: result.isAttack === true,
          attackBudget: result.attackBudget ?? 0,
          enablePrivacy: result.enablePrivacy === true,
          modelSnapshot: result.modelSnapshot,
          createdAt: result.createdAt || new Date().toISOString(),
          dataAvailable: true
        },
        ...simulationRuns.value.filter(item => item.id !== result.traceId)
      ]
    }
    if (result.states && result.states.length > 0) {
      if (traceAnimationState.value.visible || simulationAnimationState.value.visible) {
        notifySimulationOutcome(result, true)
        return
      }
      if (isLiveBoardEditorVisible.value) {
        notifySimulationOutcome(result, true)
        notifyAutomaticPlaybackDeferred()
        return
      }
      savedSimulationStates.value = [...result.states]
      simulationAnimationState.value = {
        visible: true
      }
      highlightedTrace.value = {
        states: savedSimulationStates.value,
        selectedStateIndex: 0
      }
      notifySimulationOutcome(result, true)
    }
  } catch (error: any) {
    if (!isPollingAbortedError(error)) {
      const message = extractApiErrorMessage(error, t('app.simulationFailed'))
      if (isAsyncTaskCancelledError(error)) {
        simulationError.value = null
        ElMessage.info({ message: t('app.simulationCancelled'), type: 'info' })
      } else {
        simulationError.value = message
        ElMessage.error({ message, type: 'error' })
      }
    }
  } finally {
    isSimulating.value = false
    asyncSimulationActive.value = false
    cancellingSimulationTask.value = false
    simulationCancelRequested.value = false
    if (!boardLifecycleDisposed) {
      await loadTaskInbox(false, { showLoading: false })
    }
  }
}

const upsertFuzzingRunSummary = (run: FuzzingRunSummary) => {
  fuzzingHistoryRequests.invalidate()
  const existingIndex = fuzzingRuns.value.findIndex(item => item.id === run.id)
  if (existingIndex >= 0) {
    fuzzingRuns.value = fuzzingRuns.value.map(item => item.id === run.id ? run : item)
    return
  }
  const previousCount = fuzzingRuns.value.length
  fuzzingRuns.value = [run, ...fuzzingRuns.value].slice(0, FUZZ_RUN_HISTORY_PAGE_SIZE)
  fuzzingRunsPage.value = 0
  fuzzingRunsHasMore.value = fuzzingRunsHasMore.value || previousCount >= FUZZ_RUN_HISTORY_PAGE_SIZE
}

const summarizeFuzzingRun = (run: FuzzingRun): AvailableFuzzingRunSummary => ({
  ...run,
  dataAvailable: true,
  findings: run.findings.map(finding => ({
    id: finding.id,
    fuzzTaskId: finding.fuzzTaskId,
    violatedSpecId: finding.violatedSpecId,
    violatedSpec: finding.violatedSpec,
    specificationLabel: finding.violatedSpec.templateLabel
      || finding.violatedSpec.formula
      || finding.violatedSpecId,
    firstViolationStep: finding.firstViolationStep,
    seed: finding.seed,
    createdAt: finding.createdAt,
    stateCount: finding.states.length,
    dataAvailable: true
  }))
})

const presentFuzzingRun = (run: FuzzingRun) => {
  // Transient notices must not cover the result's title or primary actions.
  ElMessage.closeAll()
  const summary = summarizeFuzzingRun(run)
  upsertFuzzingRunSummary(summary)
  fuzzingError.value = null
  fuzzingResult.value = run
  void refreshCurrentFuzzingModelFingerprint()
  showFuzzingResultDialog.value = true
  clearFuzzNotifications(undefined, run.id)
}

const watchFuzzingTask = async (taskId: number) => {
  if (isFuzzing.value) {
    if (asyncFuzzingTask.value.taskId === taskId) {
      showFuzzingPanel.value = true
    } else {
      ElMessage.info({ message: t('app.taskWatchAlreadyActive'), type: 'info' })
    }
    closeHistoryPanel()
    return
  }

  const taskSummary = fuzzingTasks.value.find(task => task.id === taskId)
  // Keep the running request separate from the editable form. Its persisted summary is
  // the only truthful source after a refresh or after the current Board has changed.
  fuzzingWatchedTask.value = taskSummary || null
  isFuzzing.value = true
  asyncFuzzingActive.value = true
  fuzzingCancelRequested.value = false
  cancellingFuzzingTask.value = false
  fuzzingError.value = null
  paperDomainStaleRecoveryActive.value = false
  asyncFuzzingTask.value = {
    taskId,
    progress: normalizeTaskProgress(taskSummary?.progress),
    status: formatTaskProgressStage(taskSummary?.progressStage, taskSummary?.status) || t('app.taskInitializing')
  }
  trackFuzzTask(taskId)
  closeHistoryPanel()
  showFuzzingPanel.value = true
  try {
    const run = await pollAsyncFuzzing(taskId)
    untrackFuzzTask(taskId)
    showFuzzingPanel.value = false
    presentFuzzingRun(run)
  } catch (error: any) {
    if (!isPollingAbortedError(error)) {
      if (isAsyncTaskCancelledError(error)) {
        untrackFuzzTask(taskId)
        fuzzingError.value = null
        ElMessage.info({ message: t('app.fuzzSearchCancelled'), type: 'info' })
      } else if (isFuzzTaskRecoveryPendingError(error)) {
        fuzzingError.value = null
        fuzzingSettingsNotice.value = t('app.fuzzResultRecoveryPending')
        ElMessage.info({ message: fuzzingSettingsNotice.value, type: 'info', duration: 6500 })
      } else if (isFuzzCompletedResultUnavailableError(error)) {
        fuzzingError.value = error.message || t('app.failedToLoadFuzzingRun')
        markFuzzNotificationUnread({
          taskId,
          runId: taskId,
          kind: 'UNAVAILABLE',
          createdAt: new Date().toISOString()
        })
      } else {
        console.error('Fuzz task watch failed:', error)
        fuzzingError.value = localizedErrorMessage(error, t('app.fuzzSearchFailed'), locale.value)
        if (showFuzzingPanel.value) {
          untrackFuzzTask(taskId)
        } else {
          markFuzzNotificationUnread({
            taskId,
            kind: 'FAILED',
            createdAt: new Date().toISOString()
          })
          ElMessage.error({ message: fuzzingError.value, type: 'error' })
        }
      }
    }
  } finally {
    isFuzzing.value = false
    asyncFuzzingActive.value = false
    cancellingFuzzingTask.value = false
    fuzzingCancelRequested.value = false
    fuzzingWatchedTask.value = null
    if (!boardLifecycleDisposed) {
      await loadTaskInbox(false, { showLoading: false })
    }
  }
}

const cancelVerificationTaskFromInbox = (taskId: number) => withTaskActionLock(
  taskActionKey('cancel', 'verification', taskId),
  async () => {
    try {
      if (asyncVerificationTask.value.taskId === taskId) {
        await cancelAsyncVerification()
      } else {
        const result = await boardApi.cancelTask(taskId)
        if (boardLifecycleDisposed) return
        notifyTaskCancellationResult('verification', result)
      }
    } catch (error) {
      if (boardLifecycleDisposed) return
      console.error('Failed to cancel verification task from inbox:', error)
      ElMessage.error({ message: t('app.failedToCancelVerificationTask'), type: 'error' })
    } finally {
      if (!boardLifecycleDisposed) {
        await loadTaskInbox(false, { showLoading: false })
      }
    }
  }
)

const cancelSimulationTaskFromInbox = (taskId: number) => withTaskActionLock(
  taskActionKey('cancel', 'simulation', taskId),
  async () => {
    try {
      if (asyncSimulationTask.value.taskId === taskId) {
        await cancelAsyncSimulation()
      } else {
        const result = await simulationApi.cancelTask(taskId)
        if (boardLifecycleDisposed) return
        notifyTaskCancellationResult('simulation', result)
      }
    } catch (error) {
      if (boardLifecycleDisposed) return
      console.error('Failed to cancel simulation task from inbox:', error)
      ElMessage.error({ message: t('app.failedToCancelSimulationTask'), type: 'error' })
    } finally {
      if (!boardLifecycleDisposed) {
        await loadTaskInbox(false, { showLoading: false })
      }
    }
  }
)

const cancelFuzzingTaskFromInbox = (taskId: number) => withTaskActionLock(
  taskActionKey('cancel', 'fuzzing', taskId),
  async () => {
    try {
      if (asyncFuzzingTask.value.taskId === taskId) {
        await cancelAsyncFuzzing()
      } else {
        const result = await fuzzingApi.cancelTask(taskId)
        if (boardLifecycleDisposed) return
        notifyTaskCancellationResult('fuzzing', result)
      }
    } catch (error) {
      if (boardLifecycleDisposed) return
      console.error('Failed to cancel fuzzing task from inbox:', error)
      ElMessage.error({ message: t('app.failedToCancelFuzzingTask'), type: 'error' })
    } finally {
      if (!boardLifecycleDisposed) {
        await loadTaskInbox(false, { showLoading: false })
      }
    }
  }
)

const dismissVerificationTask = (taskId: number) => withTaskActionLock(
  taskActionKey('dismiss', 'verification', taskId),
  async () => {
    try {
      await boardApi.deleteTask(taskId)
      if (boardLifecycleDisposed) return
      invalidateTaskInboxRequests()
      verificationTasks.value = verificationTasks.value.filter(task => task.id !== taskId)
      ElMessage.success({ message: t('app.taskDismissed'), type: 'success' })
    } catch (e: any) {
      if (boardLifecycleDisposed) return
      ElMessage.error({ message: extractApiErrorMessage(e, t('app.failedToDismissTask')), type: 'error' })
      await loadTaskInbox(false, { showLoading: false })
    }
  }
)

const dismissSimulationTask = (taskId: number) => withTaskActionLock(
  taskActionKey('dismiss', 'simulation', taskId),
  async () => {
    try {
      await simulationApi.deleteTask(taskId)
      if (boardLifecycleDisposed) return
      invalidateTaskInboxRequests()
      simulationTasks.value = simulationTasks.value.filter(task => task.id !== taskId)
      ElMessage.success({ message: t('app.taskDismissed'), type: 'success' })
    } catch (e: any) {
      if (boardLifecycleDisposed) return
      ElMessage.error({ message: extractApiErrorMessage(e, t('app.failedToDismissTask')), type: 'error' })
      await loadTaskInbox(false, { showLoading: false })
    }
  }
)

const dismissFuzzingTask = (taskId: number) => withTaskActionLock(
  taskActionKey('dismiss', 'fuzzing', taskId),
  async () => {
    try {
      await fuzzingApi.deleteTask(taskId)
      if (boardLifecycleDisposed) return
      invalidateTaskInboxRequests()
      fuzzingTasks.value = fuzzingTasks.value.filter(task => task.id !== taskId)
      clearFuzzNotifications(undefined, taskId)
      untrackFuzzTask(taskId)
      ElMessage.success({ message: t('app.taskDismissed'), type: 'success' })
    } catch (e: any) {
      if (boardLifecycleDisposed) return
      console.error('Failed to dismiss fuzzing task:', e)
      ElMessage.error({ message: t('app.failedToDismissTask'), type: 'error' })
      await loadTaskInbox(false, { showLoading: false })
    }
  }
)

const openTaskInbox = async () => {
  if (isModelPlaybackActive.value) {
    ElMessage.warning({ message: t('app.playbackReadOnlyCloseFirst'), type: 'warning' })
    return
  }
  const intentEpoch = ++historyPanelIntentEpoch
  historyDetailRequests.invalidate()
  closeResultSurfaces()
  showSimulationPanel.value = false
  showVerificationPanel.value = false
  showFuzzingPanel.value = false
  closeRecommendationPanel()
  closeDeviceRecommendationPanel()
  closeSpecRecommendationPanel()
  closeScenarioRecommendationPanel()
  activeHistoryLayer.value = 'tasks'
  showHistoryPanel.value = true
  const loaded = await loadTaskInbox(false)
  if (loaded && isCurrentHistoryPanelIntent(intentEpoch, 'tasks')) {
    clearFuzzNotifications('FAILED')
  }
}

const miniTaskCancelLabel = (kind: 'verification' | 'fuzzing' | 'simulation') => kind === 'verification'
  ? t('app.cancelVerificationTask')
  : kind === 'fuzzing' ? t('app.cancelFuzzingTask') : t('app.cancelSimulationTask')

const cancelMiniTask = async (kind: 'verification' | 'fuzzing' | 'simulation', taskId: number) => {
  if (kind === 'verification') {
    await cancelVerificationTaskFromInbox(taskId)
  } else if (kind === 'fuzzing') {
    await cancelFuzzingTaskFromInbox(taskId)
  } else {
    await cancelSimulationTaskFromInbox(taskId)
  }
}

const selectAndPlayVerificationTrace = async (traceId: number) => {
  // Same mutual-exclusion guards as selectAndPlayTrace: a historical trace opens the same animation
  // surface, so it must not stack on top of a running simulation timeline or the recommendations panel.
  const guard = canOpenTracePlayback({
    simulationVisible: simulationAnimationState.value.visible,
    recommendationPanelVisible: isAnyRecommendationPanelVisible()
  })
  if (!guard.allowed) {
    ElMessage.warning({
      message: guard.reasonCode === 'SIMULATION_VISIBLE'
        ? t('app.closeCurrentSimulationFirst')
        : t('app.closeRecommendationPanelsFirst'),
      type: 'warning'
    })
    return
  }
  if (!ensureLiveBoardEditorClosedForPlayback()) return
  const requestToken = historyDetailRequests.beginReplace()
  try {
    const trace = await boardApi.getVerificationTrace(traceId)
    if (!historyDetailRequests.isCurrent(requestToken) || boardLifecycleDisposed) return
    if (!trace?.states?.length) {
      ElMessage.warning({ message: t('app.traceHasNoStates'), type: 'warning' })
      return
    }
    closeResultDialog()
    closeHistoryPanel(false)
    activeFuzzingFinding.value = null
    savedTraces.value = [trace]
    traceAnimationState.value = {
      visible: true,
      selectedTraceIndex: 0,
      selectedStateIndex: 0,
      isPlaying: false
    }
    const currentTraceData = currentTrace.value
    if (currentTraceData) {
      highlightedTrace.value = {
        ...currentTraceData,
        selectedStateIndex: 0
      }
    }
  } catch (e: any) {
    if (!historyDetailRequests.isCurrent(requestToken) || boardLifecycleDisposed) return
    console.error('Failed to load trace:', e)
    ElMessage.error({ message: t('app.failedToLoadTrace'), type: 'error' })
  } finally {
    historyDetailRequests.finish(requestToken)
  }
}

const openFixForVerificationTrace = (trace: { id: number; violatedSpecId?: string }) => {
  if (!trace.violatedSpecId) {
    ElMessage.warning({ message: t('app.traceMissingViolatedSpec'), type: 'warning' })
    return
  }
  closeHistoryPanel()
  openFixDialog(trace.id, trace.violatedSpecId)
}

const selectAndPlaySimulationTrace = async (traceId: number) => {
  if (traceAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCounterexampleFirst'), type: 'warning' })
    return
  }
  if (simulationAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCurrentSimulationFirst'), type: 'warning' })
    return
  }
  if (isAnyRecommendationPanelVisible()) {
    ElMessage.warning({ message: t('app.closeRecommendationPanelsFirst'), type: 'warning' })
    return
  }
  if (!ensureLiveBoardEditorClosedForPlayback()) return

  const requestToken = historyDetailRequests.beginReplace()
  try {
    const trace = await simulationApi.getSimulation(traceId)
    if (!historyDetailRequests.isCurrent(requestToken) || boardLifecycleDisposed) return
    if (!trace?.states?.length) {
      ElMessage.warning({ message: t('app.simulationRunHasNoStates'), type: 'warning' })
      return
    }

    const result = {
      states: trace.states,
      steps: trace.steps,
      requestedSteps: trace.requestedSteps,
      logs: trace.logs || [],
      nusmvOutput: trace.nusmvOutput || '',
      modelComplete: trace.modelComplete,
      disabledRuleCount: trace.disabledRuleCount,
      generationIssues: getGenerationIssues(trace),
      isAttack: trace.isAttack === true,
      attackBudget: trace.attackBudget ?? 0,
      enablePrivacy: trace.enablePrivacy === true,
      modelSemantics: trace.modelSemantics,
      modelSnapshot: trace.modelSnapshot
    }

    closeHistoryPanel(false)
    lastSimulationResult.value = result
    simulationResult.value = null
    savedSimulationStates.value = [...trace.states]
    simulationAnimationState.value = {
      visible: true
    }
    highlightedTrace.value = {
      states: savedSimulationStates.value,
      selectedStateIndex: 0
    }
  } catch (e: any) {
    if (!historyDetailRequests.isCurrent(requestToken) || boardLifecycleDisposed) return
    console.error('Failed to load simulation trace:', e)
    ElMessage.error({ message: t('app.failedToLoadSimulationRun'), type: 'error' })
  } finally {
    historyDetailRequests.finish(requestToken)
  }
}

const deleteSimulationRun = async (run: SimulationTraceSummary) => {
  const traceId = run.id
  historyDetailRequests.invalidate()
  try {
    await ElMessageBox.confirm(
      t('app.deleteSimulationRunMessage', { time: formatRunTimestamp(run.createdAt) }),
      t('app.deleteSimulationRunTitle'),
      {
        confirmButtonText: t('app.delete'),
        cancelButtonText: t('app.cancel'),
        type: 'warning',
        appendTo: 'body',
        lockScroll: false
      }
    )
    await simulationApi.deleteSimulation(traceId)
    if (boardLifecycleDisposed) return
    simulationHistoryRequests.invalidate()
    simulationRuns.value = simulationRuns.value.filter(t => t.id !== traceId)
    ElMessage.success({ message: t('app.simulationRunDeleted'), type: 'success' })
  } catch (e: any) {
    if (e === 'cancel' || e === 'close') return
    if (boardLifecycleDisposed) return
    console.error('Failed to delete simulation trace:', e)
    const refreshed = await loadSimulationRuns(false)
    if (boardLifecycleDisposed) return
    if (refreshed && !simulationRuns.value.some(item => item.id === traceId)) {
      ElMessage.warning({ message: t('app.simulationDeleteOutcomeRefreshed'), type: 'warning' })
      return
    }
    ElMessage.error({
      message: localizedErrorMessage(e, t('app.failedToDeleteSimulationRun'), locale.value),
      type: 'error'
    })
  }
}

const fuzzingCompletionMessage = (run: AvailableFuzzingRunSummary | FuzzingRun): string => {
  if (run.outcome === 'FOUND_VIOLATION') {
    return t('app.fuzzSearchCompletedWithFindings', { count: run.findings.length })
  }
  if (run.outcome === 'BUDGET_EXHAUSTED') return t('app.fuzzNoViolationWithinBudget')
  return t('app.fuzzInconclusiveDetail')
}

const openFuzzingRun = async (runId: number) => {
  if (isModelPlaybackActive.value) {
    ElMessage.warning({ message: t('app.playbackReadOnlyCloseFirst'), type: 'warning' })
    return
  }
  const requestEpoch = ++fuzzingResultRequestEpoch
  const requestToken = historyDetailRequests.beginReplace()
  closeHistoryPanel(false)
  try {
    await nextTick()
    if (requestEpoch !== fuzzingResultRequestEpoch
      || !historyDetailRequests.isCurrent(requestToken)
      || boardLifecycleDisposed) return
    fuzzingError.value = null
    fuzzingResult.value = null
    fuzzingResultLoading.value = true
    showFuzzingResultDialog.value = true
    const [run] = await Promise.all([
      fuzzingApi.getRun(runId),
      refreshCurrentFuzzingModelFingerprint()
    ])
    if (requestEpoch !== fuzzingResultRequestEpoch
      || !historyDetailRequests.isCurrent(requestToken)
      || boardLifecycleDisposed) return
    presentFuzzingRun(run)
  } catch (e: any) {
    if (requestEpoch !== fuzzingResultRequestEpoch
      || !historyDetailRequests.isCurrent(requestToken)
      || boardLifecycleDisposed) return
    console.error('Failed to load fuzzing run:', e)
    showFuzzingResultDialog.value = false
    fuzzingError.value = null
    ElMessage.error({
      message: extractApiErrorMessage(e, t('app.failedToLoadFuzzingRun')),
      type: 'error'
    })
  } finally {
    if (requestEpoch === fuzzingResultRequestEpoch) {
      fuzzingResultLoading.value = false
      if (!historyDetailRequests.isCurrent(requestToken) && !fuzzingResult.value) {
        showFuzzingResultDialog.value = false
      }
    }
    historyDetailRequests.finish(requestToken)
  }
}

const closeFuzzingResult = () => {
  fuzzingResultRequestEpoch += 1
  showFuzzingResultDialog.value = false
  fuzzingResult.value = null
  fuzzingError.value = null
  fuzzingResultLoading.value = false
}

const deleteFuzzingRun = async (run: FuzzingRunSummary) => {
  historyDetailRequests.invalidate()
  try {
    await ElMessageBox.confirm(
      t('app.deleteFuzzingRunMessage', { time: formatRunTimestamp(run.completedAt || run.createdAt) }),
      t('app.deleteFuzzingRunTitle'),
      {
        confirmButtonText: t('app.delete'),
        cancelButtonText: t('app.cancel'),
        type: 'warning',
        appendTo: 'body',
        lockScroll: false
      }
    )
    await fuzzingApi.deleteRun(run.id)
    if (boardLifecycleDisposed) return
    fuzzingHistoryRequests.invalidate()
    fuzzingRuns.value = fuzzingRuns.value.filter(item => item.id !== run.id)
    fuzzingRunsPage.value = 0
    fuzzingRunsHasMore.value = false
    const refreshed = await loadFuzzingRuns(false)
    if (boardLifecycleDisposed) return
    if (fuzzingResult.value?.id === run.id) closeFuzzingResult()
    if (!refreshed) {
      ElMessage.warning({ message: t('app.fuzzingRunDeletedRefreshPending'), type: 'warning' })
      return
    }
    ElMessage.success({ message: t('app.fuzzingRunDeleted'), type: 'success' })
  } catch (e: any) {
    if (e === 'cancel' || e === 'close') return
    if (boardLifecycleDisposed) return
    console.error('Failed to delete fuzzing run:', e)
    const refreshed = await loadFuzzingRuns(false)
    if (boardLifecycleDisposed) return
    if (refreshed && !fuzzingRuns.value.some(item => item.id === run.id)) {
      ElMessage.warning({ message: t('app.fuzzingDeleteOutcomeRefreshed'), type: 'warning' })
      return
    }
    ElMessage.error({
      message: t('app.failedToDeleteFuzzingRun'),
      type: 'error'
    })
  }
}

const selectAndPlayFuzzingFinding = async (findingId: number, runId?: number) => {
  if (simulationAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCurrentSimulationFirst'), type: 'warning' })
    return
  }
  if (traceAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCounterexampleFirst'), type: 'warning' })
    return
  }
  if (isAnyRecommendationPanelVisible()) {
    ElMessage.warning({ message: t('app.closeRecommendationPanelsFirst'), type: 'warning' })
    return
  }
  if (!ensureLiveBoardEditorClosedForPlayback()) return

  const requestToken = historyDetailRequests.beginReplace()
  try {
    const existingRun = runId
      ? fuzzingRuns.value.find(run => run.id === runId)
      : fuzzingResult.value
    const [finding, resolvedRun] = await Promise.all([
      fuzzingApi.getFinding(findingId),
      existingRun ? Promise.resolve(existingRun) : (runId ? fuzzingApi.getRun(runId) : Promise.resolve(null))
    ])
    if (!historyDetailRequests.isCurrent(requestToken) || boardLifecycleDisposed) return
    if (!finding.states.length) {
      ElMessage.warning({ message: t('app.fuzzFindingHasNoStates'), type: 'warning' })
      return
    }
    if (!resolvedRun || resolvedRun.dataAvailable === false || !resolvedRun.modelSnapshot) {
      throw new Error(t('app.fuzzFindingSnapshotUnavailable'))
    }
    assertFuzzingFindingBelongsToRun(finding, resolvedRun.id, 'Fuzz finding replay')

    const trace: Trace = {
      id: finding.id,
      violatedSpecId: finding.violatedSpecId,
      violatedSpec: finding.violatedSpec,
      checkedExpression: '',
      modelComplete: false,
      disabledRuleCount: 0,
      skippedSpecCount: 0,
      generationIssues: [],
      states: finding.states,
      modelSnapshot: resolvedRun.modelSnapshot,
      createdAt: finding.createdAt
    }

    closeHistoryPanel(false)
    closeFuzzingResult()
    activeFuzzingFinding.value = finding
    savedTraces.value = [trace]
    traceAnimationState.value = {
      visible: true,
      selectedTraceIndex: 0,
      selectedStateIndex: 0,
      isPlaying: false
    }
    highlightedTrace.value = { ...trace, selectedStateIndex: 0 }
  } catch (e: any) {
    if (!historyDetailRequests.isCurrent(requestToken) || boardLifecycleDisposed) return
    console.error('Failed to load fuzzing finding:', e)
    ElMessage.error({
      message: extractApiErrorMessage(e, t('app.failedToLoadFuzzingFinding')),
      type: 'error'
    })
  } finally {
    historyDetailRequests.finish(requestToken)
  }
}

type FuzzVerificationHandoff = {
  runId: number
  specificationId?: string
  specificationLabel?: string
  targetPresent: boolean
  boardDrifted: boolean
}

const fuzzVerificationHandoff = ref<FuzzVerificationHandoff | null>(null)

const availableFuzzRunForFinding = (finding: FuzzingFindingSummary | FuzzingFinding) => {
  if (fuzzingResult.value?.id === finding.fuzzTaskId) return fuzzingResult.value
  const historyRun = fuzzingRuns.value.find(run => run.id === finding.fuzzTaskId)
  return historyRun?.dataAvailable ? historyRun : null
}

const openFormalVerificationForFuzzFinding = (finding: FuzzingFindingSummary | FuzzingFinding) => {
  const sourceRun = availableFuzzRunForFinding(finding)
  const specificationLabel = finding.violatedSpec?.templateLabel
    || finding.violatedSpec?.formula
    || ('specificationLabel' in finding ? finding.specificationLabel : '')
    || finding.violatedSpecId
  fuzzVerificationHandoff.value = {
    runId: finding.fuzzTaskId,
    specificationId: finding.violatedSpecId,
    specificationLabel,
    targetPresent: specifications.value.some(spec => spec.id === finding.violatedSpecId),
    boardDrifted: sourceRun ? fuzzRunHasBoardDrift(sourceRun) : true
  }
  closeHistoryPanel()
  closeFuzzingResult()
  showSimulationPanel.value = false
  showFuzzingPanel.value = false
  showVerificationPanel.value = true
}

const openFormalVerificationForCurrentBoard = () => {
  const sourceRun = fuzzingResult.value
  fuzzVerificationHandoff.value = sourceRun ? {
    runId: sourceRun.id,
    targetPresent: true,
    boardDrifted: fuzzingResultBoardDrifted.value
  } : null
  closeHistoryPanel()
  closeFuzzingResult()
  showSimulationPanel.value = false
  showFuzzingPanel.value = false
  showVerificationPanel.value = true
}

const closeVerificationPanel = () => {
  showVerificationPanel.value = false
  fuzzVerificationHandoff.value = null
  void nextTick(() => verificationActionButtonRef.value?.focus())
}

const reuseFuzzingSettings = () => {
  const run = fuzzingResult.value
  if (!run) return
  const eligibleCurrentIds = new Set(knownFuzzEligibleSpecifications.value.map(spec => spec.id))
  const usedFrozenAllTargets = run.targetSpecIds.length === 0
  const historicalTargetIds = usedFrozenAllTargets
    ? [...new Set([
        ...run.eligibility.eligibleSpecIds,
        ...run.eligibility.ineligibleSpecs.map(issue => issue.specId)
      ])]
    : [...run.targetSpecIds]
  const unavailableTargetCount = historicalTargetIds.filter(id => !eligibleCurrentIds.has(id)).length
  fuzzingForm.explorationMode = run.explorationMode
  fuzzingForm.maxIterations = run.maxIterations
  fuzzingForm.pathLength = run.pathLength
  fuzzingForm.populationSize = run.populationSize
  fuzzingForm.seed = run.effectiveSeed
  fuzzingForm.targetSelectionMode = 'EXPLICIT'
  // Keep unavailable explicit IDs visible so the user, not filtering code, chooses a replacement scope.
  fuzzingForm.targetSpecIds = historicalTargetIds
  fuzzingSettingsNotice.value = usedFrozenAllTargets
    ? t('app.fuzzSettingsReusedAllTargets')
    : unavailableTargetCount > 0
      ? t('app.fuzzSettingsReusedWithMissingTargets', { count: unavailableTargetCount })
      : t('app.fuzzSettingsReused')
  closeFuzzingResult()
  closeHistoryPanel()
  showSimulationPanel.value = false
  showVerificationPanel.value = false
  showFuzzingPanel.value = true
}

// Floating panel visibility state
const showVerificationPanel = ref(false)
const verificationPanelCloseButtonRef = ref<HTMLButtonElement | null>(null)
const verificationActionButtonRef = ref<HTMLButtonElement | null>(null)

watch(showVerificationPanel, visible => {
  if (!visible) return
  void nextTick(() => verificationPanelCloseButtonRef.value?.focus())
})

// 异步模拟任务状态
const asyncSimulationTask = ref<{
  taskId: number | null
  progress: number
  status: string
}>({
  taskId: null,
  progress: 0,
  status: ''
})
const asyncSimulationActive = ref(false)
const cancellingSimulationTask = ref(false)
const simulationCancelRequested = ref(false)

const notifyTaskCancellationResult = (
  kind: 'verification' | 'fuzzing' | 'simulation',
  result: TaskCancellationResult
) => {
  const task = t(kind === 'verification'
    ? 'app.verificationTaskName'
    : kind === 'fuzzing' ? 'app.fuzzTaskName' : 'app.simulationTaskName')
  switch (result.cancellationOutcome) {
    case 'ACCEPTED':
      ElMessage.info({
        message: t(result.executionMayStillBeStopping
          ? 'app.taskCancellationAcceptedStopping'
          : 'app.taskCancellationAccepted', { task }),
        type: 'info'
      })
      break
    case 'ALREADY_CANCELLED':
      ElMessage.info({ message: t('app.taskAlreadyCancelled', { task }), type: 'info' })
      break
    case 'ALREADY_COMPLETED':
      ElMessage.warning({ message: t('app.taskAlreadyCompleted', { task }), type: 'warning' })
      break
    case 'ALREADY_FAILED':
      ElMessage.warning({ message: t('app.taskAlreadyFailed', { task }), type: 'warning' })
      break
    default:
      ElMessage.warning({ message: t('app.taskCancellationNotAccepted', { task }), type: 'warning' })
  }
}

// Floating panel visibility state
const showSimulationPanel = ref(false)

// Fix dialog 状态
const showFixDialog = ref(false)
const fixTraceId = ref<number | null>(null)
const fixViolatedSpecId = ref<string>('')

// 打开 Fix 弹窗
const openFixDialog = (traceId: number, violatedSpecId: string) => {
  fixTraceId.value = traceId
  fixViolatedSpecId.value = violatedSpecId
  showFixDialog.value = true
}

const cancelAsyncVerification = async () => {
  const taskId = asyncVerificationTask.value.taskId
  if (!taskId || cancellingVerificationTask.value) return

  verificationCancelRequested.value = true
  cancellingVerificationTask.value = true
  asyncVerificationTask.value.status = t('app.taskCancelling')
  try {
    const result = await boardApi.cancelTask(taskId)
    if (boardLifecycleDisposed) return
    notifyTaskCancellationResult('verification', result)
    if (result.cancellationAccepted || result.cancellationOutcome === 'ALREADY_CANCELLED') {
      verificationCancelRequested.value = true
    } else {
      verificationCancelRequested.value = false
    }
  } catch (error: any) {
    if (boardLifecycleDisposed) return
    verificationCancelRequested.value = false
    const msg = localizedErrorMessage(error, t('app.failedToCancelVerificationTask'), locale.value)
    ElMessage.error({ message: msg, type: 'error' })
  } finally {
    cancellingVerificationTask.value = false
  }
}

const cancelAsyncSimulation = async () => {
  const taskId = asyncSimulationTask.value.taskId
  if (!taskId || cancellingSimulationTask.value) return

  simulationCancelRequested.value = true
  cancellingSimulationTask.value = true
  asyncSimulationTask.value.status = t('app.taskCancelling')
  try {
    const result = await simulationApi.cancelTask(taskId)
    if (boardLifecycleDisposed) return
    notifyTaskCancellationResult('simulation', result)
    if (result.cancellationAccepted || result.cancellationOutcome === 'ALREADY_CANCELLED') {
      simulationCancelRequested.value = true
    } else {
      simulationCancelRequested.value = false
    }
  } catch (error: any) {
    if (boardLifecycleDisposed) return
    simulationCancelRequested.value = false
    const msg = localizedErrorMessage(error, t('app.failedToCancelSimulationTask'), locale.value)
    ElMessage.error({ message: msg, type: 'error' })
  } finally {
    cancellingSimulationTask.value = false
  }
}

const cancelAsyncFuzzing = async () => {
  const taskId = asyncFuzzingTask.value.taskId
  if (!taskId || cancellingFuzzingTask.value) return

  fuzzingCancelRequested.value = true
  cancellingFuzzingTask.value = true
  asyncFuzzingTask.value.status = t('app.taskCancelling')
  try {
    const result = await fuzzingApi.cancelTask(taskId)
    if (boardLifecycleDisposed) return
    notifyTaskCancellationResult('fuzzing', result)
    fuzzingCancelRequested.value = result.cancellationAccepted
      || result.cancellationOutcome === 'ALREADY_CANCELLED'
  } catch (error: any) {
    if (boardLifecycleDisposed) return
    fuzzingCancelRequested.value = false
    console.error('Failed to cancel fuzzing task:', error)
    ElMessage.error({
      message: t('app.failedToCancelFuzzingTask'),
      type: 'error'
    })
  } finally {
    cancellingFuzzingTask.value = false
  }
}

// Fix 应用后的回调
let pendingFixRefreshPromise: Promise<boolean> | null = null

const handleFixApplied = (result: FixApplyResult) => {
  const refreshPromise = enqueueBoardMutation(async () => {
    const refreshed = await refreshRules()
    if (refreshed) return true

    rules.value = result.rules
    syncRuleDerivedEdges()
    ElMessage.warning(t('app.fixAppliedRefreshFallback'))
    return false
  })
  pendingFixRefreshPromise = refreshPromise
  const clearPendingRefresh = () => {
    if (pendingFixRefreshPromise === refreshPromise) {
      pendingFixRefreshPromise = null
    }
  }
  void refreshPromise.then(clearPendingRefresh, clearPendingRefresh)
}

const handleFixOutcomeUncertain = async () => {
  const refreshPromise = enqueueBoardMutation(() => refreshRules())
  pendingFixRefreshPromise = refreshPromise
  try {
    const refreshed = await refreshPromise
    ElMessage.warning(refreshed
      ? t('app.fixApplyOutcomeUnconfirmedAfterRefresh')
      : t('app.fixApplyOutcomeUnknownRefreshFailed'))
  } finally {
    if (pendingFixRefreshPromise === refreshPromise) {
      pendingFixRefreshPromise = null
    }
  }
}

const waitForPendingFixRefresh = async () => {
  if (pendingFixRefreshPromise) {
    await pendingFixRefreshPromise
  }
}

// 面板互斥切换函数
const togglePanel = (panel: 'simulation' | 'fuzzing' | 'verification') => {
  if (isModelPlaybackActive.value) {
    ElMessage.warning({ message: t('app.playbackReadOnlyCloseFirst'), type: 'warning' })
    return
  }
  if (isAnyRecommendationRunning()) {
    ElMessage.warning({ message: t('app.recommendationGenerationInProgress'), type: 'warning' })
    return
  }

  closeResultSurfaces()
  closeHistoryPanel()
  closeRecommendationPanel()
  closeDeviceRecommendationPanel()
  closeSpecRecommendationPanel()
  closeScenarioRecommendationPanel()
  
  if (panel === 'simulation') {
    if (showSimulationPanel.value) {
      showSimulationPanel.value = false
    } else {
      showSimulationPanel.value = true
      showFuzzingPanel.value = false
      showVerificationPanel.value = false
    }
  } else if (panel === 'fuzzing') {
    if (showFuzzingPanel.value) {
      showFuzzingPanel.value = false
    } else {
      showFuzzingPanel.value = true
      showSimulationPanel.value = false
      showVerificationPanel.value = false
    }
  } else {
    if (showVerificationPanel.value) {
      showVerificationPanel.value = false
    } else {
      showVerificationPanel.value = true
      showSimulationPanel.value = false
      showFuzzingPanel.value = false
    }
  }
}

const openSimulationFromActionDock = () => {
  togglePanel('simulation')
}

const openVerificationFromActionDock = () => {
  fuzzVerificationHandoff.value = null
  togglePanel('verification')
}

const openFuzzingFromActionDock = () => {
  if (isSceneReplacementInProgress.value) {
    ElMessage.warning({ message: t('app.sceneReplacementInProgress'), type: 'warning' })
    return
  }
  // Dismiss earlier scene/task notices before placing a tool panel beneath them.
  ElMessage.closeAll()
  if (!isFuzzing.value) fuzzingWatchedTask.value = null
  fuzzingSettingsNotice.value = null
  togglePanel('fuzzing')
}

const openHistoryFromActionDock = () => {
  if (unreadFuzzNotificationCount.value > 0) {
    const layer: HistoryLayer = unreadFailedFuzzCount.value > 0 ? 'tasks' : 'results'
    if (layer === 'results') activeHistoryResultFilter.value = 'fuzzing'
    void toggleHistoryPanel(layer)
    return
  }
  void toggleHistoryPanel()
}

const openRuleRecommendationsFromActionDock = () => {
  openRuleRecommendationPanel()
}

const openDeviceRecommendationsFromActionDock = () => {
  openDeviceRecommendationPanel()
}

const openSpecRecommendationsFromActionDock = () => {
  openSpecRecommendationPanel()
}

const openScenarioRecommendationsFromActionDock = () => {
  openScenarioRecommendationPanel()
}

// 模拟时间轴动画状态
const simulationAnimationState = ref({
  visible: false
})

// 独立保存的模拟 states 数据（用于对话框关闭后）
const savedSimulationStates = ref<SimulationState[]>([])

// 反例路径高亮状态
const highlightedTrace = ref<any>(null)

// 反例路径动画控制状态
const traceAnimationState = ref({
  visible: false,
  selectedTraceIndex: 0,
  selectedStateIndex: 0,
  isPlaying: false
})

// 独立保存的 traces 数据（用于对话框关闭后）
const savedTraces = ref<any[]>([])

// Playback is a read-only view over a persisted runtime snapshot. Derive the lock from
// the visible playback surfaces so no entry point can forget to acquire or release it.
const isAnimationLocked = computed(() =>
  traceAnimationState.value.visible || simulationAnimationState.value.visible
)
const isModelPlaybackActive = isAnimationLocked

const playbackChangesDismissedKey = ref<string | null>(null)
const playbackChangePosition = ref({ x: 0, y: 0 })

const activePlaybackKind = computed<'simulation' | 'counterexample' | 'fuzzing' | null>(() => {
  if (simulationAnimationState.value.visible) return 'simulation'
  if (traceAnimationState.value.visible && activeFuzzingFinding.value) return 'fuzzing'
  if (traceAnimationState.value.visible) return 'counterexample'
  return null
})

type ActivePlaybackState = {
  devices?: TraceDevice[]
  envVariables?: TraceVariable[]
  triggeredRules?: TraceTriggeredRule[]
  compromisedAutomationLinks?: TraceTriggeredRule[]
}

const activePlaybackStates = computed<ActivePlaybackState[]>(() => {
  if (!isModelPlaybackActive.value || !highlightedTrace.value?.states) return []
  return highlightedTrace.value.states
})

const activePlaybackStateIndex = computed(() => {
  const selected = Number(highlightedTrace.value?.selectedStateIndex ?? 0)
  const lastIndex = Math.max(activePlaybackStates.value.length - 1, 0)
  return Math.min(Math.max(Number.isFinite(selected) ? Math.trunc(selected) : 0, 0), lastIndex)
})

const activePlaybackChanges = computed<PlaybackDeviceChange[]>(() => {
  if (!activePlaybackKind.value || activePlaybackStateIndex.value <= 0) return []
  const currentState = activePlaybackStates.value[activePlaybackStateIndex.value]
  const previousState = activePlaybackStates.value[activePlaybackStateIndex.value - 1]
  if (!currentState?.devices || !previousState?.devices) return []

  return currentState.devices
    .map(device => {
      const previous = previousState.devices?.find(candidate =>
        normalizePlaybackDeviceId(candidate.deviceId) === normalizePlaybackDeviceId(device.deviceId)
      )
      return playbackDeviceChangeDetails(device, previous)
    })
    .filter((change): change is PlaybackDeviceChange => change !== null)
})

const activePlaybackEnvironmentChanges = computed<PlaybackEnvironmentChange[]>(() => {
  if (!activePlaybackKind.value || activePlaybackStateIndex.value <= 0) return []
  const currentState = activePlaybackStates.value[activePlaybackStateIndex.value]
  const previousState = activePlaybackStates.value[activePlaybackStateIndex.value - 1]
  return playbackEnvironmentChangeDetails(currentState?.envVariables, previousState?.envVariables)
})

const activePlaybackTriggeredRules = computed<TraceTriggeredRule[]>(() =>
  activePlaybackStates.value[activePlaybackStateIndex.value]?.triggeredRules || [])

const activeFuzzingStepInputEvents = computed<Array<FuzzingInputEvent & { targetLabel?: string }>>(() => {
  const finding = activeFuzzingFinding.value
  if (!finding) return []
  const state = activePlaybackStates.value[activePlaybackStateIndex.value]
  return finding.inputEvents
    .filter(event => event.step === activePlaybackStateIndex.value)
    .map(event => {
      if (event.kind !== 'DEVICE_VARIABLE' && event.kind !== 'DEVICE_STATE') return event
      const device = state?.devices?.find(candidate =>
        normalizePlaybackDeviceId(candidate.deviceId) === normalizePlaybackDeviceId(event.targetId))
      return { ...event, targetLabel: device?.deviceLabel || event.targetId }
    })
})

const firstFuzzingViolationStateNumber = computed(() =>
  activeFuzzingFinding.value ? activeFuzzingFinding.value.firstViolationStep + 1 : undefined)

const activePlaybackCompromisedLinks = computed<TraceTriggeredRule[]>(() =>
  activePlaybackStates.value[activePlaybackStateIndex.value]?.compromisedAutomationLinks || [])

const activePlaybackTriggeredRuleIds = computed(() => new Set(
  activePlaybackTriggeredRules.value
    .map(rule => rule.ruleId == null ? '' : String(rule.ruleId))
    .filter(Boolean)
))

const activePlaybackCompromisedRuleIds = computed(() => new Set(
  activePlaybackCompromisedLinks.value
    .map(rule => rule.ruleId == null ? '' : String(rule.ruleId))
    .filter(Boolean)
))

const activePlaybackAnimatedEdgeCount = computed(() => allEdges.value.filter(edge => {
  const ruleId = edge.ruleId == null ? '' : String(edge.ruleId)
  return ruleId
    && activePlaybackTriggeredRuleIds.value.has(ruleId)
    && !activePlaybackCompromisedRuleIds.value.has(ruleId)
}).length)

const activePlaybackCompromisedEdgeCount = computed(() => allEdges.value.filter(edge => {
  const ruleId = edge.ruleId == null ? '' : String(edge.ruleId)
  return ruleId && activePlaybackCompromisedRuleIds.value.has(ruleId)
}).length)

const activePlaybackChangeKey = computed(() => {
  if (!activePlaybackKind.value || activePlaybackStates.value.length === 0) return null
  return `${activePlaybackKind.value}:${activePlaybackStateIndex.value}`
})

const showPlaybackChangePopover = computed(() =>
  activePlaybackChangeKey.value !== null
  && playbackChangesDismissedKey.value !== activePlaybackChangeKey.value
)

const dismissPlaybackChanges = () => {
  playbackChangesDismissedKey.value = activePlaybackChangeKey.value
}

const movePlaybackChanges = (position: { x: number; y: number }) => {
  playbackChangePosition.value = position
}

const resetPlaybackChanges = () => {
  playbackChangesDismissedKey.value = null
  playbackChangePosition.value = { x: 0, y: 0 }
}

watch(activePlaybackKind, resetPlaybackChanges)

const isLiveBoardEditorVisible = computed(() =>
  templateInstanceDialogVisible.value ||
  dialogVisible.value ||
  renameDialogVisible.value ||
  deleteConfirmDialogVisible.value ||
  ruleBuilderVisible.value ||
  showFixDialog.value
)

const ensureLiveBoardEditorClosedForPlayback = (): boolean => {
  if (chatStore.state.streaming) {
    ElMessage.warning({ message: t('app.finishAssistantBeforePlayback'), type: 'warning' })
    return false
  }
  if (!isLiveBoardEditorVisible.value) return true
  ElMessage.warning({ message: t('app.closeLiveEditorBeforePlayback'), type: 'warning' })
  return false
}

const notifyAutomaticPlaybackDeferred = () => {
  ElMessage.info({ message: t('app.simulationPlaybackDeferredForEditor'), type: 'info' })
}

const ensurePlaybackClosedForMutation = (): boolean => {
  if (isSceneReplacementInProgress.value) {
    ElMessage.warning({ message: t('app.sceneReplacementInProgress'), type: 'warning' })
    return false
  }
  if (!isModelPlaybackActive.value) return true
  ElMessage.warning({ message: t('app.playbackReadOnlyCloseFirst'), type: 'warning' })
  return false
}

let playInterval: ReturnType<typeof setInterval> | null = null

const isCanvasMapHiddenByOverlay = computed(() =>
  showVerificationPanel.value ||
  showSimulationPanel.value ||
  showFuzzingPanel.value ||
  showHistoryPanel.value ||
  showRecommendationPanel.value ||
  showDeviceRecommendationPanel.value ||
  showSpecRecommendationPanel.value ||
  showScenarioRecommendationPanel.value ||
  traceAnimationState.value.visible ||
  simulationAnimationState.value.visible ||
  showFixDialog.value
)

// 当前选中的 trace
const currentTrace = computed(() => {
  // 优先使用 savedTraces
  if (savedTraces.value.length > 0) {
    return savedTraces.value[traceAnimationState.value.selectedTraceIndex] || null
  }
  return verificationResult.value?.traces?.[traceAnimationState.value.selectedTraceIndex] || null
})

// 所有状态数量
const totalStates = computed(() => {
  return currentTrace.value?.states?.length || 0
})

// Verification context of the trace currently being viewed, derived from the trace's own snapshot
// (backend TraceDto) rather than the live verification form.
const activeTraceContext = computed(() => {
  return deriveTraceContext(currentTrace.value)
})

const currentTraceState = computed(() => {
  const trace = currentTrace.value
  if (!trace?.states) return null
  return trace.states[traceAnimationState.value.selectedStateIndex] || null
})

const previousTraceState = computed(() => {
  const trace = currentTrace.value
  const previousIndex = traceAnimationState.value.selectedStateIndex - 1
  if (!trace?.states || previousIndex < 0) return null
  return trace.states[previousIndex] || null
})

const currentTraceEnvironmentVariables = computed(() => currentTraceState.value?.envVariables || [])
const currentTraceTriggeredRules = computed(() => currentTraceState.value?.triggeredRules || [])
const currentTraceCompromisedAutomationLinks = computed(() => currentTraceState.value?.compromisedAutomationLinks || [])
const currentTraceCompromisedPointCount = computed(() => {
  const raw = currentTraceState.value?.globalVariables
    ?.find((variable: { name: string; value: string }) => variable.name === 'compromisedPointCount')?.value
  const parsed = Number.parseInt(String(raw ?? ''), 10)
  return Number.isFinite(parsed) ? parsed : null
})
const currentTraceDevices = computed(() => currentTraceState.value?.devices || [])
const currentBoardRuleIds = computed(() => rules.value
  .map(rule => rule.id)
  .filter((id): id is string => !!id)
  .map(String))
const currentBoardDeviceIds = computed(() => nodes.value.map(node => normalizePlaybackDeviceId(node.id)))
const currentBoardDeviceIdSet = computed(() => new Set(currentBoardDeviceIds.value))

const previousTraceDevice = (device: TraceDevice) => previousTraceState.value?.devices?.find((candidate: TraceDevice) =>
  normalizePlaybackDeviceId(candidate.deviceId) === normalizePlaybackDeviceId(device.deviceId)
)

const traceDeviceChanged = (device: TraceDevice) =>
  traceAnimationState.value.selectedStateIndex > 0
  && playbackDeviceChanged(device, previousTraceDevice(device))

const traceDeviceExistsOnBoard = (device: TraceDevice) =>
  currentBoardDeviceIdSet.value.has(normalizePlaybackDeviceId(device.deviceId))

const traceDeviceSummary = (device: TraceDevice) => {
  const parts = playbackDeviceSummaryParts(device)
  return parts.length > 0 ? parts.join(' · ') : t('app.unknown')
}

const traceDeviceSecurityFacts = (device: TraceDevice) => playbackDeviceSecurityFacts(device)

const traceTriggeredRuleLabel = (rule: { ruleId?: string | null; ruleLabel?: string | null }, index: number) => {
  if (rule.ruleLabel?.trim()) return rule.ruleLabel.trim()
  const currentRule = rule.ruleId != null
    ? rules.value.find(candidate => String(candidate.id) === String(rule.ruleId))
    : undefined
  return currentRule?.name || t('app.ruleNumber', { number: index + 1 })
}

const traceTriggeredRuleExistsOnBoard = (rule: { ruleId?: string | null }) =>
  rule.ruleId != null && currentBoardRuleIds.value.includes(String(rule.ruleId))

const selectedTraceStateNumber = computed({
  get: () => traceAnimationState.value.selectedStateIndex + 1,
  set: (value: number) => {
    if (!Number.isFinite(value)) return
    goToState(Math.trunc(value) - 1)
  }
})

const selectedTraceStateRangeIndex = computed({
  get: () => traceAnimationState.value.selectedStateIndex,
  set: (value: number) => {
    if (!Number.isFinite(value)) return
    goToState(Math.trunc(value))
  }
})

const getPreviousTraceEnvValue = (name: string) =>
  previousTraceState.value?.envVariables?.find((variable: any) => variable.name === name)?.value

const traceEnvironmentVariableChanged = (name: string, value: string) =>
  traceAnimationState.value.selectedStateIndex > 0 && getPreviousTraceEnvValue(name) !== value

const traceEnvironmentVariableTitle = (name: string, value: string) => {
  const previous = getPreviousTraceEnvValue(name)
  if (previous === undefined || previous === value) {
    return `${name}: ${value}`
  }
  return `${name}: ${previous} -> ${value}`
}

// 选择并播放指定索引的反例路径动画
const selectAndPlayTrace = (traceIndex: number) => {
  // 互斥检查：如果模拟动画正在显示，则不允许打开反例路径动画
  if (simulationAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCurrentSimulationFirst'), type: 'warning' })
    return
  }
  
  if (isAnyRecommendationPanelVisible()) {
    ElMessage.warning({ message: t('app.closeRecommendationPanelsFirst'), type: 'warning' })
    return
  }
  if (!ensureLiveBoardEditorClosedForPlayback()) return
  
  if (verificationResult.value?.traces?.length > 0 && traceIndex < verificationResult.value.traces.length) {
    resetPlaybackChanges()
    activeFuzzingFinding.value = null
    // 保存 traces 数据到独立变量
    savedTraces.value = [...verificationResult.value.traces]
    
    // 关闭验证结果对话框
    closeResultDialog()
    
    // 设置选中的 trace 索引
    traceAnimationState.value = {
      visible: true,
      selectedTraceIndex: traceIndex,
      selectedStateIndex: 0,
      isPlaying: false
    }
    
    // 高亮第一个状态
    const trace = currentTrace.value
    if (trace) {
      highlightedTrace.value = {
        ...trace,
        selectedStateIndex: 0
      }
    }
  }
}

// 关闭反例路径动画
const closeTraceAnimation = () => {
  stopTraceAnimation()
  traceAnimationState.value.visible = false
  highlightedTrace.value = null
  activeFuzzingFinding.value = null
  resetPlaybackChanges()
}

// 选择违规规约
// 跳转到指定状态
const goToState = (index: number) => {
  const lastIndex = Math.max(totalStates.value - 1, 0)
  traceAnimationState.value.selectedStateIndex = Math.min(Math.max(index, 0), lastIndex)
  const trace = currentTrace.value
  if (trace) {
    highlightedTrace.value = {
      ...trace,
      selectedStateIndex: traceAnimationState.value.selectedStateIndex
    }
  }
}

const handleTraceStateKeydown = (event: KeyboardEvent, index: number) => {
  const keyToIndex: Record<string, number> = {
    ArrowLeft: index - 1,
    ArrowDown: index - 1,
    ArrowRight: index + 1,
    ArrowUp: index + 1,
    Home: 0,
    End: totalStates.value - 1
  }
  if (!(event.key in keyToIndex)) return
  event.preventDefault()
  const lastIndex = Math.max(totalStates.value - 1, 0)
  const nextIndex = Math.min(Math.max(keyToIndex[event.key], 0), lastIndex)
  goToState(nextIndex)
  revealTraceStateButton(nextIndex, true)
}

const getTraceStateAriaLabel = (index: number) => {
  const base = `${t('app.traceVisualization.state', { index: index + 1 })} (${index + 1}/${totalStates.value})`
  return activeFuzzingFinding.value?.firstViolationStep === index
    ? `${base}, ${t('app.fuzzFirstViolation')}`
    : base
}

const revealTraceStateButton = (index: number, focus = false) => {
  void nextTick(() => {
    const button = document.querySelector<HTMLButtonElement>(`[data-testid="trace-timeline-state-${index}"]`)
    button?.scrollIntoView({ behavior: 'smooth', block: 'nearest', inline: 'center' })
    if (focus) {
      button?.focus()
    }
  })
}

const selectTraceStateFromTimelinePointer = (event: PointerEvent) => {
  if (totalStates.value <= 1) return
  if (event.target instanceof Element && event.target.closest('button')) return
  const target = event.currentTarget as HTMLElement
  const rect = target.getBoundingClientRect()
  const trackLeft = rect.left + 8
  const trackWidth = Math.max(1, rect.width - 16)
  const ratio = Math.min(1, Math.max(0, (event.clientX - trackLeft) / trackWidth))
  const nextIndex = Math.round(ratio * (totalStates.value - 1))
  goToState(nextIndex)
  revealTraceStateButton(nextIndex, true)
}

// 播放/停止动画
const toggleTraceAnimation = () => {
  if (traceAnimationState.value.isPlaying) {
    stopTraceAnimation()
  } else {
    startTraceAnimation()
  }
}

const startTraceAnimation = () => {
  if (traceAnimationState.value.isPlaying) return
  if (totalStates.value <= 1) return

  const trace = currentTrace.value
  if (!trace) return

  if (traceAnimationState.value.selectedStateIndex >= totalStates.value - 1) {
    goToState(0)
  }
  
  traceAnimationState.value.isPlaying = true
  playInterval = setInterval(() => {
    const activeTrace = currentTrace.value
    if (!activeTrace) {
      stopTraceAnimation()
      return
    }
    if (traceAnimationState.value.selectedStateIndex < totalStates.value - 1) {
      traceAnimationState.value.selectedStateIndex++
      highlightedTrace.value = {
        ...activeTrace,
        selectedStateIndex: traceAnimationState.value.selectedStateIndex
      }
      if (traceAnimationState.value.selectedStateIndex >= totalStates.value - 1) {
        stopTraceAnimation()
      }
    } else {
      // 到达最后一个状态时停止播放，不循环
      stopTraceAnimation()
    }
  }, 1500)
}

const stopTraceAnimation = () => {
  traceAnimationState.value.isPlaying = false
  if (playInterval) {
    clearInterval(playInterval)
    playInterval = null
  }
}

watch(
  () => traceAnimationState.value.selectedStateIndex,
  index => {
    if (traceAnimationState.value.visible) {
      revealTraceStateButton(index)
    }
  }
)

// 当前规约的格式化显示
const formattedSpec = computed(() => {
  if (!currentTrace.value?.violatedSpec) return ''
  return formatTraceSpec(currentTrace.value.violatedSpec, t)
})

// 高亮反例路径
const handleHighlightTrace = (trace: any) => {
  if (trace && trace.states) {
    highlightedTrace.value = {
      states: trace.states,
      selectedStateIndex: trace.selectedStateIndex
    }
  }
}

// 清除高亮
// ==== Simulation Timeline Animation Logic ====

// 打开模拟时间轴动画
const openSimulationTimeline = () => {
  // 互斥检查：如果反例路径动画正在显示，则不允许打开模拟动画
  if (traceAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCounterexampleFirst'), type: 'warning' })
    return
  }
  
  if (isAnyRecommendationPanelVisible()) {
    ElMessage.warning({ message: t('app.closeRecommendationPanelsFirst'), type: 'warning' })
    return
  }
  if (!ensureLiveBoardEditorClosedForPlayback()) return
  
  if (simulationResult.value?.states?.length > 0) {
    resetPlaybackChanges()
    // 保存模拟 states 数据到独立变量
    savedSimulationStates.value = [...simulationResult.value.states]
    
    // 关闭模拟结果对话框
    simulationResult.value = null
    
    // 打开模拟时间轴动画
    simulationAnimationState.value = {
      visible: true
    }
    
    // 高亮第一个状态
    highlightedTrace.value = {
      states: savedSimulationStates.value,
      selectedStateIndex: 0
    }
  }
}

const handleSimulationTimelineAction = () => {
  if (simulationAnimationState.value.visible) {
    simulationResult.value = null
    simulationError.value = null
    return
  }
  openSimulationTimeline()
}

// 关闭模拟时间轴动画
const closeSimulationTimeline = () => {
  simulationAnimationState.value.visible = false
  highlightedTrace.value = null
  resetPlaybackChanges()
}

// 处理 SimulationTimeline 组件的关闭事件
const handleSimulationTimelineClose = (visible: boolean) => {
  if (!visible) {
    closeSimulationTimeline()
  }
}

const handleVerify = async (): Promise<boolean> => {
  if (isVerifying.value) return false
  if (isSceneReplacementInProgress.value) {
    ElMessage.warning({ message: t('app.sceneReplacementInProgress'), type: 'warning' })
    return false
  }
  await waitForPendingFixRefresh()
  await waitForPendingBoardMutations()
  if (!ensureBoardDataReady()) return false
  if (nodes.value.length === 0) {
    ElMessage.warning({ message: t('app.noDevicesToVerify'), type: 'warning' })
    return false
  }
  if (specifications.value.length === 0) {
    ElMessage.warning({ message: t('app.noSpecsToVerify'), type: 'warning' })
    return false
  }
  if (!assertRulesHaveTriggers(rules.value)) {
    return false
  }
  let requestAttackBudget = 0
  try {
    requestAttackBudget = verificationForm.isAttack ? validateAttackBudget(verificationForm.attackBudget) : 0
  } catch (error: any) {
    ElMessage.error(error?.message || t('app.verificationFailed'))
    return false
  }

  isVerifying.value = true
  asyncVerificationActive.value = false
  verificationCancelRequested.value = false
  cancellingVerificationTask.value = false
  verificationError.value = null
  verificationResult.value = null

  try {
    const req = buildVerificationRequestPayload({
      nodes: nodes.value,
      deviceTemplates: deviceTemplates.value,
      environmentVariables: environmentVariables.value,
      rules: rules.value,
      specifications: specifications.value,
      isAttack: verificationForm.isAttack,
      attackBudget: requestAttackBudget,
      enablePrivacy: verificationForm.enablePrivacy
    })
    const submission: RunSubmission<VerificationRequest> = {
      request: req,
      signature: buildModelRunSignature(req, deviceTemplates.value)
    }
    activeVerificationSubmission.value = submission

    // Handle async or sync verification
    if (verificationForm.isAsync) {
      // Async verification. IMPORTANT: await the polling promise so the outer `finally`
      // (which sets isVerifying=false) only runs after polling truly ends — otherwise
      // the progress UI vanishes immediately and the button re-enables mid-run,
      // letting the user launch duplicate tasks.
      asyncVerificationActive.value = true
      asyncVerificationTask.value = { taskId: null, progress: 0, status: t('app.taskInitializing') }

      const submittedTask = await boardApi.verifyAsync(req)
      const taskId = submittedTask.id
      submission.taskId = taskId
      asyncVerificationTask.value.taskId = taskId
      asyncVerificationTask.value.progress = submittedTask.progress ?? 0
      asyncVerificationTask.value.status = formatTaskProgressStage(
        submittedTask.progressStage, submittedTask.status)
      upsertVerificationTaskSummary(submittedTask)

      await pollAsyncVerification(taskId, { submission })
      return true
    }

    // Sync verification (original logic)
    const result = await boardApi.verify(req)
    verificationResult.value = attachLocalRunSubmission({
      ...result,
      specResults: normalizeSpecResults((result as any).specResults)
    }, submission)
    if (['FAILED', 'OUTCOME_UNKNOWN'].includes(result.historyPersistence.status)) {
      ElMessage.warning({
        message: result.historyPersistence.status === 'OUTCOME_UNKNOWN'
          ? t('app.verificationHistorySaveOutcomeUnknown')
          : t('app.verificationHistorySaveFailed'),
        type: 'warning',
        duration: 6500
      })
      void loadVerificationRuns(false)
    }
    notifyVerificationOutcome(verificationResult.value)
    return true

  } catch (error: any) {
    if (isPollingAbortedError(error)) {
      return false
    }
    const message = asyncTaskQuotaMessage(error, 'verification')
      || extractApiErrorMessage(error, t('app.verificationFailed'))
    if (isAsyncTaskCancelledError(error)) {
      verificationError.value = null
      ElMessage.info({ message: t('app.verificationCancelled'), type: 'info' })
    } else {
      console.error('Verification failed:', error)
      verificationError.value = message
      ElMessage.error({ message: verificationError.value || t('app.verificationFailed'), type: 'error' })
    }
    return false
  } finally {
    isVerifying.value = false
    asyncVerificationActive.value = false
    cancellingVerificationTask.value = false
    verificationCancelRequested.value = false
  }
}

const runVerification = async () => {
  const completed = await handleVerify()
  if (completed && !verificationForm.isAsync) {
    closeVerificationPanel()
  }
}

const runFuzzing = async (): Promise<boolean> => {
  if (isFuzzing.value) return false
  if (isSceneReplacementInProgress.value) {
    ElMessage.warning({ message: t('app.sceneReplacementInProgress'), type: 'warning' })
    return false
  }
  await waitForPendingFixRefresh()
  await waitForPendingBoardMutations()
  if (!ensureBoardDataReady(['templates', 'nodes', 'environment', 'rules', 'specs'])) return false
  if (nodes.value.length === 0) {
    ElMessage.warning({ message: t('app.noDevicesToFuzz'), type: 'warning' })
    return false
  }
  if (specifications.value.length === 0) {
    ElMessage.warning({ message: t('app.noSpecsToFuzz'), type: 'warning' })
    return false
  }
  if (!assertRulesHaveTriggers(rules.value)) return false

  if (!fuzzingWorkloadReady.value) {
    if (!fuzzingWorkloadPreviewLoading.value && validFuzzingBudgetFields()) {
      scheduleFuzzingWorkloadPreview()
    }
    ElMessage.warning({
      message: fuzzingWorkloadPreviewError.value || t('app.fuzzWorkloadRequired'),
      type: 'warning'
    })
    return false
  }

  if (fuzzingContentCommandUnsupported.value) {
    ElMessage.warning({ message: t('app.fuzzContentCommandPreflightBlocked'), type: 'warning' })
    return false
  }

  const eligibleSpecIds = knownFuzzEligibleSpecifications.value.map(spec => spec.id)
  if (eligibleSpecIds.length === 0) {
    ElMessage.warning({ message: t('app.noEligibleSpecsToFuzz'), type: 'warning' })
    return false
  }
  if (effectiveFuzzingConfigurationError.value) {
    ElMessage.warning({ message: effectiveFuzzingConfigurationError.value, type: 'warning' })
    return false
  }
  const requestTargetSpecIds = fuzzingForm.targetSelectionMode === 'EXPLICIT'
    ? normalizedFuzzTargetSpecIds.value
    : (eligibleSpecIds.length === specifications.value.length ? [] : eligibleSpecIds)
  const requestFields = {
    maxIterations: fuzzingForm.maxIterations,
    pathLength: fuzzingForm.pathLength,
    populationSize: fuzzingForm.populationSize,
    ...(requestTargetSpecIds.length > 0
      ? { targetSpecIds: [...requestTargetSpecIds] }
      : {}),
    ...(fuzzingForm.seed === null ? {} : { seed: fuzzingForm.seed })
  }
  const paperDomainFingerprint = paperDomainPreview.value?.modelFingerprint
  let request: FuzzingRequest
  if (fuzzingForm.explorationMode === 'PAPER_COMPATIBLE') {
    if (!isValidFuzzPaperDomainFingerprint(paperDomainFingerprint)) {
      ElMessage.warning({ message: t('app.fuzzPaperDomainRequired'), type: 'warning' })
      return false
    }
    request = {
      ...requestFields,
      explorationMode: 'PAPER_COMPATIBLE',
      paperDomainFingerprint
    }
  } else {
    request = {
      ...requestFields,
      explorationMode: 'BOARD_SNAPSHOT'
    }
  }

  isFuzzing.value = true
  fuzzingWatchedTask.value = null
  asyncFuzzingActive.value = true
  cancellingFuzzingTask.value = false
  fuzzingCancelRequested.value = false
  fuzzingError.value = null
  fuzzingSettingsNotice.value = null
  asyncFuzzingTask.value = { taskId: null, progress: 0, status: t('app.taskInitializing') }
  let submittedTaskId: number | null = null

  try {
    const submittedTask = await fuzzingApi.startAsync(request)
    submittedTaskId = submittedTask.id
    trackFuzzTask(submittedTask.id)
    asyncFuzzingTask.value = {
      taskId: submittedTask.id,
      progress: normalizeTaskProgress(submittedTask.progress),
      status: formatTaskProgressStage(submittedTask.progressStage, submittedTask.status)
    }
    upsertFuzzingTaskSummary(submittedTask)
    fuzzingWatchedTask.value = submittedTask

    const run = await pollAsyncFuzzing(submittedTask.id)
    untrackFuzzTask(submittedTask.id)
    const shouldPresent = showFuzzingPanel.value
    showFuzzingPanel.value = false
    if (shouldPresent) {
      presentFuzzingRun(run)
    } else {
      const notificationShown = markFuzzNotificationUnread({
        taskId: submittedTask.id,
        runId: run.id,
        kind: 'COMPLETED',
        outcome: run.outcome,
        createdAt: run.completedAt
      })
      if (notificationShown && run.outcome === 'BUDGET_EXHAUSTED') {
        ElMessage.info({ message: fuzzingCompletionMessage(run), type: 'info', duration: 6500 })
      } else if (notificationShown) {
        ElMessage.warning({ message: fuzzingCompletionMessage(run), type: 'warning', duration: 6500 })
      }
    }
    return true
  } catch (error: any) {
    if (isPollingAbortedError(error)) return false
    if (isAsyncTaskCancelledError(error)) {
      if (submittedTaskId) untrackFuzzTask(submittedTaskId)
      fuzzingError.value = null
      ElMessage.info({ message: t('app.fuzzSearchCancelled'), type: 'info' })
    } else if (submittedTaskId && isFuzzTaskRecoveryPendingError(error)) {
      fuzzingError.value = null
      fuzzingSettingsNotice.value = t('app.fuzzResultRecoveryPending')
      if (!showFuzzingPanel.value) {
        ElMessage.info({ message: fuzzingSettingsNotice.value, type: 'info', duration: 6500 })
      }
    } else if (submittedTaskId && isFuzzCompletedResultUnavailableError(error)) {
      const unavailableMessage = error.message || t('app.failedToLoadFuzzingRun')
      fuzzingError.value = unavailableMessage
      markFuzzNotificationUnread({
        taskId: submittedTaskId,
        runId: submittedTaskId,
        kind: 'UNAVAILABLE',
        createdAt: new Date().toISOString()
      })
      if (!showFuzzingPanel.value) {
        ElMessage.error({ message: unavailableMessage, type: 'error' })
      }
    } else {
      console.error('Fuzz search failed:', error)
      const stalePaperDomain = submittedTaskId === null
        && request.explorationMode === 'PAPER_COMPATIBLE'
        && hasApiValidationError(error, 'paperDomainFingerprint')
      if (stalePaperDomain) {
        paperDomainStaleRecoveryActive.value = true
        const boardRefreshed = await refreshSceneForReconciliation()
        invalidatePaperDomainPreview()
        fuzzingError.value = t(boardRefreshed
          ? 'app.fuzzPaperDomainStale'
          : 'app.fuzzPaperDomainStaleBoardRefreshFailed')
        if (boardRefreshed && showFuzzingPanel.value && validPaperPathLength()) {
          schedulePaperDomainPreview()
        } else {
          ElMessage.warning({ message: fuzzingError.value, type: 'warning' })
        }
      } else {
        fuzzingError.value = fuzzTaskQuotaMessage(error)
          || extractApiErrorMessage(error, t('app.fuzzSearchFailed'))
      }
      if (submittedTaskId && !showFuzzingPanel.value) {
        markFuzzNotificationUnread({
          taskId: submittedTaskId,
          kind: 'FAILED',
          createdAt: new Date().toISOString()
        })
        ElMessage.error({ message: fuzzingError.value, type: 'error' })
      } else if (submittedTaskId) {
        untrackFuzzTask(submittedTaskId)
      } else if (!showFuzzingPanel.value && !stalePaperDomain) {
        ElMessage.error({ message: fuzzingError.value, type: 'error' })
      }
    }
    return false
  } finally {
    isFuzzing.value = false
    asyncFuzzingActive.value = false
    cancellingFuzzingTask.value = false
    fuzzingCancelRequested.value = false
    fuzzingWatchedTask.value = null
    if (!boardLifecycleDisposed) {
      await loadTaskInbox(false, { showLoading: false })
    }
  }
}

// Run simulation with proper panel handling
const runSimulation = async () => {
  await handleSimulate({ ...simulationForm })
}

const handleSimulate = async (simConfig: {
  steps: number
  isAttack: boolean
  attackBudget: number
  enablePrivacy: boolean
  isAsync: boolean
  saveToHistory?: boolean
}): Promise<boolean> => {
  if (isSimulating.value) return false
  if (isSceneReplacementInProgress.value) {
    ElMessage.warning({ message: t('app.sceneReplacementInProgress'), type: 'warning' })
    return false
  }
  await waitForPendingFixRefresh()
  await waitForPendingBoardMutations()
  if (!ensureBoardDataReady(['templates', 'nodes', 'environment', 'rules'])) return false
  if (nodes.value.length === 0) {
    ElMessage.warning({ message: t('app.noDevicesToSimulate'), type: 'warning' })
    return false
  }
  if (!assertRulesHaveTriggers(rules.value)) {
    return false
  }
  const normalizedSimConfig = { ...simConfig }
  let requestSteps = 10
  let requestAttackBudget = 0
  try {
    requestSteps = validateSimulationSteps(normalizedSimConfig.steps)
    requestAttackBudget = normalizedSimConfig.isAttack ? validateAttackBudget(normalizedSimConfig.attackBudget) : 0
  } catch (error: any) {
    ElMessage.error(error?.message || t('app.simulationFailed'))
    return false
  }

  isSimulating.value = true
  asyncSimulationActive.value = false
  simulationCancelRequested.value = false
  cancellingSimulationTask.value = false
  simulationError.value = null
  simulationResult.value = null

  // 重置异步任务状态
  if (normalizedSimConfig.isAsync) {
    asyncSimulationActive.value = true
    asyncSimulationTask.value = { taskId: null, progress: 0, status: t('app.taskInitializing') }
  }

  try {
    const req = buildSimulationRequestPayload({
      nodes: nodes.value,
      deviceTemplates: deviceTemplates.value,
      environmentVariables: environmentVariables.value,
      rules: rules.value,
      steps: requestSteps,
      isAttack: normalizedSimConfig.isAttack,
      attackBudget: requestAttackBudget,
      enablePrivacy: normalizedSimConfig.enablePrivacy
    })
    const submission: RunSubmission<SimulationRequest> = {
      request: req,
      signature: buildModelRunSignature(req, deviceTemplates.value)
    }
    activeSimulationSubmission.value = submission
    
    let result: any

    if (normalizedSimConfig.isAsync) {
      // 异步模拟：创建任务并轮询进度
      const submittedTask = await simulationApi.simulateAsync(req)
      const taskId = submittedTask.id
      submission.taskId = taskId
      asyncSimulationTask.value.taskId = taskId
      asyncSimulationTask.value.progress = submittedTask.progress ?? 0
      asyncSimulationTask.value.status = formatTaskProgressStage(
        submittedTask.progressStage, submittedTask.status)
      upsertSimulationTaskSummary(submittedTask)

      // 轮询任务进度
      result = await pollAsyncSimulation(taskId)
    } else {
      // 同步模拟
      if (normalizedSimConfig.saveToHistory) {
        const trace = await simulationApi.simulateAndSave(req)
        result = {
          traceId: trace.id,
          states: trace.states,
          steps: trace.steps,
          requestedSteps: trace.requestedSteps,
          createdAt: trace.createdAt,
          logs: trace.logs || [],
          nusmvOutput: trace.nusmvOutput || '',
          modelComplete: trace.modelComplete,
          disabledRuleCount: trace.disabledRuleCount,
          generationIssues: getGenerationIssues(trace),
          isAttack: trace.isAttack === true,
          attackBudget: trace.attackBudget ?? 0,
          enablePrivacy: trace.enablePrivacy === true,
          modelSemantics: trace.modelSemantics,
          modelSnapshot: trace.modelSnapshot
        }
      } else {
        result = await simulationApi.simulate(req)
      }
    }

    if (['FAILED', 'OUTCOME_UNKNOWN'].includes(result.historyPersistence?.status)) {
      ElMessage.warning({
        message: result.historyPersistence.status === 'OUTCOME_UNKNOWN'
          ? t('app.simulationHistorySaveOutcomeUnknown')
          : t('app.simulationHistorySaveFailed'),
        type: 'warning',
        duration: 6500
      })
      void loadSimulationRuns(false)
    }
    
    // Keep the full result so its logs / raw NuSMV output remain reachable from the timeline via
    // openSimulationLogs(); the success path opens the timeline (below), not the result dialog.
    result = attachLocalRunSubmission(result, submission)
    lastSimulationResult.value = result
    if (result.traceId) {
      simulationHistoryRequests.invalidate()
      simulationRuns.value = [
        {
          id: result.traceId,
          requestedSteps: result.requestedSteps,
          steps: result.steps,
          modelComplete: isSimulationModelComplete(result),
          disabledRuleCount: getSimulationDisabledRuleCount(result),
          generationIssues: getGenerationIssues(result),
          isAttack: result.isAttack === true,
          attackBudget: result.attackBudget ?? 0,
          enablePrivacy: result.enablePrivacy === true,
          modelSnapshot: result.modelSnapshot,
          createdAt: result.createdAt || new Date().toISOString(),
          dataAvailable: true
        },
        ...simulationRuns.value.filter(item => item.id !== result.traceId)
      ]
    }

    // 直接打开时间轴动画，不显示结果对话框
    if (result.states && result.states.length > 0) {
      if (normalizedSimConfig.isAsync) {
        if (!showSimulationPanel.value || traceAnimationState.value.visible || simulationAnimationState.value.visible || isLiveBoardEditorVisible.value) {
          notifySimulationOutcome(result, true)
          if (isLiveBoardEditorVisible.value) notifyAutomaticPlaybackDeferred()
          return true
        }

        savedSimulationStates.value = [...result.states]
        showSimulationPanel.value = false
        simulationAnimationState.value = {
          visible: true
        }
        highlightedTrace.value = {
          states: savedSimulationStates.value,
          selectedStateIndex: 0
        }
        notifySimulationOutcome(result, true)
        return true
      }

      // 保存模拟 states 数据
      savedSimulationStates.value = [...result.states]

      // 关闭模拟配置面板
      showSimulationPanel.value = false
      
      // 打开模拟时间轴动画
      simulationAnimationState.value = {
        visible: true
      }
      
      // 高亮第一个状态
      highlightedTrace.value = {
        states: savedSimulationStates.value,
        selectedStateIndex: 0
      }
      
      notifySimulationOutcome(result, !!normalizedSimConfig.saveToHistory)
      return true
    } else {
      const failureReason = t('app.simulationCompletedNoStates')
      simulationError.value = failureReason
      ElMessage.error({ message: failureReason, type: 'error' })
      return false
    }

  } catch (error: any) {
    if (isPollingAbortedError(error)) {
      return false
    }
    const message = asyncTaskQuotaMessage(error, 'simulation')
      || extractApiErrorMessage(error, t('app.simulationFailed'))
    if (isAsyncTaskCancelledError(error)) {
      simulationError.value = null
      ElMessage.info({ message: t('app.simulationCancelled'), type: 'info' })
    } else {
      console.error('Simulation failed:', error)
      simulationError.value = message
      ElMessage.error({ message: simulationError.value || t('app.simulationFailed'), type: 'error' })
    }
    return false
  } finally {
    isSimulating.value = false
    asyncSimulationActive.value = false
    cancellingSimulationTask.value = false
    simulationCancelRequested.value = false
  }
}

// Open the saved run summary and technical details without replacing the primary timeline view.
const openSimulationRunDetails = () => {
  if (!lastSimulationResult.value) {
    ElMessage.info({ message: t('app.noSimulationRunDetailsAvailable'), type: 'info' })
    return
  }
  simulationResult.value = lastSimulationResult.value
}

// A status/progress fetch error is "permanent" (fail fast, don't retry to timeout) when
// it is an auth/not-found/client error — retrying will never succeed. Network blips and
// 5xx are treated as transient.
const isPermanentPollError = (error: any): boolean => {
  if (error?.code === RUN_RESPONSE_INCOMPLETE_CODE
    || error?.code === FUZZ_RESPONSE_INCOMPLETE_CODE) return true
  const status = error?.response?.status
  return typeof status === 'number'
    && status >= 400
    && status < 500
    && !isTransientTaskHttpStatus(status)
}

// 轮询异步验证任务：await 到终态/超时/永久错误为止，供 handleVerify await。
// 用 while + await sleep（而非 setInterval + async 回调）：串行执行，天然无重入——
// 若某次状态查询超过 1s 也不会并发发起下一轮、不会重复 toast 或旧响应覆盖新进度。
const pollAsyncVerification = async (
  taskId: number,
  options: { presentResult?: boolean; submission?: RunSubmission<VerificationRequest> } = {}
): Promise<void> => {
  let pollCount = 0

  while (pollCount < ASYNC_TASK_MAX_POLLS) {
    throwIfPollingAborted()
    let task: VerificationTask
    try {
      task = await boardApi.getTask(taskId)
      throwIfPollingAborted()
      asyncVerificationTask.value.progress = normalizeTaskProgress(task.progress)
      asyncVerificationTask.value.status = formatTaskProgressStage(task.progressStage, task.status)
      upsertVerificationTaskSummary(task)
    } catch (e: any) {
      if (isPollingAbortedError(e)) {
        throw e
      }
      // Permanent errors (401/403/404/…) fail fast; transient errors retry.
      if (isPermanentPollError(e)) {
        throw e
      }
      await waitForNextPoll()
      pollCount++
      continue
    }

    // Terminal-state handling outside the try so its logic isn't swallowed by the catch.
    if (task.status === 'COMPLETED') {
      const traces = task.outcome === 'VIOLATED'
        ? await boardApi.getTaskTraces(taskId)
        : []
      throwIfPollingAborted()
      const result = attachLocalRunSubmission(
        buildVerificationResultFromTask(task, traces),
        options.submission || submissionForTask(activeVerificationSubmission.value, taskId)
      )
      upsertVerificationTaskSummary({ ...task, progress: 100 })
      if (options.presentResult || showVerificationPanel.value) {
        verificationResult.value = result
        notifyVerificationOutcome(verificationResult.value)
        showVerificationPanel.value = false
      } else {
        notifyVerificationOutcome(result)
      }
      await loadVerificationRuns()
      return
    } else if (task.status === 'FAILED') {
      throw new Error(task.errorMessage || t('app.verificationFailed'))
    } else if (task.status === 'CANCELLED') {
      throw new AsyncTaskCancelledError(task.errorMessage || t('app.verificationCancelled'))
    }

    // 仍在 PENDING/RUNNING，等待后继续
    await waitForNextPoll()
    pollCount++
  }

  throw new Error(t('app.verificationTimeout'))
}

// 轮询异步模拟任务
const pollAsyncSimulation = async (taskId: number): Promise<any> => {
  let pollCount = 0

  while (pollCount < ASYNC_TASK_MAX_POLLS) {
    throwIfPollingAborted()
    let task: SimulationTask
    try {
      // 获取任务进度 + 状态（瞬时网络错误容忍：进入 catch 后继续轮询）
      task = await simulationApi.getTask(taskId)
      throwIfPollingAborted()
      asyncSimulationTask.value.progress = normalizeTaskProgress(task.progress)
      asyncSimulationTask.value.status = formatTaskProgressStage(task.progressStage, task.status)
      upsertSimulationTaskSummary(task)
    } catch (error: any) {
      if (isPollingAbortedError(error)) {
        throw error
      }
      // Permanent errors (401/403/404/task-not-found) fail fast; only transient
      // errors (network blips, 5xx) retry until the poll ceiling.
      if (isPermanentPollError(error)) {
        throw error
      }
      console.error('Poll error (transient, will retry):', error)
      await waitForNextPoll()
      pollCount++
      continue
    }

    // 终态处理放在 try 之外：FAILED/CANCELLED 必须立即抛出并中止轮询，
    // 不能被上面的瞬时错误 catch 吞掉（否则会一直轮询到超时才报通用错误）。
    if (task.status === 'COMPLETED') {
      if (task.simulationTraceId) {
        const trace = await simulationApi.getSimulation(task.simulationTraceId)
        throwIfPollingAborted()
        upsertSimulationTaskSummary({ ...task, progress: 100 })
        await loadSimulationRuns()
        return {
          traceId: trace.id,
          states: trace.states,
          steps: trace.steps,
          requestedSteps: trace.requestedSteps,
          createdAt: trace.createdAt,
          logs: trace.logs || [],
          nusmvOutput: trace.nusmvOutput,
          modelComplete: trace.modelComplete,
          disabledRuleCount: trace.disabledRuleCount,
          generationIssues: getGenerationIssues(trace),
          isAttack: trace.isAttack === true,
          attackBudget: trace.attackBudget ?? 0,
          enablePrivacy: trace.enablePrivacy === true,
          modelSemantics: trace.modelSemantics,
          modelSnapshot: trace.modelSnapshot
        }
      }
      upsertSimulationTaskSummary({ ...task, progress: 100 })
      throw new Error(t('app.taskCompletedNoTraceFound'))
    } else if (task.status === 'FAILED') {
      throw new Error(task.errorMessage || t('app.asyncSimulationFailed'))
    } else if (task.status === 'CANCELLED') {
      throw new AsyncTaskCancelledError(t('app.simulationTaskCancelledByServer'))
    }

    // 仍在 PENDING/RUNNING，等待后继续
    await waitForNextPoll()
    pollCount++
  }

  // 超出最大轮询次数
  throw new Error(t('app.simulationTimeout'))
}

const pollAsyncFuzzing = async (taskId: number): Promise<FuzzingRun> => {
  let pollCount = 0
  let completedResultFailures = 0

  while (pollCount < ASYNC_TASK_MAX_POLLS) {
    throwIfPollingAborted()
    let task: FuzzingTask
    try {
      task = await fuzzingApi.getTask(taskId)
      throwIfPollingAborted()
      asyncFuzzingTask.value.progress = normalizeTaskProgress(task.progress)
      asyncFuzzingTask.value.status = formatTaskProgressStage(task.progressStage, task.status)
      upsertFuzzingTaskSummary(task)
    } catch (error: any) {
      if (isPollingAbortedError(error)) throw error
      if (isPermanentPollError(error)) throw error
      await waitForNextPoll()
      pollCount++
      continue
    }

    if (task.status === 'COMPLETED') {
      asyncFuzzingTask.value.progress = 100
      try {
        const run = await loadFuzzRunSingleFlight(taskId, task.runId ?? task.id)
        clearFuzzRunRecoveryState(taskId)
        upsertFuzzingRunSummary(summarizeFuzzingRun(run))
        return run
      } catch (error: any) {
        if (classifyTrackedFuzzRunError(error) !== 'RETRY') {
          throw new FuzzCompletedResultUnavailableError(
            localizedErrorMessage(error, t('app.failedToLoadFuzzingRun'), locale.value)
          )
        }
        asyncFuzzingTask.value.status = t('app.fuzzResultRecoveryPending')
        const retryDelay = scheduleFuzzRunRecovery(taskId)
        completedResultFailures++
        if (completedResultFailures >= FUZZ_INLINE_RESULT_RECOVERY_MAX_FAILURES) {
          throw new FuzzTaskRecoveryPendingError()
        }
        await waitForPollingDelay(retryDelay)
        pollCount++
        continue
      }
    }
    if (task.status === 'FAILED') {
      throw new Error(task.errorMessage || t('app.fuzzSearchFailed'))
    }
    if (task.status === 'CANCELLED' || fuzzingCancelRequested.value) {
      throw new AsyncTaskCancelledError(task.errorMessage || t('app.fuzzSearchCancelled'))
    }

    await waitForNextPoll()
    pollCount++
  }

  throw new FuzzTaskRecoveryPendingError()
}

// ==== Results Dialog ====
const showResultDialog = computed(() => !!verificationResult.value || !!verificationError.value)
const isSimulationResultDialogOpen = computed(() => !!simulationResult.value || !!simulationError.value)
const closeSimulationResultDialog = () => {
  simulationResult.value = null
  simulationError.value = null
}
const {
  setDialogRef: setSimulationResultDialogRef,
  handleModalKeydown: handleSimulationResultDialogKeydown
} = useModalAccessibility(
  isSimulationResultDialogOpen,
  closeSimulationResultDialog,
  () => document.querySelector<HTMLElement>('[data-testid="open-simulation-panel"]')
)
const isResultSurfaceVisible = computed(() =>
  showResultDialog.value || !!simulationResult.value || !!simulationError.value
  || showFuzzingResultDialog.value
)
const showCanvasEmptyState = computed(() =>
  isBoardDataReady.value
  && nodes.value.length === 0
  && !isSceneReplacementInProgress.value
  && !isModelPlaybackActive.value
  && !isResultSurfaceVisible.value
  && !showSimulationPanel.value
  && !showVerificationPanel.value
  && !showFuzzingPanel.value
  && !showHistoryPanel.value
  && !isAnyRecommendationPanelVisible()
)
const verificationGenerationWarningCounts = computed(() => getGenerationWarningCounts(verificationResult.value))
const verificationGenerationIssues = computed(() => getGenerationIssues(verificationResult.value))
const verificationCheckLogs = computed(() => verificationResult.value?.checkLogs || [])
const verificationSpecResultSummary = computed(() => {
  const results = normalizeSpecResults(verificationResult.value?.specResults).map((result, index) => {
    const submittedSpecSnapshot = {
      templateId: result.templateId,
      templateLabel: result.specificationLabel
    } as Specification
    return {
      ...result,
      displayTitle: getSpecResultDisplayTitle(submittedSpecSnapshot, index),
      presentation: result.outcome === 'SATISFIED'
        ? {
            borderClass: 'border-green-200',
            badgeClass: 'bg-green-50 border-green-200 text-green-700',
            icon: 'check_circle',
            label: t('app.specSatisfied')
          }
        : result.outcome === 'VIOLATED'
          ? {
              borderClass: 'border-red-200',
              badgeClass: 'bg-red-50 border-red-200 text-red-700',
              icon: 'error',
              label: t('app.specViolated')
            }
          : {
              borderClass: 'border-amber-200',
              badgeClass: 'bg-amber-50 border-amber-200 text-amber-700',
              icon: 'help',
              label: t('app.specInconclusive')
            }
    }
  })
  const satisfied = results.filter(result => result.outcome === 'SATISFIED').length
  const violated = results.filter(result => result.outcome === 'VIOLATED').length
  const inconclusive = results.filter(result => result.outcome === 'INCONCLUSIVE').length
  return {
    results,
    total: results.length,
    satisfied,
    violated,
    inconclusive
  }
})
const verificationViolationCount = computed(() =>
  Math.max(verificationSpecResultSummary.value.violated, verificationResult.value?.traces?.length || 0)
)
const verificationUnsafeDetail = computed(() =>
  verificationViolationCount.value > 0
    ? t('app.foundViolations', { count: verificationViolationCount.value })
    : t('app.verificationResultUnreliable')
)
const verificationResultStatus = computed(() => {
  const outcome = getVerificationOutcome(verificationResult.value)
  if (outcome === 'INCONCLUSIVE') {
    return {
      headerClass: 'bg-amber-50 border-amber-200',
      cardClass: 'bg-amber-50 border border-amber-200',
      iconBgClass: 'bg-amber-100',
      iconTextClass: 'text-amber-700',
      titleClass: 'text-amber-900',
      detailClass: 'text-amber-800',
      icon: 'help',
      title: t('app.verificationInconclusive'),
      detail: t('app.verificationInconclusiveDetail')
    }
  }

  if (outcome === 'SATISFIED' && !isVerificationModelComplete(verificationResult.value, outcome)) {
    return {
      headerClass: 'bg-amber-50 border-amber-200',
      cardClass: 'bg-gradient-to-r from-amber-50 to-yellow-50 border border-amber-200',
      iconBgClass: 'bg-amber-100',
      iconTextClass: 'text-amber-600',
      titleClass: 'text-amber-800',
      detailClass: 'text-amber-700',
      icon: 'report',
      title: t('app.verificationPassedWithGenerationWarnings'),
      detail: t('app.emittedSpecsPassedWithGenerationWarnings')
    }
  }

  if (outcome === 'SATISFIED') {
    return {
      headerClass: 'bg-green-50 border-green-200',
      cardClass: 'bg-gradient-to-r from-green-50 to-emerald-50 border border-green-200',
      iconBgClass: 'bg-green-100',
      iconTextClass: 'text-green-600',
      titleClass: 'text-green-800',
      detailClass: 'text-green-600',
      icon: 'verified',
      title: t('app.checkedSpecificationsSatisfied'),
      detail: t('app.allSpecsPassedVerification')
    }
  }

  return {
    headerClass: 'bg-red-50 border-red-200',
    cardClass: 'bg-gradient-to-r from-red-50 to-orange-50 border border-red-200',
    iconBgClass: 'bg-red-100',
    iconTextClass: 'text-red-600',
    titleClass: 'text-red-800',
    detailClass: 'text-red-600',
    icon: 'warning',
    title: t('app.specificationViolationFound'),
    detail: verificationUnsafeDetail.value
  }
})

const verificationModelSemanticsConsistent = computed(() => isModelSemanticsConsistent(
  verificationResult.value?.modelSemantics,
  {
    isAttack: verificationResult.value?.isAttack,
    attackBudget: verificationResult.value?.attackBudget,
    enablePrivacy: verificationResult.value?.enablePrivacy
  }
))

const verificationBoardComparison = computed<RunBoardComparison>(() =>
  compareRunToCurrentBoard(verificationResult.value, 'verification')
)

const simulationBoardComparison = computed<RunBoardComparison>(() =>
  compareRunToCurrentBoard(lastSimulationResult.value, 'simulation')
)

const traceModelSemanticsConsistent = computed(() => isModelSemanticsConsistent(
  currentTrace.value?.modelSemantics,
  activeTraceContext.value
))

const counterexampleTraceHelpText = computed(() => {
  if (activeFuzzingFinding.value) {
    return [
      t('app.fuzzFindingReplayHint'),
      t('app.traceVisualization.playbackSnapshotReadOnly')
    ].join('\n\n')
  }
  const context = activeTraceContext.value
  const details = [
    t('app.traceVisualization.counterexampleTraceHint'),
    t('app.traceVisualization.playbackSnapshotReadOnly')
  ]

  if (!traceModelSemanticsConsistent.value) {
    details.push(t('app.modelSemanticsUnavailable'))
    return details.join('\n\n')
  }

  details.push(context.isAttack
    ? t('app.traceVisualization.simulationAttackContext', {
        count: context.attackBudget,
        total: currentTrace.value?.modelSemantics?.modeledAttackPointCount ?? 0,
        devices: currentTrace.value?.modelSemantics?.modeledDeviceAttackPointCount ?? 0,
        falsifiable: currentTrace.value?.modelSemantics?.modeledFalsifiableReadingDeviceCount ?? 0,
        links: currentTrace.value?.modelSemantics?.modeledAutomationLinkAttackPointCount ?? 0
      })
    : t('app.traceVisualization.simulationNoAttackContext'))
  details.push(context.enablePrivacy
    ? t('app.traceVisualization.privacyPropagationEnabled')
    : t('app.traceVisualization.privacyPropagationNotModeled'))
  details.push(t('app.environmentEvolutionIncluded'))
  details.push(t('app.labelPropagationScopeSummary'))
  return details.join('\n\n')
})

const closeResultDialog = () => {
  verificationResult.value = null
  verificationError.value = null
}
</script>

<template>
  <!-- [Fix] @wheel.ctrl.prevent 阻止浏览器原生缩放 -->
  <div
    :class="[
      'iot-board',
      { 'is-inspector-collapsed': boardPanels.inspector.collapsed }
    ]"
    data-testid="board-root"
    :aria-busy="!isBoardDataReady"
    :style="boardShellStyle"
    @wheel.ctrl.prevent="onBoardWheel"
  >
    <!-- Navigation Bar - 与首页风格一致 -->
    <nav class="board-nav-bar">
      <div class="nav-content">
        <button
          type="button"
          class="logo-left"
          :aria-label="t('app.title')"
          @click="router.push('/board')"
        >
          IoT-Verify<sup class="logo-sup">®</sup>
        </button>

        <div class="nav-actions">
          <ThemeToggle :tone="boardHeaderTone" compact />
          <LanguageToggle :tone="boardHeaderTone" compact />
          <input
            ref="sceneImportInputRef"
            data-testid="scene-import-file"
            class="sr-only"
            type="file"
            accept="application/json,.json"
            @change="handleSceneImportFile"
          />
          <button
            type="button"
            class="nav-action-btn scene-action-btn"
            data-testid="scene-import"
            :aria-label="t('app.sceneImport')"
            :title="t('app.sceneImport')"
            :disabled="isImportingScene || !isBoardDataReady"
            @click="triggerSceneImport"
          >
            <span class="material-symbols-outlined" aria-hidden="true">upload_file</span>
            <span>{{ t('app.sceneImport') }}</span>
          </button>
          <button
            type="button"
            class="nav-action-btn scene-action-btn"
            data-testid="scene-export"
            :aria-label="t('app.sceneExport')"
            :title="t('app.sceneExport')"
            :disabled="isImportingScene || isClearingScene || !isBoardDataReady"
            @click="exportScene"
          >
            <span class="material-symbols-outlined" aria-hidden="true">download</span>
            <span>{{ t('app.sceneExport') }}</span>
          </button>
          <button
            type="button"
            class="nav-action-btn scene-action-btn scene-clear-btn"
            data-testid="scene-clear"
            :aria-label="t('app.sceneClear')"
            :title="t('app.sceneClear')"
            :disabled="isImportingScene || isClearingScene || !isBoardDataReady"
            @click="clearScene"
          >
            <span class="material-symbols-outlined" aria-hidden="true">delete_sweep</span>
            <span>{{ t('app.sceneClear') }}</span>
          </button>
          <details
            ref="sceneActionsMenuRef"
            class="scene-actions-menu"
            @toggle="handleSceneActionsMenuToggle"
            @keydown.esc.stop.prevent="closeSceneActionsMenu(true)"
          >
            <summary
              class="scene-actions-menu__trigger"
              role="button"
              :aria-label="t('app.sceneActions')"
              :title="t('app.sceneActions')"
              aria-controls="scene-actions-command-group"
              :aria-expanded="sceneActionsMenuOpen"
            >
              <span class="material-symbols-outlined" aria-hidden="true">more_horiz</span>
            </summary>
            <div
              id="scene-actions-command-group"
              class="scene-actions-menu__popover"
              role="group"
              :aria-label="t('app.sceneActions')"
            >
              <button
                type="button"
                :disabled="isImportingScene || !isBoardDataReady"
                @click="closeSceneActionsMenu(); triggerSceneImport()"
              >
                <span class="material-symbols-outlined" aria-hidden="true">upload_file</span>
                <span>{{ t('app.sceneImport') }}</span>
              </button>
              <button
                type="button"
                :disabled="isImportingScene || isClearingScene || !isBoardDataReady"
                @click="closeSceneActionsMenu(); exportScene()"
              >
                <span class="material-symbols-outlined" aria-hidden="true">download</span>
                <span>{{ t('app.sceneExport') }}</span>
              </button>
              <button
                type="button"
                class="scene-actions-menu__danger"
                :disabled="isImportingScene || isClearingScene || !isBoardDataReady"
                @click="closeSceneActionsMenu(); clearScene()"
              >
                <span class="material-symbols-outlined" aria-hidden="true">delete_sweep</span>
                <span>{{ t('app.sceneClear') }}</span>
              </button>
            </div>
          </details>
          <button
            type="button"
            class="nav-action-btn ai-assistant-btn"
            data-testid="open-ai-assistant"
            :aria-label="t('app.aiAssistant')"
            :disabled="!isBoardDataReady"
            @click="toggleChat"
          >
            <span class="material-symbols-outlined">smart_toy</span>
            <span>{{ t('app.aiAssistant') }}</span>
          </button>
          <button
            type="button"
            class="nav-logout-btn"
            :aria-label="t('app.logout')"
            :title="t('app.logout')"
            @click="handleLogout"
          >
            <span class="material-symbols-outlined">logout</span>
          </button>
        </div>
      </div>
    </nav>

    <div
      v-if="!isBoardDataReady && failedBoardDataKeys.length === 0"
      class="fixed inset-x-0 top-14 z-[2200] flex h-9 items-center justify-center gap-2 border-b border-teal-200 bg-teal-50 text-xs font-semibold text-teal-900 dark:border-teal-800 dark:bg-teal-950 dark:text-teal-100"
      role="status"
      aria-live="polite"
      data-testid="board-data-loading"
    >
      <span class="material-symbols-outlined animate-spin text-base" aria-hidden="true">progress_activity</span>
      {{ t('app.boardSnapshotLoading') }}
    </div>

    <div
      v-if="failedBoardDataKeys.length > 0"
      class="fixed left-1/2 top-16 z-[2300] flex w-[min(92vw,720px)] -translate-x-1/2 items-center gap-3 rounded-md border border-red-300 bg-red-50 px-4 py-3 text-sm text-red-900 shadow-lg dark:border-red-800 dark:bg-red-950 dark:text-red-100"
      role="alert"
      data-testid="board-data-load-error"
    >
      <span class="material-symbols-outlined shrink-0" aria-hidden="true">sync_problem</span>
      <span class="min-w-0 flex-1 break-words">
        {{ t('app.boardDataLoadFailedWithCollections', {
          collections: failedBoardDataKeys.map(boardDataKeyLabel).join(', ')
        }) }}
      </span>
      <button
        type="button"
        class="inline-flex shrink-0 items-center gap-1 rounded-md border border-red-400 px-2.5 py-1.5 font-semibold hover:bg-red-100 dark:border-red-700 dark:hover:bg-red-900"
        @click="retryBoardDataLoad"
      >
        <span class="material-symbols-outlined text-base" aria-hidden="true">refresh</span>
        {{ t('app.retry') }}
      </button>
    </div>

    <!-- Logout Confirmation Dialog -->
    <LogoutConfirmDialog
      v-if="showLogoutDialog"
      v-model:visible="showLogoutDialog"
      :loading="isLoggingOut"
      @confirm="handleLogoutConfirm"
      @cancel="handleLogoutCancel"
      @delete-account="handleOpenDeleteAccount"
    />

    <AccountDeleteDialog
      v-if="showDeleteAccountDialog"
      v-model:visible="showDeleteAccountDialog"
      :username="currentUser?.username"
      :phone="currentUser?.phone"
      :loading="isDeletingAccount"
      @confirm="handleDeleteAccountConfirm"
    />

    <div
      v-if="templateInstanceDialogVisible"
      class="fixed inset-0 z-[2400] flex items-center justify-center bg-slate-950/20 p-4 backdrop-blur-[2px] dark:bg-slate-950/35"
      @click="cancelTemplateInstanceCreate"
    >
      <div
        class="max-h-[calc(100vh-2rem)] w-full max-w-lg overflow-y-auto rounded-2xl border border-slate-200 bg-white p-5 shadow-2xl dark:border-slate-700 dark:bg-slate-900"
        data-testid="template-instance-dialog"
        role="dialog"
        aria-modal="true"
        aria-labelledby="template-instance-title"
        @click.stop
      >
        <div class="mb-4 flex items-start gap-3">
          <div class="flex h-12 w-12 flex-shrink-0 items-center justify-center rounded-xl bg-orange-100 text-orange-600 dark:bg-orange-500/15 dark:text-orange-300">
            <span class="material-symbols-outlined" aria-hidden="true">add_location_alt</span>
          </div>
          <div class="min-w-0">
            <h3 id="template-instance-title" class="text-base font-extrabold text-slate-900 dark:text-white">
              {{ t('app.createDeviceFromTemplate') }}
            </h3>
            <p class="mt-1 text-xs leading-relaxed text-slate-500 dark:text-slate-400">
              {{ t('app.createDeviceFromTemplateHint', { template: templateInstanceDialogData.template?.manifest.Name || t('app.unknown') }) }}
            </p>
          </div>
        </div>

        <label class="block text-xs font-bold uppercase tracking-wide text-slate-500 dark:text-slate-400">
          {{ t('app.deviceName') }}
        </label>
        <input
          v-model="templateInstanceDialogData.name"
          data-testid="template-instance-name"
          class="mt-1 w-full rounded-xl border-2 border-slate-200 bg-white px-3 py-2.5 text-sm font-semibold text-slate-900 outline-none transition focus:border-orange-400 focus:ring-2 focus:ring-orange-100 dark:border-slate-700 dark:bg-slate-950 dark:text-white dark:focus:border-orange-400 dark:focus:ring-orange-500/20"
          :placeholder="t('app.deviceNamePlaceholder')"
          :disabled="templateInstanceSaving"
          @keydown.enter.prevent="confirmTemplateInstanceCreate"
          @keydown.esc.prevent="cancelTemplateInstanceCreate"
        />

        <div
          v-if="templateInstanceEnvironmentAdditions.length > 0"
          data-testid="template-instance-environment-preview"
          class="mt-3 flex items-start gap-2 rounded-lg border border-sky-200 bg-sky-50 px-3 py-2 text-xs leading-relaxed text-sky-900 dark:border-sky-500/30 dark:bg-sky-500/10 dark:text-sky-200"
        >
          <span class="material-symbols-outlined mt-0.5 text-sm" aria-hidden="true">water_drop</span>
          <span>{{ t('app.deviceCreationEnvironmentAdditionsPreview', { names: templateInstanceEnvironmentAdditions.join(', ') }) }}</span>
        </div>

        <details
          v-if="templateInstanceHasRuntimeFields"
          data-testid="template-instance-runtime"
          class="mt-4 rounded-xl border border-orange-100 bg-orange-50/40 p-3 shadow-sm dark:border-orange-500/20 dark:bg-orange-500/10"
        >
          <summary
            data-testid="template-instance-runtime-toggle"
            class="flex cursor-pointer select-none items-center justify-between gap-2 text-[11px] font-bold text-slate-600 dark:text-slate-300"
          >
            <span class="inline-flex min-w-0 items-center gap-1.5">
              <span class="material-symbols-outlined text-sm text-orange-500" aria-hidden="true">tune</span>
              {{ t('app.initialValues') }}
            </span>
            <span class="material-symbols-outlined text-sm text-slate-400" aria-hidden="true">expand_more</span>
          </summary>

          <p class="mt-2 text-[10px] leading-relaxed text-slate-500 dark:text-slate-400">
            {{ t('app.initialValuesHint') }}
          </p>

          <div v-if="templateInstanceHasModes" class="mt-3 grid grid-cols-1 gap-2 sm:grid-cols-3">
            <label class="min-w-0">
              <span class="mb-1 block text-[10px] font-bold uppercase tracking-wide text-slate-500 dark:text-slate-400">{{ t('app.initialState') }}</span>
              <select
                v-model="templateInstanceRuntime.state"
                data-testid="template-instance-state"
                class="w-full rounded-lg border-2 border-slate-200 bg-white px-2 py-2 text-xs text-slate-700 shadow-sm transition focus:border-orange-400 focus:ring-2 focus:ring-orange-100 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100 dark:focus:ring-orange-500/20"
              >
                <option v-for="state in templateInstanceWorkingStates" :key="state.Name" :value="state.Name">{{ state.Name }}</option>
              </select>
            </label>

            <label class="min-w-0">
              <span class="mb-1 block text-[10px] font-bold uppercase tracking-wide text-slate-500 dark:text-slate-400">{{ t('app.stateTrust') }}</span>
              <select
                v-model="templateInstanceRuntime.currentStateTrust"
                data-testid="template-instance-state-trust"
                class="w-full rounded-lg border-2 border-slate-200 bg-white px-2 py-2 text-xs text-slate-700 shadow-sm transition focus:border-orange-400 focus:ring-2 focus:ring-orange-100 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100 dark:focus:ring-orange-500/20"
              >
                <option v-for="trust in TRUST_OPTIONS" :key="trust" :value="trust">{{ t(`app.${trust}`) }}</option>
              </select>
            </label>

            <label class="min-w-0">
              <span class="mb-1 block text-[10px] font-bold uppercase tracking-wide text-slate-500 dark:text-slate-400">{{ t('app.statePrivacy') }}</span>
              <select
                v-model="templateInstanceRuntime.currentStatePrivacy"
                data-testid="template-instance-state-privacy"
                class="w-full rounded-lg border-2 border-slate-200 bg-white px-2 py-2 text-xs text-slate-700 shadow-sm transition focus:border-orange-400 focus:ring-2 focus:ring-orange-100 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-100 dark:focus:ring-orange-500/20"
              >
                <option v-for="privacy in PRIVACY_OPTIONS" :key="privacy" :value="privacy">{{ t(`app.${privacy}`) }}</option>
              </select>
            </label>
          </div>

          <div v-if="templateInstanceInternalVariables.length > 0" class="mt-3 space-y-2">
            <div
              v-for="variable in templateInstanceInternalVariables"
              :key="variable.Name"
              class="rounded-lg border border-slate-200 bg-white/80 p-2 dark:border-slate-700 dark:bg-slate-950/80"
            >
              <div class="mb-2 flex items-center justify-between gap-2">
                <span class="truncate text-[11px] font-bold text-slate-700 dark:text-slate-200" :title="variable.Name">{{ variable.Name }}</span>
                <span v-if="templateVariableUsesNumericBounds(variable)" class="text-[10px] font-semibold text-slate-400 dark:text-slate-500">
                  {{ templateVariableInputPlaceholder(variable) }}
                </span>
              </div>

              <div class="grid grid-cols-[minmax(0,1fr)_5.8rem_5.8rem] gap-2 max-[520px]:grid-cols-1">
                <label class="min-w-0">
                  <span class="mb-1 block text-[9px] font-bold uppercase text-slate-400 dark:text-slate-500">{{ t('app.variableValue') }}</span>
                  <select
                    v-if="templateVariableHasEnumValues(variable)"
                    v-model="templateInstanceRuntime.variables[variable.Name]"
                    :data-testid="`template-instance-variable-${variable.Name}`"
                    class="w-full min-w-0 rounded-lg border border-slate-200 bg-white px-2 py-1.5 text-xs text-slate-700 dark:border-slate-700 dark:bg-slate-900 dark:text-slate-100"
                  >
                    <option value="">{{ t('app.useTemplateDefault') }}</option>
                    <option v-for="value in variable.Values" :key="value" :value="String(value)">{{ value }}</option>
                  </select>
                  <input
                    v-else
                    v-model="templateInstanceRuntime.variables[variable.Name]"
                    :data-testid="`template-instance-variable-${variable.Name}`"
                    class="w-full min-w-0 rounded-lg border border-slate-200 bg-white px-2 py-1.5 text-xs text-slate-700 placeholder:text-slate-400 dark:border-slate-700 dark:bg-slate-900 dark:text-slate-100"
                    :placeholder="templateVariableInputPlaceholder(variable)"
                    type="text"
                  />
                </label>

                <label class="min-w-0">
                  <span class="mb-1 block text-[9px] font-bold uppercase text-slate-400 dark:text-slate-500">{{ t('app.variableTrust') }}</span>
                  <select
                    v-model="templateInstanceRuntime.variableTrusts[variable.Name]"
                    :data-testid="`template-instance-variable-trust-${variable.Name}`"
                    class="w-full min-w-0 rounded-lg border border-slate-200 bg-white px-1.5 py-1.5 text-[11px] text-slate-700 dark:border-slate-700 dark:bg-slate-900 dark:text-slate-100"
                  >
                    <option v-for="trust in TRUST_OPTIONS" :key="trust" :value="trust">{{ t(`app.${trust}`) }}</option>
                  </select>
                </label>

                <label class="min-w-0">
                  <span class="mb-1 block text-[9px] font-bold uppercase text-slate-400 dark:text-slate-500">{{ t('app.privacy') }}</span>
                  <select
                    v-model="templateInstanceRuntime.privacies[variable.Name]"
                    :data-testid="`template-instance-privacy-${variable.Name}`"
                    class="w-full min-w-0 rounded-lg border border-slate-200 bg-white px-1.5 py-1.5 text-[11px] text-slate-700 dark:border-slate-700 dark:bg-slate-900 dark:text-slate-100"
                  >
                    <option v-for="privacy in PRIVACY_OPTIONS" :key="privacy" :value="privacy">{{ t(`app.${privacy}`) }}</option>
                  </select>
                </label>
              </div>
            </div>
          </div>
        </details>

        <div class="mt-5 flex justify-end gap-3">
          <button
            type="button"
            class="inline-flex min-h-10 items-center justify-center rounded-xl border border-slate-200 bg-white px-4 text-sm font-bold text-slate-600 transition hover:bg-slate-50 disabled:cursor-not-allowed disabled:opacity-60 dark:border-slate-700 dark:bg-slate-950 dark:text-slate-300 dark:hover:bg-slate-800"
            :disabled="templateInstanceSaving"
            @click="cancelTemplateInstanceCreate"
          >
            {{ t('app.cancel') }}
          </button>
          <button
            type="button"
            data-testid="template-instance-confirm"
            class="inline-flex min-h-10 items-center justify-center gap-2 rounded-xl bg-orange-500 px-4 text-sm font-bold text-white shadow-lg shadow-orange-500/20 transition hover:bg-orange-600 disabled:cursor-not-allowed disabled:opacity-60"
            :disabled="templateInstanceSaving"
            @click="confirmTemplateInstanceCreate"
          >
            <span v-if="templateInstanceSaving" class="h-4 w-4 animate-spin rounded-full border-2 border-white/40 border-t-white" aria-hidden="true"></span>
            <span v-else class="material-symbols-outlined text-base" aria-hidden="true">add</span>
            {{ t('app.createDevice') }}
          </button>
        </div>
      </div>
    </div>

    <!-- Left Sidebar - Control Center -->
    <ControlCenter
      :device-templates="deviceTemplates"
      :templates-loading="templatesLoading"
      :nodes="nodes"
      :edges="edges"
      :canvas-pan="canvasPan"
      :canvas-zoom="canvasZoom"
      :collapsed="boardPanels.control.collapsed"
      :width="boardPanels.control.width"
      :active-section="boardPanels.control.activeSection"
      :read-only="isModelPlaybackActive || isSceneReplacementInProgress"
      :read-only-message="isSceneReplacementInProgress ? t('app.sceneReplacementInProgress') : t('app.playbackReadOnlyCloseFirst')"
      :run-board-mutation="enqueueBoardMutation"
      :class="{ 'board-panel--playback-read-only': isModelPlaybackActive || isSceneReplacementInProgress }"
      @create-device="handleCreateDevice"
      @create-devices="handleCreateDevices"
      @template-drag-start="handleTemplateDragStart"
      @template-drag-end="handleTemplateDragEnd"
      @open-rule-builder="openRuleBuilder"
      @add-spec="handleAddSpec"
      @replace-template-catalog="replaceTemplateCatalog"
      @replace-template-state="replaceTemplateState"
      @update:collapsed="handleControlCollapsedUpdate"
      @update:active-section="handleControlActiveSectionUpdate"
    />

    <!-- Right Sidebar - System Inspector -->
    <SystemInspector
      :devices="nodes"
      :device-templates="deviceTemplates"
      :environment-variables="environmentVariables"
      :rules="rules"
      :specifications="specifications"
      :focused-device-id="focusedNodeId"
      :focused-rule-id="focusedRuleId"
      :focused-spec-id="focusedSpecId"
      :collapsed="boardPanels.inspector.collapsed"
      :width="boardPanels.inspector.width"
      :active-section="boardPanels.inspector.activeSection"
      :read-only="isModelPlaybackActive"
      :rules-reordering="rulesReordering"
      :class="{ 'board-panel--playback-read-only': isModelPlaybackActive }"
      @delete-device="deleteNodeFromStatus"
      @delete-rule="deleteRule"
      @move-rule="moveRule"
      @delete-spec="deleteSpecification"
      @device-click="focusDeviceFromInspector"
      @open-rule-builder="openRuleBuilder"
      @open-control-section="openControlSection"
      @save-environment="saveEnvironmentVariables"
      @update:collapsed="handleInspectorCollapsedUpdate"
      @update:active-section="handleInspectorActiveSectionUpdate"
    >
      <template #overview>
        <div
          v-show="!isCanvasMapHiddenByOverlay && !boardPanels.inspector.collapsed"
          data-testid="canvas-map"
          class="canvas-map w-full p-3 border rounded-lg shadow-sm bg-white/90 border-slate-200 dark:bg-slate-950/90 dark:border-slate-700"
        >
          <div class="flex items-center justify-between mb-2">
            <span class="text-[10px] uppercase font-bold text-slate-400 dark:text-slate-500">{{ t('app.canvasMap') }}</span>
            <div class="canvas-map__zoom-controls flex items-center gap-1" data-testid="canvas-map-zoom-controls">
              <button
                type="button"
                class="canvas-map__tool inline-flex h-6 w-6 items-center justify-center rounded-md text-slate-500 hover:bg-slate-100 hover:text-slate-900 dark:text-slate-300 dark:hover:bg-slate-800 dark:hover:text-white"
                data-testid="canvas-map-zoom-out"
                :title="t('app.zoomOut')"
                :aria-label="t('app.zoomOut')"
                @click="adjustCanvasZoom(-ZOOM_STEP)"
              >
                <span class="material-symbols-outlined text-sm" aria-hidden="true">remove</span>
              </button>
              <label class="canvas-map__zoom-input-wrap" :title="t('app.zoomLevel')">
                <input
                  class="canvas-map__zoom-input"
                  data-testid="canvas-map-zoom-input"
                  type="number"
                  :min="Math.round(MIN_ZOOM * 100)"
                  :max="Math.round(MAX_ZOOM * 100)"
                  step="5"
                  :value="canvasZoomPercent"
                  :aria-label="t('app.zoomLevel')"
                  @input="handleCanvasMapZoomInput"
                  @change="handleCanvasMapZoomInput"
                  @keydown.stop
                />
                <span aria-hidden="true">%</span>
              </label>
              <button
                type="button"
                class="canvas-map__tool inline-flex h-6 w-6 items-center justify-center rounded-md text-slate-500 hover:bg-slate-100 hover:text-slate-900 dark:text-slate-300 dark:hover:bg-slate-800 dark:hover:text-white"
                data-testid="canvas-map-zoom-in"
                :title="t('app.zoomIn')"
                :aria-label="t('app.zoomIn')"
                @click="adjustCanvasZoom(ZOOM_STEP)"
              >
                <span class="material-symbols-outlined text-sm" aria-hidden="true">add</span>
              </button>
              <button
                type="button"
                class="canvas-map__tool inline-flex h-6 w-6 items-center justify-center rounded-md text-slate-500 hover:bg-slate-100 hover:text-slate-900 dark:text-slate-300 dark:hover:bg-slate-800 dark:hover:text-white"
                data-testid="canvas-map-fit"
                :title="t('app.fitToContent')"
                @click="fitToContent"
              >
                <span class="material-symbols-outlined text-sm">fit_screen</span>
              </button>
            </div>
          </div>

          <div
            class="canvas-map__viewport w-full h-28 rounded bg-slate-50 border border-slate-200 relative overflow-hidden shadow-inner cursor-crosshair select-none dark:bg-slate-900 dark:border-slate-700"
            data-testid="canvas-map-viewport"
            @pointerdown="onCanvasMapPointerDown"
          >
            <svg
              class="absolute inset-0 w-full h-full"
              :viewBox="canvasMapViewBox"
              preserveAspectRatio="none"
            >
              <line
                v-for="line in canvasMapLines"
                :key="line.id"
                :x1="line.x1"
                :y1="line.y1"
                :x2="line.x2"
                :y2="line.y2"
                :stroke="line.color"
                stroke-width="2"
                stroke-opacity="0.8"
                stroke-linecap="round"
              />
              <circle
                v-for="dot in canvasMapDots"
                :key="dot.id"
                :cx="dot.x + 4"
                :cy="dot.y + 4"
                r="3.6"
                :fill="dot.color"
                stroke="rgba(255,255,255,0.78)"
                stroke-width="1"
              />
              <rect
                v-if="canvasMapViewportRect"
                data-testid="canvas-map-viewport-rect"
                class="canvas-map__viewport-rect"
                :x="canvasMapViewportRect.x"
                :y="canvasMapViewportRect.y"
                :width="canvasMapViewportRect.width"
                :height="canvasMapViewportRect.height"
                rx="2"
              />
            </svg>

            <div class="absolute inset-0 border-2 border-primary/20 rounded pointer-events-none"></div>

            <div v-if="canvasMapDots.length === 0" class="absolute inset-0 flex items-center justify-center text-slate-400 dark:text-slate-500 text-xs">
              {{ t('app.noDevicesOnCanvas') }}
            </div>
          </div>
        </div>
      </template>
    </SystemInspector>

    <button
      type="button"
      class="canvas-fit-mobile"
      data-testid="canvas-fit-mobile"
      :title="t('app.fitToContent')"
      :aria-label="t('app.fitToContent')"
      @click="fitToContent"
    >
      <span class="material-symbols-outlined" aria-hidden="true">fit_screen</span>
    </button>

    <!-- Canvas Area -->
    <div class="canvas-container">
      <!-- Canvas Board -->
      <CanvasBoard
          :nodes="nodes"
          :edges="allEdges"
          :pan="canvasPan"
          :zoom="canvasZoom"
          :get-node-icon="getBoardNodeIcon"
          :get-node-label-style="getNodeLabelStyle"
          :highlighted-trace="highlightedTrace"
          :focused-node-id="focusedNodeId"
          :focused-rule-id="focusedRuleId"
          :interaction-locked="isModelPlaybackActive"
          @canvas-pointerdown="onCanvasPointerDown"
          @canvas-dragover="onCanvasDragOver"
          @canvas-drop="onCanvasDrop"
          @canvas-enter="onCanvasEnter"
          @canvas-leave="onCanvasLeave"
          @node-context="onNodeContext"
          @node-open="openNodeFromCanvas"
          @node-delete="deleteNodeFromStatus"
          @node-moved-or-resized="handleNodeMovedOrResized"
      />

      <section
        v-if="showCanvasEmptyState"
        class="pointer-events-none absolute inset-0 z-10 flex items-center justify-center px-20 py-24"
        data-testid="canvas-empty-state"
        aria-labelledby="canvas-empty-state-title"
      >
        <div class="pointer-events-auto max-w-xl text-center">
          <span class="material-symbols-outlined text-4xl text-slate-400 dark:text-slate-500" aria-hidden="true">account_tree</span>
          <h2 id="canvas-empty-state-title" class="mt-3 text-xl font-bold text-slate-800 dark:text-slate-100">
            {{ t('app.emptyCanvasTitle') }}
          </h2>
          <p class="mt-2 text-sm text-slate-500 dark:text-slate-400">
            {{ t('app.emptyCanvasDescription') }}
          </p>
          <div class="mt-5 flex flex-wrap items-center justify-center gap-2">
            <button
              type="button"
              class="inline-flex min-h-10 items-center gap-2 rounded-md bg-slate-900 px-4 text-sm font-semibold text-white shadow-sm hover:bg-slate-800 dark:bg-slate-100 dark:text-slate-900 dark:hover:bg-white"
              data-testid="empty-state-add-device"
              @click="openControlSection('devices')"
            >
              <span class="material-symbols-outlined text-lg" aria-hidden="true">add</span>
              {{ t('app.emptyCanvasAddDevice') }}
            </button>
            <button
              type="button"
              class="inline-flex min-h-10 items-center gap-2 rounded-md border border-slate-300 bg-white/90 px-4 text-sm font-semibold text-slate-700 shadow-sm hover:bg-white dark:border-slate-600 dark:bg-slate-900/90 dark:text-slate-100 dark:hover:bg-slate-900"
              data-testid="empty-state-generate-scenario"
              @click="openScenarioRecommendationPanel"
            >
              <span class="material-symbols-outlined text-lg" aria-hidden="true">auto_awesome</span>
              {{ t('app.emptyCanvasGenerateScenario') }}
            </button>
            <button
              type="button"
              class="inline-flex min-h-10 items-center gap-2 rounded-md border border-slate-300 bg-white/90 px-4 text-sm font-semibold text-slate-700 shadow-sm hover:bg-white dark:border-slate-600 dark:bg-slate-900/90 dark:text-slate-100 dark:hover:bg-slate-900"
              data-testid="empty-state-import-scene"
              @click="triggerSceneImport"
            >
              <span class="material-symbols-outlined text-lg" aria-hidden="true">upload_file</span>
              {{ t('app.emptyCanvasImportScene') }}
            </button>
          </div>
        </div>
      </section>

      <PlaybackChangePopover
        v-if="showPlaybackChangePopover && activePlaybackKind"
        :changes="activePlaybackChanges"
        :environment-changes="activePlaybackEnvironmentChanges"
        :triggered-rules="activePlaybackTriggeredRules"
        :compromised-automation-links="activePlaybackCompromisedLinks"
        :animated-edge-count="activePlaybackAnimatedEdgeCount"
        :compromised-edge-count="activePlaybackCompromisedEdgeCount"
        :state-number="activePlaybackStateIndex + 1"
        :total-states="activePlaybackStates.length"
        :kind="activePlaybackKind"
        :position="playbackChangePosition"
        :input-events="activeFuzzingStepInputEvents"
        :first-violation-state-number="firstFuzzingViolationStateNumber"
        @dismiss="dismissPlaybackChanges"
        @move="movePlaybackChanges"
      />

      <div
        v-if="draggingTplName"
        class="pointer-events-none absolute inset-4 z-20 flex items-center justify-center rounded-2xl border-2 border-dashed border-orange-400/80 bg-orange-100/15 text-sm font-extrabold text-orange-600 backdrop-blur-[1px] dark:bg-orange-500/10 dark:text-orange-200"
        data-testid="template-drop-overlay"
      >
        <span class="rounded-full border border-orange-300/70 bg-white/90 px-4 py-2 shadow-lg dark:border-orange-500/40 dark:bg-slate-900/90">
          {{ t('app.releaseTemplateToCreateDevice') }}
        </span>
      </div>

    </div>

    <!-- Responsive Action Dock - anchored left of System Inspector -->
    <div
      v-show="!isResultSurfaceVisible"
      class="board-floating-actions board-action-dock"
      :class="[
        `board-action-dock--${actionDockMode}`,
        {
          'has-activity': hasActionDockActivity
        }
      ]"
      :style="actionDockStyle"
      role="toolbar"
      :aria-hidden="isResultSurfaceVisible"
      :aria-label="t('app.boardTools')"
    >
      <button
        v-if="isActionDockPackedMode"
        type="button"
        class="board-action-dock__launcher"
        data-testid="restore-action-dock"
        :aria-label="actionDockViewportWidth >= 1280 ? t('app.actionDockSwitchExpanded') : t('app.actionDockSwitchCompact')"
        :title="actionDockViewportWidth >= 1280 ? t('app.actionDockSwitchExpanded') : t('app.actionDockSwitchCompact')"
        @click="restoreActionDockFromPacked"
      >
        <span class="material-symbols-outlined" aria-hidden="true">toolbar</span>
        <span v-if="hasActionDockActivity" class="board-action-dock__activity-dot" aria-hidden="true"></span>
      </button>

      <div
        v-if="!isActionDockPackedMode"
        class="board-action-dock__panel"
      >
        <div
          class="board-action-dock__header"
        >
          <span class="board-action-dock__title">{{ t('app.boardTools') }}</span>
          <button
            type="button"
            class="board-action-dock__toggle"
            data-testid="toggle-action-dock"
            :aria-label="actionDockToggleLabel"
            :title="actionDockToggleLabel"
            @click="cycleActionDockMode"
          >
            <span class="material-symbols-outlined" aria-hidden="true">
              {{ actionDockToggleIcon }}
            </span>
          </button>
        </div>

        <div class="board-tool-group" data-testid="run-tool-group" role="group" :aria-label="t('app.runTools')">
          <span class="board-tool-group-label">{{ t('app.runTools') }}</span>

        <div class="board-tool-wrapper group">
          <div
            v-if="simulationAnimationState.visible"
            class="board-tool-pulse bg-blue-400"
          ></div>
          <button
            type="button"
            @click="openSimulationFromActionDock"
            data-testid="open-simulation-panel"
            :disabled="traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isAnyRecommendationRunning()"
            :aria-label="isSimulating ? t('app.simulationRunning') : t('app.openSimulationSettings')"
            :aria-pressed="showSimulationPanel || simulationAnimationState.visible"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              (traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isAnyRecommendationRunning())
                ? 'bg-blue-300 cursor-not-allowed disabled:hover:scale-100'
                : 'bg-blue-500 hover:bg-blue-600'
            ]"
            :title="isSimulating ? t('app.simulationRunning') : t('app.openSimulationSettings')"
          >
            <span v-if="isSimulating" class="material-symbols-outlined animate-spin" aria-hidden="true">sync</span>
            <span v-else class="material-symbols-outlined" aria-hidden="true">play_circle</span>
            <span class="board-tool-label">{{ t('app.simulationTitle') }}</span>
            <span class="board-tool-tooltip" role="tooltip">
              {{ isSimulating ? t('app.simulationRunning') : (simulationAnimationState.visible ? t('app.simulationRunning') : t('app.openSimulationSettings')) }}
              <span v-if="simulationAnimationState.visible" class="ml-1 text-blue-300">({{ t('app.active') }})</span>
            </span>
          </button>
        </div>

        <div class="board-tool-wrapper group">
          <div v-if="isFuzzing" class="board-tool-pulse bg-indigo-400"></div>
          <button
            type="button"
            @click="openFuzzingFromActionDock"
            data-testid="open-fuzzing-panel"
            :disabled="isSceneReplacementInProgress || traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isAnyRecommendationRunning()"
            :aria-label="isSceneReplacementInProgress
              ? t('app.sceneReplacementInProgress')
              : isFuzzing ? t('app.fuzzRunning') : t('app.openFuzzSettings')"
            :aria-pressed="showFuzzingPanel"
            :class="[
              'board-tool-button text-white shadow-lg transition-all hover:scale-[1.03] hover:shadow-xl active:scale-95',
              (isSceneReplacementInProgress || traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isAnyRecommendationRunning())
                ? 'cursor-not-allowed bg-indigo-300 disabled:hover:scale-100'
                : showFuzzingPanel ? 'bg-indigo-700' : 'bg-indigo-600 hover:bg-indigo-700'
            ]"
            :title="isSceneReplacementInProgress
              ? t('app.sceneReplacementInProgress')
              : isFuzzing ? t('app.fuzzRunning') : t('app.openFuzzSettings')"
          >
            <span v-if="isFuzzing" class="material-symbols-outlined animate-spin" aria-hidden="true">sync</span>
            <span v-else class="material-symbols-outlined" aria-hidden="true">radar</span>
            <span class="board-tool-label">{{ t('app.fuzzSearch') }}</span>
            <span class="board-tool-tooltip" role="tooltip">{{ isSceneReplacementInProgress
              ? t('app.sceneReplacementInProgress')
              : isFuzzing ? t('app.fuzzRunning') : t('app.openFuzzSettings') }}</span>
          </button>
        </div>

        <div class="board-tool-wrapper group">
          <div
            v-if="traceAnimationState.visible"
            class="board-tool-pulse bg-green-400"
          ></div>
          <button
            ref="verificationActionButtonRef"
            type="button"
            @click="openVerificationFromActionDock"
            data-testid="open-verification-panel"
            :disabled="traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isAnyRecommendationRunning()"
            :aria-label="isVerifying ? t('app.verifying') : t('app.openVerificationSettings')"
            :aria-pressed="showVerificationPanel || traceAnimationState.visible"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              (traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isAnyRecommendationRunning())
                ? 'bg-green-300 cursor-not-allowed disabled:hover:scale-100'
                : 'bg-green-500 hover:bg-green-600'
            ]"
            :title="isVerifying ? t('app.verifying') : t('app.openVerificationSettings')"
          >
            <span v-if="isVerifying" class="material-symbols-outlined animate-spin" aria-hidden="true">sync</span>
            <span v-else class="material-symbols-outlined" aria-hidden="true">fact_check</span>
            <span class="board-tool-label">{{ t('app.verification') }}</span>
            <span class="board-tool-tooltip" role="tooltip">
              {{ isVerifying ? t('app.verifying') : t('app.openVerificationSettings') }}
              <span v-if="traceAnimationState.visible" class="ml-1 text-green-300">({{ t('app.active') }})</span>
            </span>
          </button>
        </div>

        <div class="board-tool-wrapper group">
          <button
            type="button"
            @click="openHistoryFromActionDock"
            data-testid="open-history-panel"
            :disabled="isModelPlaybackActive || isAnyRecommendationRunning()"
            :aria-label="isModelPlaybackActive
              ? t('app.playbackReadOnlyCloseFirst')
              : unreadFuzzNotificationCount > 0
                ? t('app.fuzzUnreadUpdates', { count: unreadFuzzNotificationCount })
                : t('app.openRunHistory')"
            :aria-pressed="showHistoryPanel"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              (isModelPlaybackActive || isAnyRecommendationRunning())
                ? 'bg-cyan-300 cursor-not-allowed disabled:hover:scale-100'
                : showHistoryPanel ? 'bg-cyan-700' : 'bg-cyan-600 hover:bg-cyan-700'
            ]"
            :title="isModelPlaybackActive ? t('app.playbackReadOnlyCloseFirst') : t('app.openRunHistory')"
          >
            <span class="material-symbols-outlined" aria-hidden="true">history</span>
            <span class="board-tool-label">{{ t('app.runHistory') }}</span>
            <span
              v-if="unreadFuzzNotificationCount > 0"
              class="absolute right-0.5 top-0.5 inline-flex h-4 min-w-4 items-center justify-center rounded-full bg-red-600 px-1 text-[9px] font-black text-white"
              data-testid="fuzz-unread-badge"
              aria-hidden="true"
            >{{ unreadFuzzNotificationCount > 99 ? '99+' : unreadFuzzNotificationCount }}</span>
            <span class="board-tool-tooltip" role="tooltip">
              {{ unreadFuzzNotificationCount > 0
                ? t('app.fuzzUnreadUpdates', { count: unreadFuzzNotificationCount })
                : t('app.openRunHistory') }}
            </span>
          </button>
        </div>
      </div>

      <div class="board-tool-separator" aria-hidden="true"></div>

      <div class="board-tool-group" data-testid="ai-tool-group" role="group" :aria-label="t('app.aiTools')">
        <span class="board-tool-group-label">{{ t('app.aiTools') }}</span>

        <div class="board-tool-wrapper group">
          <div
            v-if="isRecommendingScenario"
            class="board-tool-pulse bg-teal-400"
          ></div>
          <button
            type="button"
            @click="openScenarioRecommendationsFromActionDock"
            data-testid="open-scenario-recommendations"
            :disabled="traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isRecommendationRunningForAnother('scenario')"
            :aria-label="t('app.openScenarioRecommendations')"
            :aria-pressed="showScenarioRecommendationPanel || isRecommendingScenario"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              (traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isRecommendationRunningForAnother('scenario'))
                ? 'bg-teal-300 cursor-not-allowed disabled:hover:scale-100'
                : 'bg-teal-600 hover:bg-teal-700'
            ]"
            :title="t('app.openScenarioRecommendations')"
          >
            <span v-if="isRecommendingScenario" class="material-symbols-outlined animate-spin" aria-hidden="true">sync</span>
            <span v-else class="material-symbols-outlined" aria-hidden="true">account_tree</span>
            <span class="board-tool-label">{{ t('app.scenarioTool') }}</span>
            <span class="board-tool-tooltip" role="tooltip">
              {{ t('app.openScenarioRecommendations') }}
            </span>
          </button>
        </div>

        <div class="board-tool-wrapper group">
          <div
            v-if="isRecommendingRules"
            class="board-tool-pulse bg-amber-400"
          ></div>
          <button
            type="button"
            @click="openRuleRecommendationsFromActionDock"
            data-testid="open-rule-recommendations"
            :disabled="traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isRecommendationRunningForAnother('rule')"
            :aria-label="t('app.openRuleRecommendations')"
            :aria-pressed="showRecommendationPanel || isRecommendingRules"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              (traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isRecommendationRunningForAnother('rule'))
                ? 'bg-amber-300 cursor-not-allowed disabled:hover:scale-100'
                : 'bg-amber-500 hover:bg-amber-600'
            ]"
            :title="t('app.openRuleRecommendations')"
          >
            <span v-if="isRecommendingRules" class="material-symbols-outlined animate-spin" aria-hidden="true">sync</span>
            <span v-else class="material-symbols-outlined" aria-hidden="true">rule_settings</span>
            <span class="board-tool-label">{{ t('app.rulesTool') }}</span>
            <span class="board-tool-tooltip" role="tooltip">
              {{ t('app.openRuleRecommendations') }}
            </span>
          </button>
        </div>

        <div class="board-tool-wrapper group">
          <div
            v-if="isRecommendingDevices"
            class="board-tool-pulse bg-purple-400"
          ></div>
          <button
            type="button"
            @click="openDeviceRecommendationsFromActionDock"
            data-testid="open-device-recommendations"
            :disabled="traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isRecommendationRunningForAnother('device')"
            :aria-label="t('app.openDeviceRecommendations')"
            :aria-pressed="showDeviceRecommendationPanel || isRecommendingDevices"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              (traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isRecommendationRunningForAnother('device'))
                ? 'bg-purple-300 cursor-not-allowed disabled:hover:scale-100'
                : 'bg-purple-500 hover:bg-purple-600'
            ]"
            :title="t('app.openDeviceRecommendations')"
          >
            <span v-if="isRecommendingDevices" class="material-symbols-outlined animate-spin" aria-hidden="true">sync</span>
            <span v-else class="material-symbols-outlined" aria-hidden="true">devices_other</span>
            <span class="board-tool-label">{{ t('app.devicesTool') }}</span>
            <span class="board-tool-tooltip" role="tooltip">
              {{ t('app.openDeviceRecommendations') }}
            </span>
          </button>
        </div>

        <div class="board-tool-wrapper group">
          <div
            v-if="isRecommendingSpecs"
            class="board-tool-pulse bg-red-400"
          ></div>
          <button
            type="button"
            @click="openSpecRecommendationsFromActionDock"
            data-testid="open-spec-recommendations"
            :disabled="traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isRecommendationRunningForAnother('spec')"
            :aria-label="t('app.openSpecificationRecommendations')"
            :aria-pressed="showSpecRecommendationPanel || isRecommendingSpecs"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              (traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || isRecommendationRunningForAnother('spec'))
                ? 'bg-red-300 cursor-not-allowed disabled:hover:scale-100'
                : 'bg-red-500 hover:bg-red-600'
            ]"
            :title="t('app.openSpecificationRecommendations')"
          >
            <span v-if="isRecommendingSpecs" class="material-symbols-outlined animate-spin" aria-hidden="true">sync</span>
            <span v-else class="material-symbols-outlined" aria-hidden="true">playlist_add_check</span>
            <span class="board-tool-label">{{ t('app.specificationsTool') }}</span>
            <span class="board-tool-tooltip" role="tooltip">
              {{ t('app.openSpecificationRecommendations') }}
            </span>
          </button>
        </div>
        </div>
      </div>
    </div>

    <TraceHistoryPanel
      v-if="showHistoryPanel"
      :active-layer="activeHistoryLayer"
      :result-filter="activeHistoryResultFilter"
      :verification-tasks="verificationTasks"
      :fuzzing-tasks="fuzzingTasks"
      :simulation-tasks="simulationTasks"
      :verification-runs="verificationRuns"
      :fuzzing-runs="fuzzingRuns"
      :simulation-runs="simulationRuns"
      :loading-tasks="loadingTaskHistory"
      :loading-results="loadingResultHistory"
      :result-errors="historyResultErrors"
      :has-more-fuzzing-runs="fuzzingRunsHasMore"
      :loading-more-fuzzing-runs="loadingMoreFuzzingRuns"
      :pending-task-action-keys="pendingTaskActionKeys"
      :action-locked="historyActionLocked"
      :current-board-scope="currentFuzzingBoardScope"
      @update:active-layer="setHistoryLayer"
      @update:result-filter="setHistoryResultFilter"
      @close="closeHistoryPanel"
      @refresh-tasks="refreshHistoryTasks"
      @refresh-results="refreshHistoryResults"
      @load-more-fuzzing-runs="loadMoreFuzzingRuns"
      @watch-verification-task="watchVerificationTask"
      @watch-fuzzing-task="watchFuzzingTask"
      @watch-simulation-task="watchSimulationTask"
      @cancel-verification-task="cancelVerificationTaskFromInbox"
      @cancel-fuzzing-task="cancelFuzzingTaskFromInbox"
      @cancel-simulation-task="cancelSimulationTaskFromInbox"
      @dismiss-verification-task="dismissVerificationTask"
      @dismiss-fuzzing-task="dismissFuzzingTask"
      @dismiss-simulation-task="dismissSimulationTask"
      @open-verification-run="openVerificationRun"
      @delete-verification-run="deleteVerificationRun"
      @view-verification-trace="selectAndPlayVerificationTrace"
      @fix-verification-trace="openFixForVerificationTrace"
      @view-simulation-run="selectAndPlaySimulationTrace"
      @delete-simulation-run="deleteSimulationRun"
      @open-fuzzing-run="openFuzzingRun"
      @delete-fuzzing-run="deleteFuzzingRun"
      @view-fuzzing-finding="selectAndPlayFuzzingFinding"
      @verify-fuzzing-finding="openFormalVerificationForFuzzFinding"
    />

    <div
      v-if="miniTaskItems.length > 0"
      data-testid="mini-task-indicator"
      class="board-mini-tasks fixed z-40 w-[360px] max-w-[calc(100vw-2rem)] rounded-xl border shadow-2xl"
    >
      <div class="flex items-center justify-between border-b border-slate-100 px-3 py-2">
        <div class="flex items-center gap-2">
          <span class="material-symbols-outlined text-cyan-600 text-lg">pending_actions</span>
          <span class="text-xs font-bold text-slate-700">
            {{ t('app.backgroundTasks') }}
          </span>
        </div>
        <button
          type="button"
          class="inline-flex items-center gap-1 rounded-md px-2 py-1 text-xs font-semibold text-cyan-700 hover:bg-cyan-50"
          :disabled="isModelPlaybackActive"
          :title="isModelPlaybackActive ? t('app.playbackReadOnlyCloseFirst') : t('app.taskInbox')"
          @click="openTaskInbox"
        >
          <span class="material-symbols-outlined text-sm">inbox</span>
          {{ t('app.taskInbox') }}
        </button>
      </div>
      <div class="space-y-2 p-3">
        <div
          v-for="task in miniTaskItems.slice(0, 3)"
          :key="task.key"
          class="board-card-surface rounded-lg border p-2"
        >
          <div class="flex items-center justify-between gap-2">
            <div class="min-w-0">
              <div class="truncate text-xs font-semibold text-slate-700">
                {{ task.label }}
              </div>
              <div class="truncate text-[11px] text-slate-500">
                {{ task.status }}
              </div>
            </div>
            <button
              type="button"
              class="inline-flex h-11 w-11 shrink-0 items-center justify-center rounded-md text-slate-500 hover:bg-red-50 hover:text-red-600"
              :title="miniTaskCancelLabel(task.kind)"
              :aria-label="miniTaskCancelLabel(task.kind)"
              @click="cancelMiniTask(task.kind, task.id)"
            >
              <span class="material-symbols-outlined text-sm" aria-hidden="true">cancel</span>
            </button>
          </div>
          <div
            class="mt-2 h-1.5 overflow-hidden rounded-full bg-slate-200"
            role="progressbar"
            :aria-label="`${task.label}: ${task.status}`"
            aria-valuemin="0"
            aria-valuemax="100"
            :aria-valuenow="task.progress"
          >
            <div
              class="h-full rounded-full bg-cyan-600 transition-all"
              :style="{ width: `${task.progress}%` }"
            ></div>
          </div>
        </div>
        <button
          v-if="miniTaskItems.length > 3"
          type="button"
          class="w-full rounded-md px-2 py-1 text-xs font-semibold text-cyan-700 hover:bg-cyan-50"
          @click="openTaskInbox"
        >
          {{ t('app.viewMoreTasks', { count: miniTaskItems.length - 3 }) }}
        </button>
      </div>
    </div>

    <FuzzingPanel
      v-if="showFuzzingPanel"
      :form="fuzzingForm"
      :specifications="specifications"
      :running="isFuzzing"
      :progress="asyncFuzzingTask.progress"
      :status="asyncFuzzingTask.status"
      :task-id="asyncFuzzingTask.taskId"
      :cancelling="cancellingFuzzingTask"
      :error="fuzzingError"
      :configuration-error="effectiveFuzzingConfigurationError"
      :workload="fuzzingWorkload"
      :workload-limit="fuzzingWorkloadLimit"
      :workload-ready="fuzzingWorkloadReady"
      :workload-loading="fuzzingWorkloadPreviewLoading"
      :workload-error="fuzzingWorkloadPreviewError"
      :paper-domain-preview="paperDomainPreview"
      :paper-domain-loading="paperDomainPreviewLoading"
      :paper-domain-error="paperDomainPreviewError"
      :notice="fuzzingSettingsNotice"
      :preflight-blocked="fuzzingContentCommandUnsupported"
      :preflight-message="fuzzingContentCommandUnsupported ? t('app.fuzzContentCommandPreflightBlocked') : null"
      :frozen-task="fuzzingWatchedTask"
      @submit="runFuzzing"
      @cancel="cancelAsyncFuzzing"
      @close="showFuzzingPanel = false"
      @refresh-paper-domain="refreshPaperDomainPreview"
      @refresh-workload="refreshFuzzingWorkloadPreview"
    />

    <!-- Verification Panel -->
    <div 
      v-if="showVerificationPanel"
      data-testid="verification-panel"
      class="board-floating-panel board-run-panel board-surface-panel fixed top-20 z-30 w-72 max-w-[calc(100vw-2rem)] rounded-2xl shadow-2xl border overflow-hidden"
      role="dialog"
      aria-labelledby="verification-panel-title"
      tabindex="-1"
    >
      <!-- Verification Header with gradient -->
      <div class="relative overflow-hidden">
        <div class="absolute inset-0 bg-gradient-to-br from-green-500 to-emerald-600"></div>
        <div class="absolute inset-0 bg-[url('data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iNjAiIGhlaWdodD0iNjAiIHZpZXdCb3g9IjAgMCA2MCA2MCIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj48ZyBmaWxsPSJub25lIiBmaWxsLXJ1bGU9ImV2ZW5vZGQiPjxwYXRoIGQ9Ik0zNiAxOGMtOS45NDEgMC0xOCA4LjA1OS0xOCAxOHM4LjA1OSAxOCAxOCAxOCAxOC04LjA1OSAxOC0xOC04LjA1OS0xOC0xOC0xOHptMCAzMmMtNy43MzIgMC0xNC02LjI2OC0xNC0xNHM2LjI2OC0xNCAxNC0xNCAxNCA2LjI2OCAxNCAxNC02LjI2OCAxNC0xNCAxNHoiIGZpbGw9IiNmZmYiIGZpbGwtb3BhY2l0eT0iLjA1Ii8+PC9nPjwvc3ZnPg==')] opacity-30"></div>
        <div class="relative flex items-center justify-between p-4">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-green-500 backdrop-blur-sm rounded-xl flex items-center justify-center shadow-lg">
              <span class="material-symbols-outlined text-white text-xl">verified_user</span>
            </div>
            <div>
              <h3 id="verification-panel-title" class="text-black font-bold text-base">{{ t('app.verification') }}</h3>
              <p class="text-green-900/80 text-xs">{{ t('app.configureAndRunVerification') }}</p>
            </div>
          </div>
          <button
            ref="verificationPanelCloseButtonRef"
            type="button"
            @click="closeVerificationPanel"
            data-testid="close-verification-panel"
            :aria-label="t('app.close')"
            :title="t('app.close')"
            class="w-8 h-8 flex items-center justify-center rounded-lg text-black/70 hover:text-black hover:bg-black/10 transition-all"
          >
            <span class="material-symbols-outlined" aria-hidden="true">close</span>
          </button>
        </div>
      </div>
      <!-- Verification Options -->
      <div class="p-3 space-y-3 bg-gradient-to-b from-white to-green-50/30">
        <section
          v-if="fuzzVerificationHandoff"
          data-testid="fuzz-verification-handoff"
          class="rounded-lg border border-indigo-200 bg-indigo-50 px-3 py-2.5 text-[11px] leading-4 text-indigo-950"
          aria-labelledby="fuzz-verification-handoff-title"
        >
          <h4 id="fuzz-verification-handoff-title" class="font-bold">
            {{ t('app.fuzzVerificationHandoffTitle', { run: fuzzVerificationHandoff.runId }) }}
          </h4>
          <p v-if="fuzzVerificationHandoff.specificationLabel" class="mt-1 break-words font-semibold">
            {{ t('app.fuzzVerificationHandoffTarget', { specification: fuzzVerificationHandoff.specificationLabel }) }}
          </p>
          <p class="mt-1">{{ t('app.fuzzVerificationHandoffCurrentBoard') }}</p>
          <p
            v-if="!fuzzVerificationHandoff.targetPresent"
            class="mt-2 rounded-md border border-amber-300 bg-amber-50 px-2 py-1.5 font-semibold text-amber-950"
            role="alert"
          >
            {{ t('app.fuzzVerificationHandoffTargetMissing') }}
          </p>
          <p
          v-else-if="fuzzVerificationHandoff.boardDrifted"
            class="mt-2 rounded-md border border-amber-300 bg-amber-50 px-2 py-1.5 font-semibold text-amber-950"
          >
            {{ t('app.fuzzVerificationHandoffScopeChanged') }}
          </p>
        </section>

        <!-- Attack Mode -->
        <div class="p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
          <div class="flex items-center justify-between gap-3">
            <div class="flex min-w-0 items-center gap-3">
            <div class="w-8 h-8 bg-red-100 rounded-lg flex items-center justify-center">
              <span class="material-symbols-outlined text-red-500 text-lg">warning</span>
            </div>
            <label class="text-xs font-bold text-slate-700 uppercase tracking-wide">
              {{ t('app.attackMode') }}
            </label>
            </div>
            <button
            type="button"
            data-testid="verification-attack-toggle"
            :disabled="isVerifying || (!verificationForm.isAttack && !hasModeledAttackEffect)"
            :title="!hasModeledAttackEffect ? t('app.attackNoModeledEffect') : undefined"
            @click="verificationForm.isAttack = !verificationForm.isAttack"
            class="relative inline-flex h-6 w-11 items-center rounded-full transition-colors disabled:cursor-not-allowed disabled:opacity-60"
            :class="verificationForm.isAttack ? 'bg-red-500' : 'bg-slate-300'"
          >
            <span
              class="h-4 w-4 rounded-full bg-white shadow-md transition-all duration-300 ease-spring"
              :style="{
                transform: verificationForm.isAttack ? 'translateX(20px)' : 'translateX(4px)',
                willChange: 'transform'
              }"
            />
            </button>
          </div>
          <p
            v-if="!hasModeledAttackEffect"
            data-testid="verification-attack-unavailable"
            class="mt-2 text-[10px] leading-4 text-amber-700"
          >
            {{ t('app.attackNoModeledEffect') }}
          </p>
        </div>

        <!-- Attack budget (visible when attack is enabled) -->
        <div v-if="verificationForm.isAttack && hasModeledAttackEffect" class="p-3 bg-red-50 rounded-xl border border-red-200/60">
          <div class="mb-2 flex items-center justify-between gap-2">
            <label for="verification-attack-budget" class="min-w-0 text-[10px] font-bold text-red-700 uppercase tracking-wide">
              {{ t('app.attackBudgetLabel') }}:
              <span class="text-red-500">{{ verificationForm.attackBudget }} / {{ attackBudgetMax }}</span>
            </label>
            <InfoTooltip
              :text="t('app.verificationAttackBudgetHint', { limit: attackBudgetMax, surface: attackSurfacePointCount })"
              :label="t('app.showHelpFor', { topic: t('app.attackBudgetLabel') })"
              placement="left"
              tone="danger"
              test-id="verification-attack-budget-help"
            />
          </div>
          <input
            id="verification-attack-budget"
            v-model.number="verificationForm.attackBudget"
            data-testid="verification-attack-budget"
            :disabled="isVerifying"
            type="range"
            min="1"
            :max="attackBudgetMax"
            :aria-invalid="Boolean(verificationAttackConfigurationError)"
            class="w-full h-2 bg-red-200 rounded-lg appearance-none cursor-pointer accent-red-500 disabled:cursor-not-allowed disabled:opacity-60"
          />
          <div class="flex justify-between text-[10px] text-red-400 mt-1">
            <span>1</span>
            <span>{{ attackBudgetMax }}</span>
          </div>
          <p v-if="attackBudgetIsCapped" class="mt-1 text-[10px] font-semibold leading-4 text-amber-700" data-testid="verification-attack-budget-cap">
            {{ t('app.attackBudgetCappedHint', { surface: attackSurfacePointCount, limit: attackBudgetMax }) }}
          </p>
          <p v-if="verificationAttackConfigurationError" class="mt-1 text-[10px] font-semibold leading-4 text-red-700" data-testid="verification-attack-budget-invalid">
            {{ verificationAttackConfigurationError }}
          </p>
        </div>

        <!-- Privacy Analysis -->
        <div class="p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
          <div class="flex items-center justify-between gap-3">
            <div class="flex min-w-0 items-center gap-3">
            <div class="w-8 h-8 bg-purple-100 rounded-lg flex items-center justify-center">
              <span class="material-symbols-outlined text-purple-500 text-lg">security</span>
            </div>
            <label class="text-xs font-bold text-slate-700 uppercase tracking-wide">
              {{ t('app.privacyAnalysis') }}
            </label>
            <InfoTooltip
              :text="hasPrivacySpecification ? t('app.privacyModelRequiredHint') : t('app.privacyModelHint')"
              :label="t('app.showHelpFor', { topic: t('app.privacyAnalysis') })"
              placement="left"
              tone="privacy"
              test-id="verification-privacy-help"
            />
            </div>
            <button
            type="button"
            data-testid="verification-privacy-toggle"
            :disabled="isVerifying || hasPrivacySpecification"
            @click="verificationForm.enablePrivacy = !verificationForm.enablePrivacy"
            class="relative inline-flex h-6 w-11 items-center rounded-full transition-colors disabled:cursor-not-allowed disabled:opacity-60"
            :class="verificationForm.enablePrivacy ? 'bg-purple-500' : 'bg-slate-300'"
          >
            <span
              class="h-4 w-4 rounded-full bg-white shadow-md transition-all duration-300 ease-spring"
              :style="{
                transform: verificationForm.enablePrivacy ? 'translateX(20px)' : 'translateX(4px)',
                willChange: 'transform'
              }"
            />
            </button>
          </div>
          <p v-if="hasPrivacySpecification" class="mt-2 text-[10px] font-semibold leading-4 text-purple-700" data-testid="verification-privacy-required">
            {{ t('app.privacyModelRequiredStatus') }}
          </p>
        </div>

        <!-- Run Mode -->
        <div class="p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
          <div class="flex items-center gap-3 mb-2">
            <div class="w-8 h-8 bg-blue-100 rounded-lg flex items-center justify-center">
              <span class="material-symbols-outlined text-blue-500 text-lg">schedule</span>
            </div>
            <label class="text-xs font-bold text-slate-700 uppercase tracking-wide">
              {{ t('app.runMode') }}
            </label>
          </div>
          <div class="grid grid-cols-2 gap-1 rounded-lg bg-slate-100 p-1">
            <button
              type="button"
              :disabled="isVerifying"
              @click="verificationForm.isAsync = false"
              data-testid="verification-mode-sync"
              :aria-pressed="!verificationForm.isAsync"
              :title="t('app.syncVerificationModeHint')"
              class="min-w-0 rounded-md px-2 py-1.5 text-[11px] font-bold transition-all disabled:cursor-not-allowed disabled:opacity-60"
              :class="!verificationForm.isAsync ? 'bg-white text-green-700 shadow-sm' : 'text-slate-500 hover:text-slate-700'"
            >
              {{ t('app.runNow') }}
            </button>
            <button
              type="button"
              :disabled="isVerifying"
              @click="verificationForm.isAsync = true"
              data-testid="verification-mode-async"
              :aria-pressed="verificationForm.isAsync"
              :title="t('app.asyncVerificationModeHint')"
              class="min-w-0 rounded-md px-2 py-1.5 text-[11px] font-bold transition-all disabled:cursor-not-allowed disabled:opacity-60"
              :class="verificationForm.isAsync ? 'bg-white text-blue-700 shadow-sm' : 'text-slate-500 hover:text-slate-700'"
            >
              {{ t('app.backgroundTask') }}
            </button>
          </div>
          <p class="mt-2 text-[11px] leading-snug text-slate-500">
            {{ verificationForm.isAsync ? t('app.asyncVerificationModeHint') : t('app.syncVerificationModeHint') }}
          </p>
        </div>

        <!-- Async Progress (visible when async verification is running) -->
        <div v-if="isVerifying && asyncVerificationActive" class="space-y-1">
          <div class="flex items-center justify-between text-xs">
            <span class="text-green-600 font-medium">{{ asyncVerificationTask.status }}</span>
            <div v-if="asyncVerificationTask.taskId" class="flex items-center gap-2">
              <span class="text-green-600 font-bold">{{ asyncVerificationTask.progress }}%</span>
              <button
                type="button"
                class="w-6 h-6 inline-flex items-center justify-center rounded-md border border-green-200 text-green-700 hover:bg-green-50 disabled:opacity-50 disabled:cursor-not-allowed"
                :disabled="cancellingVerificationTask"
                :title="t('app.cancelVerificationTask')"
                @click="cancelAsyncVerification"
              >
                <span class="material-symbols-outlined text-sm">{{ cancellingVerificationTask ? 'hourglass_empty' : 'cancel' }}</span>
              </button>
            </div>
          </div>
          <div class="w-full h-2 bg-green-200 rounded-full overflow-hidden">
            <div
              class="h-full bg-green-500 transition-all duration-500 ease-out"
              :class="{ 'animate-pulse': !asyncVerificationTask.taskId }"
              :style="{ width: asyncVerificationTask.taskId ? `${asyncVerificationTask.progress}%` : '35%' }"
            />
          </div>
        </div>

        <!-- Run Verification Button -->
        <button
          @click="runVerification"
          data-testid="run-verification"
          :disabled="isVerifying || Boolean(verificationRunBlockedReason)"
          :title="verificationRunBlockedReason || undefined"
          class="w-full py-2.5 bg-green-600 hover:bg-green-700 disabled:bg-green-300 text-white rounded-lg text-xs font-bold uppercase tracking-wider transition-all shadow-md hover:shadow-lg hover:scale-[1.02] active:scale-[0.98] flex items-center justify-center gap-2 disabled:cursor-not-allowed disabled:hover:scale-100"
        >
          <template v-if="!isBoardDataReady && failedBoardDataKeys.length === 0">
            <span class="material-symbols-outlined text-sm animate-spin">sync</span>
            {{ t('app.loading') }}
          </template>
          <template v-else-if="isVerifying">
            <span class="material-symbols-outlined text-sm animate-spin">sync</span>
            {{ t('app.verifying') }}
          </template>
          <template v-else>
            <span class="material-symbols-outlined text-sm">play_arrow</span>
            {{ verificationForm.isAsync ? t('app.createVerificationTask') : t('app.runVerificationNow') }}
          </template>
        </button>
      </div>
    </div>

    <!-- Scenario Recommendation Panel -->
    <div
      v-if="showScenarioRecommendationPanel"
      data-testid="scenario-recommendation-panel"
      class="board-floating-panel board-recommendation-panel board-surface-panel fixed top-20 z-30 w-[28rem] max-w-[calc(100vw-2rem)] rounded-2xl shadow-2xl border overflow-hidden"
    >
      <div class="relative overflow-hidden">
        <div class="absolute inset-0 bg-gradient-to-br from-teal-500 to-cyan-600"></div>
        <div class="relative flex items-center justify-between p-4">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-teal-600 backdrop-blur-sm rounded-xl flex items-center justify-center shadow-lg">
              <span class="material-symbols-outlined text-white text-xl">account_tree</span>
            </div>
            <div>
              <h3 class="text-black font-bold text-base">{{ t('app.scenarioRecommendations') }}</h3>
              <p class="text-black/70 text-xs">{{ t('app.aiPoweredScenarioSuggestions') }}</p>
            </div>
          </div>
          <button
            type="button"
            @click="closeScenarioRecommendationPanel"
            data-testid="close-scenario-recommendations"
            :aria-label="t('app.close')"
            :title="t('app.close')"
            class="w-8 h-8 flex items-center justify-center rounded-lg text-black/70 hover:text-black hover:bg-black/10 transition-all"
          >
            <span class="material-symbols-outlined" aria-hidden="true">close</span>
          </button>
        </div>
      </div>

      <div class="p-3 space-y-3 bg-gradient-to-b from-white to-teal-50/30 max-h-[560px] overflow-y-auto">
        <div class="grid grid-cols-3 gap-2 rounded-lg border border-teal-100 bg-white p-2">
          <label class="text-xs font-medium text-slate-600">
            {{ t('app.devicesTool') }}
            <input
              v-model.number="scenarioRecommendationFilters.maxDevices"
              :disabled="isRecommendingScenario"
              type="number"
              min="1"
              max="10"
              class="mt-1 w-full rounded-md border border-slate-200 bg-white px-2 py-1.5 text-xs text-slate-700 focus:outline-none focus:ring-2 focus:ring-teal-200 disabled:bg-slate-100"
            />
          </label>
          <label class="text-xs font-medium text-slate-600">
            {{ t('app.rulesTool') }}
            <input
              v-model.number="scenarioRecommendationFilters.maxRules"
              :disabled="isRecommendingScenario"
              type="number"
              min="1"
              max="10"
              class="mt-1 w-full rounded-md border border-slate-200 bg-white px-2 py-1.5 text-xs text-slate-700 focus:outline-none focus:ring-2 focus:ring-teal-200 disabled:bg-slate-100"
            />
          </label>
          <label class="text-xs font-medium text-slate-600">
            {{ t('app.specificationsTool') }}
            <input
              v-model.number="scenarioRecommendationFilters.maxSpecs"
              :disabled="isRecommendingScenario"
              type="number"
              min="1"
              max="10"
              class="mt-1 w-full rounded-md border border-slate-200 bg-white px-2 py-1.5 text-xs text-slate-700 focus:outline-none focus:ring-2 focus:ring-teal-200 disabled:bg-slate-100"
            />
          </label>
        </div>

        <label class="block rounded-lg border border-teal-100 bg-white p-2 text-xs font-medium text-slate-600">
          {{ t('app.recommendationScenario') }}
          <textarea
            v-model.trim="scenarioRecommendationFilters.userRequirement"
            :disabled="isRecommendingScenario"
            rows="3"
            :maxlength="AI_RECOMMENDATION_REQUIREMENT_MAX_LENGTH"
            :placeholder="t('app.scenarioRecommendationPlaceholder')"
            class="mt-1 w-full resize-none rounded-md border border-slate-200 bg-white px-2 py-1.5 text-xs leading-relaxed text-slate-700 focus:outline-none focus:ring-2 focus:ring-teal-200 disabled:bg-slate-100"
          ></textarea>
          <span class="mt-1 block text-[10px] font-normal leading-snug text-slate-400">
            {{ t('app.scenarioRecommendationBasisHint') }}
          </span>
        </label>

        <button
          type="button"
          data-testid="generate-scenario-recommendation"
          @click="fetchScenarioRecommendation"
          :disabled="isRecommendationRunningForAnother('scenario')"
          :class="[
            'flex w-full items-center justify-center gap-2 rounded-lg px-3 py-2.5 text-sm font-bold text-white shadow-sm transition-all active:scale-[0.98] disabled:cursor-not-allowed disabled:opacity-60',
            isRecommendingScenario ? 'bg-red-500 hover:bg-red-600' : 'bg-teal-600 hover:bg-teal-700'
          ]"
        >
          <span class="material-symbols-outlined text-base">
            {{ isRecommendingScenario ? 'stop' : 'auto_awesome' }}
          </span>
          {{ isRecommendingScenario ? t('app.stopScenarioRecommendation') : t('app.generateScenarioRecommendation') }}
        </button>

        <RecommendationProgressStatus
          v-if="isRecommendingScenario"
          kind="scenario"
          :elapsed-seconds="recommendationProgressElapsed"
          :stage="recommendationProgressStage"
          :template-count="deviceTemplates.length"
          :device-count="nodes.length"
          :rule-count="rules.length"
          :spec-count="specifications.length"
        />

        <div
          v-if="scenarioRecommendationMessage && !isRecommendingScenario"
          class="rounded-lg border border-teal-100 bg-teal-50 px-3 py-2 text-xs font-medium text-teal-700"
        >
          {{ scenarioRecommendationMessage }}
        </div>
        <div
          v-if="scenarioRecommendationResult && !isRecommendingScenario"
          data-testid="scenario-candidate-accounting"
          class="rounded-lg border border-slate-200 bg-white px-3 py-2 text-xs leading-relaxed text-slate-600"
        >
          {{ t('app.recommendationCandidateSummary', {
            raw: scenarioRecommendationResult.rawCandidateCount,
            inspected: scenarioRecommendationResult.inspectedCount,
            kept: scenarioRecommendationResult.validatedCount,
            filtered: scenarioRecommendationResult.filteredCount,
            truncated: scenarioRecommendationResult.truncatedCount
          }) }}
        </div>
        <div
          v-if="scenarioRecommendationResult?.filteredCount && scenarioRecommendationResult.filteredCount > 0 && !isRecommendingScenario"
          class="rounded-lg border border-slate-200 bg-slate-50 px-3 py-2 text-xs font-medium text-slate-600"
        >
          <p>{{ t('app.recommendationFilteredNotice', { count: scenarioRecommendationResult.filteredCount }) }}</p>
          <ul
            v-if="scenarioRecommendationResult.filteredItems?.length"
            class="mt-1 max-h-32 list-disc space-y-0.5 overflow-y-auto pl-4 pr-1 font-normal leading-relaxed"
          >
            <li
              v-for="(item, index) in scenarioRecommendationResult.filteredItems"
              :key="`${item.type || 'item'}-${item.index || index}-${item.reasonCode || item.reason}`"
            >
              {{ formatRecommendationFilteredItem(item) }}
            </li>
          </ul>
          <p v-else class="mt-1 font-normal text-slate-500">
            {{ t('app.recommendationFilteredNoDetails') }}
          </p>
        </div>
        <div
          v-if="scenarioRecommendationResult?.adjustedCount && scenarioRecommendationResult.adjustedCount > 0 && !isRecommendingScenario"
          data-testid="scenario-adjusted-items"
          class="rounded-lg border border-amber-200 bg-amber-50 px-3 py-2 text-xs font-medium text-amber-800"
        >
          <p>{{ t('app.recommendationAdjustedNotice', { count: scenarioRecommendationResult.adjustedCount }) }}</p>
          <ul class="mt-1 max-h-36 list-disc space-y-0.5 overflow-y-auto pl-4 pr-1 font-normal leading-relaxed">
            <li
              v-for="(item, index) in scenarioRecommendationResult.adjustedItems || []"
              :key="`${item.type || 'item'}-${item.index || index}-${item.reasonCode || item.reason}`"
            >
              {{ formatRecommendationAdjustmentItem(item) }}
            </li>
          </ul>
        </div>

        <div v-if="isRecommendingScenario" class="flex flex-col items-center justify-center py-10">
          <div class="relative">
            <span class="material-symbols-outlined text-teal-500 text-5xl animate-spin">sync</span>
            <div class="absolute inset-0 bg-teal-400 rounded-full animate-ping opacity-20"></div>
          </div>
          <p class="text-slate-600 text-sm mt-4 font-medium">{{ t('app.designingScenario') }}</p>
          <p class="text-slate-400 text-xs mt-1">{{ t('app.generatingCoupledScenario') }}</p>
        </div>

        <div v-else-if="!scenarioRecommendationRequested" class="flex flex-col items-center justify-center py-10">
          <div class="w-16 h-16 bg-teal-50 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-teal-400 text-3xl">tune</span>
          </div>
          <p class="text-slate-600 text-sm font-medium mt-2">{{ t('app.configureRecommendationParameters') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.clickGenerateScenario') }}</p>
        </div>

        <div v-else-if="!recommendedScenarioScene" class="flex flex-col items-center justify-center py-10">
          <div class="w-16 h-16 bg-slate-100 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-slate-300 text-3xl">account_tree</span>
          </div>
          <p class="text-slate-600 text-sm font-medium mt-2">{{ t('app.noRecommendationsAvailable') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.recommendationEmptyGuidance') }}</p>
        </div>

        <div v-else class="space-y-3">
          <div class="rounded-xl border border-slate-200 bg-white p-3 shadow-sm">
            <div class="flex items-start justify-between gap-3">
              <div class="min-w-0">
                <h4 class="truncate text-sm font-bold text-slate-800">
                  {{ localizedRecommendationText(scenarioRecommendationResult?.scenarioName, t('app.scenarioRecommendations')) }}
                </h4>
                <p v-if="scenarioRecommendationResult?.rationale" class="mt-1 text-xs leading-relaxed text-slate-500">
                  {{ localizedRecommendationText(scenarioRecommendationResult.rationale, t('app.recommendedBasedOnCurrentDevices')) }}
                </p>
              </div>
              <div class="shrink-0 rounded-full bg-teal-100 px-2 py-1 text-xs font-semibold text-teal-700">
                {{ t('app.scenarioSummaryCount', { count: scenarioRecommendationResult?.count || 0 }) }}
              </div>
            </div>

            <div class="mt-3 grid grid-cols-4 gap-2 text-center">
              <div class="rounded-lg bg-slate-50 px-2 py-2">
                <div class="text-base font-bold text-slate-800">{{ recommendedScenarioScene.devices.length }}</div>
                <div class="text-[10px] text-slate-500">{{ t('app.devicesTool') }}</div>
              </div>
              <div class="rounded-lg bg-slate-50 px-2 py-2">
                <div class="text-base font-bold text-slate-800">{{ recommendedScenarioScene.environmentVariables.length }}</div>
                <div class="text-[10px] text-slate-500">{{ t('app.environmentPool') }}</div>
              </div>
              <div class="rounded-lg bg-slate-50 px-2 py-2">
                <div class="text-base font-bold text-slate-800">{{ recommendedScenarioScene.rules.length }}</div>
                <div class="text-[10px] text-slate-500">{{ t('app.rulesTool') }}</div>
              </div>
              <div class="rounded-lg bg-slate-50 px-2 py-2">
                <div class="text-base font-bold text-slate-800">{{ recommendedScenarioScene.specs.length }}</div>
                <div class="text-[10px] text-slate-500">{{ t('app.specificationsTool') }}</div>
              </div>
            </div>

            <div
              class="mt-3 flex items-start gap-2 rounded-lg border px-2.5 py-2 text-xs"
              :class="scenarioRecommendationResult?.verificationReady
                ? 'border-emerald-200 bg-emerald-50 text-emerald-800'
                : 'border-amber-200 bg-amber-50 text-amber-900'"
            >
              <span class="material-symbols-outlined text-base" aria-hidden="true">
                {{ scenarioRecommendationResult?.verificationReady ? 'verified' : 'info' }}
              </span>
              <div>
                <div class="font-semibold">
                  {{ scenarioRecommendationResult?.verificationReady
                    ? t('app.scenarioVerificationReady')
                    : t('app.scenarioVerificationNotReady') }}
                </div>
                <ul v-if="scenarioRecommendationResult?.readinessIssues.length" class="mt-1 list-disc pl-4">
                  <li v-for="issue in scenarioRecommendationResult.readinessIssues" :key="issue.code">
                    {{ t(`app.scenarioReadiness.${issue.code}`) }}
                  </li>
                </ul>
              </div>
            </div>
          </div>

          <details class="rounded-xl border border-slate-200 bg-white p-3 text-xs">
            <summary class="flex cursor-pointer items-center gap-1 font-semibold text-teal-700">
              <span class="material-symbols-outlined text-sm">visibility</span>
              {{ t('app.viewScenarioDetails') }}
            </summary>
            <div class="mt-3 space-y-3 text-slate-600">
              <div>
                <div class="mb-1 font-semibold text-slate-700">{{ t('app.deviceList') }}</div>
                <div class="space-y-1">
                  <div
                    v-for="device in recommendedScenarioScene.devices"
                    :key="device.id"
                    class="rounded bg-slate-50 px-2 py-1.5"
                  >
                    <div class="font-medium text-slate-700">{{ device.label }} · {{ device.templateName }}</div>
                    <div v-if="scenarioDeviceHasStateMachine(device)" class="mt-0.5 text-[11px] text-slate-500">
                      {{ t('app.scenarioDeviceRuntime', {
                        state: device.state,
                        trust: device.currentStateTrust ? t(`app.${device.currentStateTrust}`) : t('app.unknown'),
                        privacy: device.currentStatePrivacy ? t(`app.${device.currentStatePrivacy}`) : t('app.unknown')
                      }) }}
                    </div>
                    <div v-else class="mt-0.5 text-[11px] text-slate-500">
                      {{ t('app.scenarioStatelessDeviceRuntime') }}
                    </div>
                    <div v-if="device.variables?.length" class="mt-0.5 text-[11px] text-slate-500">
                      {{ t('app.scenarioLocalVariables', {
                        values: device.variables.map(variable => `${variable.name}=${variable.value} (${variable.trust ? t(`app.${variable.trust}`) : t('app.unknown')})`).join('，')
                      }) }}
                    </div>
                    <div v-if="device.privacies?.length" class="mt-0.5 text-[11px] text-slate-500">
                      {{ t('app.scenarioLocalSensitivities', {
                        values: device.privacies.map(item => `${item.name}=${t(`app.${item.privacy}`)}`).join('，')
                      }) }}
                    </div>
                  </div>
                </div>
              </div>
              <div v-if="recommendedScenarioScene.environmentVariables.length">
                <div class="mb-1 font-semibold text-slate-700">{{ t('app.environmentPool') }}</div>
                <ul class="space-y-1">
                  <li
                    v-for="variable in recommendedScenarioScene.environmentVariables"
                    :key="variable.name"
                    class="rounded bg-slate-50 px-2 py-1"
                  >
                    {{ t('app.scenarioEnvironmentRuntime', {
                      name: variable.name,
                      value: variable.value ?? t('app.empty'),
                      trust: t(`app.${variable.trust}`),
                      privacy: t(`app.${variable.privacy}`)
                    }) }}
                  </li>
                </ul>
              </div>
              <div v-if="recommendedScenarioScene.rules.length">
                <div class="mb-1 font-semibold text-slate-700">{{ t('app.globalRules') }}</div>
                <div class="mb-2 flex items-start gap-1.5 rounded border border-amber-200 bg-amber-50 px-2 py-1.5 text-[10px] leading-4 text-amber-900">
                  <span class="material-symbols-outlined text-sm" aria-hidden="true">low_priority</span>
                  <span>{{ t('app.ruleExecutionOrderHint') }}</span>
                </div>
                <ul class="space-y-1">
                  <li v-for="(rule, index) in recommendedScenarioScene.rules" :key="index" class="rounded bg-slate-50 px-2 py-1.5">
                    <div class="flex items-center gap-1.5 font-medium text-slate-700">
                      <span class="rounded bg-amber-100 px-1 py-0.5 text-[9px] font-bold text-amber-800">#{{ index + 1 }}</span>
                      <span>{{ rule.name || t('app.ruleNumber', { number: index + 1 }) }}</span>
                    </div>
                    <div class="mt-0.5 text-[11px] text-slate-500">
                      {{ t('app.scenarioRuleSemantics', {
                        triggers: rule.sources.map(formatScenarioRuleSource).join(` ${t('app.and')} `),
                        action: formatScenarioRuleAction(rule)
                      }) }}
                    </div>
                  </li>
                </ul>
              </div>
              <div v-if="recommendedScenarioScene.specs.length">
                <div class="mb-1 font-semibold text-slate-700">{{ t('app.specificationsTool') }}</div>
                <ul class="space-y-1">
                  <li v-for="(spec, index) in recommendedScenarioScene.specs" :key="spec.id" class="rounded bg-slate-50 px-2 py-1.5">
                    <div class="font-medium text-slate-700">{{ getSpecResultDisplayTitle(spec, index) }}</div>
                    <div class="mt-0.5 break-all font-mono text-[11px] text-slate-500">
                      {{ t('app.formulaPreview') }}: {{ formatScenarioSpecFormula(spec) }}
                    </div>
                  </li>
                </ul>
              </div>
            </div>
          </details>

          <div class="grid grid-cols-2 gap-2">
            <button
              type="button"
              data-testid="export-recommended-scenario"
              class="flex items-center justify-center gap-2 rounded-lg border border-teal-200 bg-white px-3 py-2 text-sm font-bold text-teal-700 transition hover:bg-teal-50"
              @click="exportRecommendedScenario"
            >
              <span class="material-symbols-outlined text-base">download</span>
              {{ t('app.exportScenarioJson') }}
            </button>
            <button
              type="button"
              data-testid="apply-recommended-scenario"
              class="flex items-center justify-center gap-2 rounded-lg bg-teal-600 px-3 py-2 text-sm font-bold text-white shadow-sm transition hover:bg-teal-700"
              :disabled="isImportingScene"
              @click="applyRecommendedScenario"
            >
              <span class="material-symbols-outlined text-base">playlist_add_check</span>
              {{ t('app.replaceCurrentScene') }}
            </button>
          </div>

          <p class="px-1 text-[10px] leading-relaxed text-slate-400">
            {{ t('app.applyScenarioHint') }}
          </p>
        </div>
      </div>
    </div>

    <!-- Rule Recommendation Panel -->
    <div 
      v-if="showRecommendationPanel"
      data-testid="rule-recommendation-panel"
      class="board-floating-panel board-recommendation-panel board-surface-panel fixed top-20 z-30 w-96 max-w-[calc(100vw-2rem)] rounded-2xl shadow-2xl border overflow-hidden"
    >
      <!-- Recommendation Header with gradient -->
      <div class="relative overflow-hidden">
        <div class="absolute inset-0 bg-gradient-to-br from-amber-500 to-orange-600"></div>
        <div class="absolute inset-0 bg-[url('data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iNjAiIGhlaWdodD0iNjAiIHZpZXdCb3g9IjAgMCA2MCA2MCIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj48ZyBmaWxsPSJub25lIiBmaWxsLXJ1bGU9ImV2ZW5vZGQiPjxwYXRoIGQ9Ik0zNiAxOGMtOS45NDEgMC0xOCA4LjA1OS0xOCAxOHM4LjA1OSAxOCAxOCAxOCAxOC04LjA1OSAxOC0xOC04LjA1OS0xOC0xOC0xOHptMCAzMmMtNy43MzIgMC0xNC02LjI2OC0xNC0xNHM2LjI2OC0xNCAxNC0xNCAxNCA2LjI2OCAxNCAxNC02LjI2OCAxNC0xNCAxNHoiIGZpbGw9IiNmZmYiIGZpbGwtb3BhY2l0eT0iLjA1Ii8+PC9nPjwvc3ZnPg==')] opacity-30"></div>
        <div class="relative flex items-center justify-between p-4">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-amber-500 backdrop-blur-sm rounded-xl flex items-center justify-center shadow-lg">
              <span class="material-symbols-outlined text-white text-xl">auto_awesome</span>
            </div>
            <div>
              <h3 class="text-black font-bold text-base">{{ t('app.ruleRecommendations') }}</h3>
              <p class="text-black/70 text-xs">{{ t('app.aiPoweredAutomationSuggestions') }}</p>
            </div>
          </div>
          <button 
            type="button"
            @click="closeRecommendationPanel"
            data-testid="close-rule-recommendations"
            :aria-label="t('app.close')"
            :title="t('app.close')"
            class="w-8 h-8 flex items-center justify-center rounded-lg text-black/70 hover:text-black hover:bg-black/10 transition-all"
          >
            <span class="material-symbols-outlined" aria-hidden="true">close</span>
          </button>
        </div>
      </div>

      <!-- Recommendation Content -->
      <div class="p-3 space-y-3 bg-gradient-to-b from-white to-amber-50/30 max-h-[500px] overflow-y-auto">
        <div class="grid grid-cols-[1fr_88px] gap-2 rounded-lg border border-amber-100 bg-white p-2">
          <label class="text-xs font-medium text-slate-600">
            {{ t('app.category') }}
            <select
              v-model="ruleRecommendationFilters.category"
              :disabled="isRecommendingRules"
              class="mt-1 w-full rounded-md border border-slate-200 bg-white px-2 py-1.5 text-xs text-slate-700 focus:outline-none focus:ring-2 focus:ring-amber-200 disabled:bg-slate-100"
            >
              <option
                v-for="option in ruleRecommendationCategories"
                :key="option.value"
                :value="option.value"
              >
                {{ t(option.labelKey) }}
              </option>
            </select>
          </label>
          <label class="text-xs font-medium text-slate-600">
            {{ t('app.count') }}
            <input
              v-model.number="ruleRecommendationFilters.maxRecommendations"
              :disabled="isRecommendingRules"
              type="number"
              min="1"
              max="10"
              class="mt-1 w-full rounded-md border border-slate-200 bg-white px-2 py-1.5 text-xs text-slate-700 focus:outline-none focus:ring-2 focus:ring-amber-200 disabled:bg-slate-100"
            />
          </label>
        </div>

        <label class="block rounded-lg border border-amber-100 bg-white p-2 text-xs font-medium text-slate-600">
          {{ t('app.recommendationScenario') }}
          <textarea
            v-model.trim="ruleRecommendationFilters.userRequirement"
            :disabled="isRecommendingRules"
            rows="3"
            :maxlength="AI_RECOMMENDATION_REQUIREMENT_MAX_LENGTH"
            :placeholder="t('app.recommendationScenarioPlaceholder')"
            class="mt-1 w-full resize-none rounded-md border border-slate-200 bg-white px-2 py-1.5 text-xs leading-relaxed text-slate-700 focus:outline-none focus:ring-2 focus:ring-amber-200 disabled:bg-slate-100"
          ></textarea>
          <span class="mt-1 block text-[10px] font-normal leading-snug text-slate-400">
            {{ t('app.recommendationBasisHint') }}
          </span>
        </label>

        <button
          type="button"
          data-testid="generate-rule-recommendations"
          @click="fetchRuleRecommendations"
          :disabled="isRecommendationRunningForAnother('rule')"
          :class="[
            'flex w-full items-center justify-center gap-2 rounded-lg px-3 py-2.5 text-sm font-bold text-white shadow-sm transition-all active:scale-[0.98] disabled:cursor-not-allowed disabled:opacity-60',
            isRecommendingRules ? 'bg-red-500 hover:bg-red-600' : 'bg-amber-500 hover:bg-amber-600'
          ]"
        >
          <span class="material-symbols-outlined text-base">
            {{ isRecommendingRules ? 'stop' : 'auto_awesome' }}
          </span>
          {{ isRecommendingRules ? t('app.stopRuleRecommendations') : t('app.generateRecommendations') }}
        </button>

        <RecommendationProgressStatus
          v-if="isRecommendingRules"
          kind="rule"
          :elapsed-seconds="recommendationProgressElapsed"
          :stage="recommendationProgressStage"
          :template-count="deviceTemplates.length"
          :device-count="nodes.length"
          :rule-count="rules.length"
          :spec-count="specifications.length"
        />

        <div
          v-if="ruleRecommendationMessage && !isRecommendingRules"
          class="rounded-lg border border-amber-100 bg-amber-50 px-3 py-2 text-xs font-medium text-amber-700"
        >
          {{ ruleRecommendationMessage }}
        </div>
        <div
          v-if="ruleRecommendationMessage && !isRecommendingRules"
          data-testid="rule-candidate-accounting"
          class="rounded-lg border border-slate-200 bg-white px-3 py-2 text-xs leading-relaxed text-slate-600"
        >
          {{ t('app.recommendationCandidateSummary', {
            raw: ruleRecommendationRawCandidateCount,
            inspected: ruleRecommendationInspectedCount,
            kept: ruleRecommendations.length,
            filtered: ruleRecommendationFilteredCount,
            truncated: ruleRecommendationTruncatedCount
          }) }}
        </div>
        <div
          v-if="ruleRecommendationFilteredCount > 0 && !isRecommendingRules"
          class="rounded-lg border border-slate-200 bg-slate-50 px-3 py-2 text-xs font-medium text-slate-600"
        >
          <p>{{ t('app.recommendationFilteredNotice', { count: ruleRecommendationFilteredCount }) }}</p>
          <ul
            v-if="ruleRecommendationFilteredItems.length"
            class="mt-1 max-h-32 list-disc space-y-0.5 overflow-y-auto pl-4 pr-1 font-normal leading-relaxed"
          >
            <li
              v-for="(item, index) in ruleRecommendationFilteredItems"
              :key="`${item.type || 'item'}-${item.index || index}-${item.reasonCode || item.reason}`"
            >
              {{ formatRecommendationFilteredItem(item) }}
            </li>
          </ul>
          <p v-else class="mt-1 font-normal text-slate-500">
            {{ t('app.recommendationFilteredNoDetails') }}
          </p>
        </div>
        <div
          v-if="ruleRecommendationAdjustedItems.length > 0 && !isRecommendingRules"
          data-testid="rule-adjusted-items"
          class="rounded-lg border border-amber-200 bg-amber-50 px-3 py-2 text-xs font-medium text-amber-800"
        >
          <p>{{ t('app.recommendationAdjustedNotice', { count: ruleRecommendationAdjustedItems.length }) }}</p>
          <ul class="mt-1 max-h-36 list-disc space-y-0.5 overflow-y-auto pl-4 pr-1 font-normal leading-relaxed">
            <li
              v-for="(item, index) in ruleRecommendationAdjustedItems"
              :key="`${item.type || 'item'}-${item.index || index}-${item.reasonCode || item.reason}`"
            >
              {{ formatRecommendationAdjustmentItem(item) }}
            </li>
          </ul>
        </div>

        <!-- Loading State -->
        <div v-if="isRecommendingRules" class="flex flex-col items-center justify-center py-10">
          <div class="relative">
            <span class="material-symbols-outlined text-amber-500 text-5xl animate-spin">sync</span>
            <div class="absolute inset-0 bg-amber-400 rounded-full animate-ping opacity-20"></div>
          </div>
          <p class="text-slate-600 text-sm mt-4 font-medium">{{ t('app.analyzingDevices') }}</p>
          <p class="text-slate-400 text-xs mt-1">{{ t('app.generatingAutomationRules') }}</p>
        </div>

        <!-- Setup State -->
        <div v-else-if="!ruleRecommendationRequested" class="flex flex-col items-center justify-center py-10">
          <div class="w-16 h-16 bg-amber-50 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-amber-400 text-3xl">tune</span>
          </div>
          <p class="text-slate-600 text-sm font-medium mt-2">{{ t('app.configureRecommendationParameters') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.clickGenerateRecommendations') }}</p>
        </div>

        <!-- Empty State -->
        <div v-else-if="ruleRecommendations.length === 0" class="flex flex-col items-center justify-center py-10">
          <div class="w-16 h-16 bg-slate-100 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-slate-300 text-3xl">psychology</span>
          </div>
          <p class="text-slate-600 text-sm font-medium mt-2">{{ t('app.noRecommendationsAvailable') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.recommendationEmptyGuidance') }}</p>
        </div>

        <!-- Recommendations List -->
        <div v-else class="space-y-3">
          <!-- Header with count -->
          <div class="flex items-center justify-between px-1">
            <span class="text-xs font-medium text-slate-500">{{ t('app.recommendationsFound', { count: ruleRecommendations.length }) }}</span>
            <button 
              @click="fetchRuleRecommendations"
              class="text-xs text-amber-600 hover:text-amber-700 font-medium flex items-center gap-1"
            >
              <span class="material-symbols-outlined text-sm">refresh</span>
              {{ t('app.regenerateRecommendations') }}
            </button>
          </div>

          <div 
            v-for="(rec, index) in ruleRecommendations" 
            :key="index"
            class="bg-white rounded-xl border border-slate-200 shadow-sm hover:shadow-md transition-all overflow-hidden group"
          >
            <!-- Card Header -->
            <div class="p-3 pb-2">
              <div class="flex items-start justify-between gap-2">
                <div class="flex min-w-0 items-center gap-2">
                  <!-- Rule Icon -->
                  <div class="w-10 h-10 shrink-0 bg-amber-100 rounded-lg flex items-center justify-center">
                    <span class="material-symbols-outlined text-amber-600">smart_toy</span>
                  </div>
                  <div class="min-w-0">
                    <h4 class="text-sm font-bold text-slate-800 break-words">{{ rec.name }}</h4>
                  </div>
                </div>
              </div>
            </div>

            <!-- Reason -->
            <div class="px-3 pb-2">
              <p class="text-xs text-slate-600 break-words">
                {{ rec.category ? t('app.categoryWithValue', { value: rec.category }) : t('app.aiGeneratedAutomationRule') }}
              </p>
            </div>

            <!-- Details -->
            <div class="px-3 pb-2">
              <details class="text-xs">
                <summary class="flex cursor-pointer items-center gap-1 font-medium text-amber-600 hover:text-amber-700">
                  <span class="material-symbols-outlined text-sm">info</span>
                  {{ t('app.viewDetails') }}
                </summary>
                <div class="mt-2 space-y-2 rounded-lg bg-slate-50 p-2 text-slate-700">
                  <div v-if="rec.conditions && rec.conditions.length">
                    <div class="mb-1 font-semibold text-amber-700">{{ t('app.trigger') }}:</div>
                    <ul class="space-y-1">
                      <li v-for="(cond, condIndex) in rec.conditions" :key="condIndex" class="text-xs">
                        <span class="font-mono rounded bg-white px-1 py-0.5">
                          {{ formatRecommendedRuleConditionDevice(cond) }}.{{ cond.attribute }}
                        </span>
                        <template v-if="isValueBasedRuleRecommendationCondition(cond.targetType)">
                          <span class="mx-1">{{ cond.relation }}</span>
                          <span class="font-mono rounded bg-white px-1 py-0.5">{{ cond.value }}</span>
                        </template>
                        <span v-else class="ml-1 text-slate-500">{{ t('app.apiSignalFires') }}</span>
                      </li>
                    </ul>
                  </div>
                  <div v-if="rec.command">
                    <div class="mb-1 font-semibold text-amber-700">{{ t('app.action') }}:</div>
                    <div class="text-xs">
                      <span class="font-mono rounded bg-white px-1 py-0.5">
                        {{ formatRecommendedRuleCommandDevice(rec.command) }}.{{ rec.command.action }}
                      </span>
                      <span v-if="rec.command.contentDevice && rec.command.content" class="ml-2 text-slate-500">
                        ({{ t('app.copyFrom') }} {{ formatRecommendedRuleContentDevice(rec.command) }}<template v-if="rec.command.content">.{{ rec.command.content }}<template v-if="rec.command.contentPrivacy"> ({{ t(`app.${rec.command.contentPrivacy}`) }})</template></template>)
                      </span>
                    </div>
                  </div>
                </div>
              </details>
            </div>

            <!-- Action Button -->
            <div class="px-3 pb-3">
              <button 
                @click="applyRecommendation(rec, index)"
                :disabled="appliedRuleRecommendations.has(index) || applyingRuleRecommendations.has(index)"
                :aria-busy="applyingRuleRecommendations.has(index)"
                :class="[
                  'w-full py-2 px-4 text-white text-sm font-medium rounded-lg transition-colors flex items-center justify-center gap-2',
                  appliedRuleRecommendations.has(index)
                    ? 'bg-green-500 cursor-default'
                    : applyingRuleRecommendations.has(index)
                      ? 'bg-slate-400 cursor-wait'
                      : 'bg-amber-500 hover:bg-amber-600'
                ]"
              >
                <span
                  class="material-symbols-outlined text-sm"
                  :class="{ 'animate-spin': applyingRuleRecommendations.has(index) }"
                >
                  {{ appliedRuleRecommendations.has(index) ? 'check' : applyingRuleRecommendations.has(index) ? 'progress_activity' : 'add' }}
                </span>
                {{ appliedRuleRecommendations.has(index)
                  ? t('app.addedToBoard')
                  : applyingRuleRecommendations.has(index)
                    ? t('app.applyingRecommendation')
                    : t('app.applyThisRule') }}
              </button>
            </div>
          </div>
        </div>
      </div>
    </div>

    <!-- Device Recommendation Panel -->
    <div 
      v-if="showDeviceRecommendationPanel"
      data-testid="device-recommendation-panel"
      class="board-floating-panel board-recommendation-panel board-surface-panel fixed top-20 z-30 w-96 max-w-[calc(100vw-2rem)] rounded-2xl shadow-2xl border overflow-hidden"
    >
      <!-- Recommendation Header with gradient -->
      <div class="relative overflow-hidden">
        <div class="absolute inset-0 bg-gradient-to-br from-purple-500 to-violet-600"></div>
        <div class="absolute inset-0 bg-[url('data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iNjAiIGhlaWdodD0iNjAiIHZpZXdCb3g9IjAgMCA2MCA2MCIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj48ZyBmaWxsPSJub25lIiBmaWxsLXJ1bGU9ImV2ZW5vZGQiPjxwYXRoIGQ9Ik0zNiAxOGMtOS45NDEgMC0xOCA4LjA1OS0xOCAxOHM4LjA1OSAxOCAxOCAxOCAxOC04LjA1OSAxOC0xOC04LjA1OS0xOC0xOC0xOHptMCAzMmMtNy43MzIgMC0xNC02LjI2OC0xNC0xNHM2LjI2OC0xNCAxNC0xNCAxNCA2LjI2OCAxNCAxNC02LjI2OCAxNC0xNCAxNHoiIGZpbGw9IiNmZmYiIGZpbGwtb3BhY2l0eT0iLjA1Ii8+PC9nPjwvc3ZnPg==')] opacity-30"></div>
        <div class="relative flex items-center justify-between p-4">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-purple-500 backdrop-blur-sm rounded-xl flex items-center justify-center shadow-lg">
              <span class="material-symbols-outlined text-white text-xl">devices</span>
            </div>
            <div>
              <h3 class="text-black font-bold text-base">{{ t('app.deviceRecommendations') }}</h3>
              <p class="text-black/70 text-xs">{{ t('app.aiPoweredDeviceSuggestions') }}</p>
            </div>
          </div>
          <button 
            type="button"
            @click="closeDeviceRecommendationPanel"
            data-testid="close-device-recommendations"
            :aria-label="t('app.close')"
            :title="t('app.close')"
            class="w-8 h-8 flex items-center justify-center rounded-lg text-black/70 hover:text-black hover:bg-black/10 transition-all"
          >
            <span class="material-symbols-outlined" aria-hidden="true">close</span>
          </button>
        </div>
      </div>

      <!-- Recommendation Content -->
      <div class="p-3 space-y-3 bg-gradient-to-b from-white to-purple-50/30 max-h-[500px] overflow-y-auto">
        <div class="rounded-lg border border-purple-100 bg-white p-2">
          <label class="text-xs font-medium text-slate-600">
            {{ t('app.count') }}
            <input
              v-model.number="deviceRecommendationFilters.maxRecommendations"
              :disabled="isRecommendingDevices"
              type="number"
              min="1"
              max="10"
              class="mt-1 w-full rounded-md border border-slate-200 bg-white px-2 py-1.5 text-xs text-slate-700 focus:outline-none focus:ring-2 focus:ring-purple-200 disabled:bg-slate-100"
            />
          </label>
        </div>

        <label class="block rounded-lg border border-purple-100 bg-white p-2 text-xs font-medium text-slate-600">
          {{ t('app.recommendationScenario') }}
          <textarea
            v-model.trim="deviceRecommendationFilters.userRequirement"
            :disabled="isRecommendingDevices"
            rows="3"
            :maxlength="AI_RECOMMENDATION_REQUIREMENT_MAX_LENGTH"
            :placeholder="t('app.recommendationScenarioPlaceholder')"
            class="mt-1 w-full resize-none rounded-md border border-slate-200 bg-white px-2 py-1.5 text-xs leading-relaxed text-slate-700 focus:outline-none focus:ring-2 focus:ring-purple-200 disabled:bg-slate-100"
          ></textarea>
          <span class="mt-1 block text-[10px] font-normal leading-snug text-slate-400">
            {{ t('app.recommendationBasisHint') }}
          </span>
        </label>

        <button
          type="button"
          data-testid="generate-device-recommendations"
          @click="fetchDeviceRecommendations"
          :disabled="isRecommendationRunningForAnother('device')"
          :class="[
            'flex w-full items-center justify-center gap-2 rounded-lg px-3 py-2.5 text-sm font-bold text-white shadow-sm transition-all active:scale-[0.98] disabled:cursor-not-allowed disabled:opacity-60',
            isRecommendingDevices ? 'bg-red-500 hover:bg-red-600' : 'bg-purple-500 hover:bg-purple-600'
          ]"
        >
          <span class="material-symbols-outlined text-base">
            {{ isRecommendingDevices ? 'stop' : 'auto_awesome' }}
          </span>
          {{ isRecommendingDevices ? t('app.stopDeviceRecommendations') : t('app.generateRecommendations') }}
        </button>

        <RecommendationProgressStatus
          v-if="isRecommendingDevices"
          kind="device"
          :elapsed-seconds="recommendationProgressElapsed"
          :stage="recommendationProgressStage"
          :template-count="deviceTemplates.length"
          :device-count="nodes.length"
          :rule-count="rules.length"
          :spec-count="specifications.length"
        />

        <div
          v-if="deviceRecommendationMessage && !isRecommendingDevices"
          class="rounded-lg border border-purple-100 bg-purple-50 px-3 py-2 text-xs font-medium text-purple-700"
        >
          {{ deviceRecommendationMessage }}
        </div>
        <div
          v-if="deviceRecommendationMessage && !isRecommendingDevices"
          data-testid="device-candidate-accounting"
          class="rounded-lg border border-slate-200 bg-white px-3 py-2 text-xs leading-relaxed text-slate-600"
        >
          {{ t('app.recommendationCandidateSummary', {
            raw: deviceRecommendationRawCandidateCount,
            inspected: deviceRecommendationInspectedCount,
            kept: deviceRecommendations.length,
            filtered: deviceRecommendationFilteredCount,
            truncated: deviceRecommendationTruncatedCount
          }) }}
        </div>
        <div
          v-if="deviceRecommendationFilteredCount > 0 && !isRecommendingDevices"
          class="rounded-lg border border-slate-200 bg-slate-50 px-3 py-2 text-xs font-medium text-slate-600"
        >
          <p>{{ t('app.recommendationFilteredNotice', { count: deviceRecommendationFilteredCount }) }}</p>
          <ul
            v-if="deviceRecommendationFilteredItems.length"
            class="mt-1 max-h-32 list-disc space-y-0.5 overflow-y-auto pl-4 pr-1 font-normal leading-relaxed"
          >
            <li
              v-for="(item, index) in deviceRecommendationFilteredItems"
              :key="`${item.type || 'item'}-${item.index || index}-${item.reasonCode || item.reason}`"
            >
              {{ formatRecommendationFilteredItem(item) }}
            </li>
          </ul>
          <p v-else class="mt-1 font-normal text-slate-500">
            {{ t('app.recommendationFilteredNoDetails') }}
          </p>
        </div>
        <div
          v-if="deviceRecommendationAdjustedItems.length > 0 && !isRecommendingDevices"
          class="rounded-lg border border-amber-200 bg-amber-50 px-3 py-2 text-xs font-medium text-amber-800"
        >
          <p>{{ t('app.deviceRecommendationAdjustedNotice', { count: deviceRecommendationAdjustedItems.length }) }}</p>
          <ul class="mt-1 max-h-36 list-disc space-y-0.5 overflow-y-auto pl-4 pr-1 font-normal leading-relaxed">
            <li
              v-for="(item, index) in deviceRecommendationAdjustedItems"
              :key="`${item.type || 'device'}-${item.index || index}-${item.reasonCode || item.reason}`"
            >
              {{ formatRecommendationAdjustmentItem(item) }}
            </li>
          </ul>
        </div>

        <!-- Loading State -->
        <div v-if="isRecommendingDevices" class="flex flex-col items-center justify-center py-10">
          <div class="relative">
            <span class="material-symbols-outlined text-purple-500 text-5xl animate-spin">sync</span>
            <div class="absolute inset-0 bg-purple-400 rounded-full animate-ping opacity-20"></div>
          </div>
          <p class="text-slate-600 text-sm mt-4 font-medium">{{ t('app.analyzingBoard') }}</p>
          <p class="text-slate-400 text-xs mt-1">{{ t('app.findingCompatibleDevices') }}</p>
        </div>

        <!-- Setup State -->
        <div v-else-if="!deviceRecommendationRequested" class="flex flex-col items-center justify-center py-10">
          <div class="w-16 h-16 bg-purple-50 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-purple-400 text-3xl">tune</span>
          </div>
          <p class="text-slate-600 text-sm font-medium mt-2">{{ t('app.configureRecommendationParameters') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.clickGenerateRecommendations') }}</p>
        </div>

        <!-- Empty State -->
        <div v-else-if="deviceRecommendations.length === 0" class="flex flex-col items-center justify-center py-10">
          <div class="w-16 h-16 bg-slate-100 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-slate-300 text-3xl">devices</span>
          </div>
          <p class="text-slate-600 text-sm font-medium mt-2">{{ t('app.noRecommendationsAvailable') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.recommendationEmptyGuidance') }}</p>
        </div>

        <!-- Recommendations List -->
        <div v-else class="space-y-3">
          <!-- Header with count -->
          <div class="flex items-center justify-between px-1">
            <span class="text-xs font-medium text-slate-500">{{ t('app.devicesRecommended', { count: deviceRecommendations.length }) }}</span>
            <button 
              @click="fetchDeviceRecommendations"
              class="text-xs text-purple-600 hover:text-purple-700 font-medium flex items-center gap-1"
            >
              <span class="material-symbols-outlined text-sm">refresh</span>
              {{ t('app.regenerateRecommendations') }}
            </button>
          </div>

          <div
            v-for="(rec, index) in deviceRecommendations"
            :key="index"
            class="bg-white rounded-xl border border-slate-200 shadow-sm hover:shadow-md transition-all overflow-hidden group"
          >
            <!-- Card Header -->
            <div class="p-3 pb-2">
              <div class="flex items-start justify-between gap-2">
                <div class="flex min-w-0 items-center gap-2">
                  <!-- Device Icon -->
                  <div class="w-10 h-10 shrink-0 bg-purple-100 rounded-lg flex items-center justify-center">
                    <span class="material-symbols-outlined text-purple-600">device_hub</span>
                  </div>
                  <div class="min-w-0">
                    <h4 class="text-sm font-bold text-slate-800 truncate" :title="rec.suggestedLabel || rec.templateName">
                      {{ rec.suggestedLabel || rec.templateName }}
                    </h4>
                    <p class="text-[11px] font-medium text-purple-600 truncate" :title="rec.templateName">{{ rec.templateName }}</p>
                    <p class="text-xs text-slate-500 break-words">{{ rec.description || t('app.noDescription') }}</p>
                  </div>
                </div>
              </div>
            </div>

            <!-- Reason -->
            <div class="px-3 pb-2">
              <div v-if="rec.intendedUse || rec.suggestedPlacement || rec.initialState || rec.currentStateTrust || rec.currentStatePrivacy" class="mb-2 flex flex-wrap gap-1">
                <span v-if="rec.intendedUse" class="rounded-full bg-purple-50 px-2 py-1 text-[11px] font-medium text-purple-700">
                  {{ t('app.deviceRecommendationIntendedUse', { value: localizedRecommendationText(rec.intendedUse, t('app.recommendedBasedOnCurrentDevices')) }) }}
                </span>
                <span v-if="rec.suggestedPlacement" class="rounded-full bg-slate-50 px-2 py-1 text-[11px] font-medium text-slate-600">
                  {{ t('app.deviceRecommendationSuggestedPlacement', { value: localizedRecommendationText(rec.suggestedPlacement, t('app.recommendedBasedOnCurrentDevices')) }) }}
                </span>
                <span v-if="rec.initialState" class="rounded-full bg-slate-50 px-2 py-1 text-[11px] font-medium text-slate-600">
                  {{ t('app.deviceRecommendationInitialState', { value: rec.initialState }) }}
                </span>
                <span v-if="rec.currentStateTrust" class="rounded-full bg-emerald-50 px-2 py-1 text-[11px] font-medium text-emerald-700">
                  {{ t('app.deviceRecommendationStateTrust', { value: t(`app.${rec.currentStateTrust}`) }) }}
                </span>
                <span v-if="rec.currentStatePrivacy" class="rounded-full bg-fuchsia-50 px-2 py-1 text-[11px] font-medium text-fuchsia-700">
                  {{ t('app.deviceRecommendationStatePrivacy', { value: t(`app.${rec.currentStatePrivacy}`) }) }}
                </span>
              </div>
              <p v-if="rec.intendedUse || rec.suggestedPlacement" class="mb-2 text-[11px] leading-relaxed text-slate-500">
                {{ t('app.deviceRecommendationContextAdvisory') }}
              </p>
              <p
                v-if="recommendedDeviceEnvironmentAdditions(rec).length > 0"
                class="mb-2 rounded-lg border border-sky-100 bg-sky-50 px-2 py-1.5 text-[11px] leading-relaxed text-sky-800"
              >
                {{ t('app.deviceCreationEnvironmentAdditionsPreview', { names: recommendedDeviceEnvironmentAdditions(rec).join(', ') }) }}
              </p>
              <div v-if="rec.initialVariables?.length || rec.initialPrivacies?.length" class="mb-2 space-y-1 text-[11px] text-slate-600">
                <div v-for="variable in rec.initialVariables || []" :key="`value-${variable.name}`" class="break-words">
                  {{ t('app.deviceRecommendationInitialVariable', {
                    name: variable.name,
                    value: variable.value,
                    trust: variable.trust ? t(`app.${variable.trust}`) : t('app.useTemplateDefault')
                  }) }}
                </div>
                <div v-for="privacy in rec.initialPrivacies || []" :key="`privacy-${privacy.name}`" class="break-words">
                  {{ t('app.deviceRecommendationInitialPrivacy', {
                    name: privacy.name,
                    privacy: t(`app.${privacy.privacy}`)
                  }) }}
                </div>
              </div>
              <p class="text-xs text-slate-600 break-words">{{ localizedRecommendationText(rec.reason, t('app.recommendedBasedOnCurrentDevices')) }}</p>
            </div>

            <!-- Action Button -->
            <div class="px-3 pb-3">
              <button 
                @click="applyDeviceRecommendation(rec, index)"
                :disabled="appliedDeviceRecommendations.has(index) || applyingDeviceRecommendations.has(index)"
                :aria-busy="applyingDeviceRecommendations.has(index)"
                :class="[
                  'w-full py-2 px-4 text-white text-sm font-medium rounded-lg transition-colors flex items-center justify-center gap-2',
                  appliedDeviceRecommendations.has(index)
                    ? 'bg-green-500 cursor-default'
                    : applyingDeviceRecommendations.has(index)
                      ? 'bg-slate-400 cursor-wait'
                      : 'bg-purple-500 hover:bg-purple-600'
                ]"
              >
                <span
                  class="material-symbols-outlined text-sm"
                  :class="{ 'animate-spin': applyingDeviceRecommendations.has(index) }"
                >
                  {{ appliedDeviceRecommendations.has(index) ? 'check' : applyingDeviceRecommendations.has(index) ? 'progress_activity' : 'add' }}
                </span>
                {{ appliedDeviceRecommendations.has(index)
                  ? t('app.addedToBoard')
                  : applyingDeviceRecommendations.has(index)
                    ? t('app.applyingRecommendation')
                    : t('app.addThisDevice') }}
              </button>
            </div>
          </div>
        </div>
      </div>
    </div>

    <!-- Specification Recommendation Panel -->
    <div 
      v-if="showSpecRecommendationPanel"
      data-testid="spec-recommendation-panel"
      class="board-floating-panel board-recommendation-panel board-surface-panel fixed top-20 z-30 w-96 max-w-[calc(100vw-2rem)] rounded-2xl shadow-2xl border overflow-hidden"
    >
      <!-- Recommendation Header with gradient -->
      <div class="relative overflow-hidden">
        <div class="absolute inset-0 bg-gradient-to-br from-red-500 to-rose-600"></div>
        <div class="absolute inset-0 bg-[url('data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iNjAiIGhlaWdodD0iNjAiIHZpZXdCb3g9IjAgMCA2MCA2MCIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj48ZyBmaWxsPSJub25lIiBmaWxsLXJ1bGU9ImV2ZW5vZGQiPjxwYXRoIGQ9Ik0zNiAxOGMtOS45NDEgMC0xOCA4LjA1OS0xOCAxOHM4LjA1OSAxOCAxOCAxOCAxOC04LjA1OSAxOC0xOC04LjA1OS0xOC0xOC0xOHptMCAzMmMtNy43MzIgMC0xNC02LjI2OC0xNC0xNHM2LjI2OC0xNCAxNC0xNCAxNCA2LjI2OCAxNCAxNC02LjI2OCAxNC0xNCAxNHoiIGZpbGw9IiNmZmYiIGZpbGwtb3BhY2l0eT0iLjA1Ii8+PC9nPjwvc3ZnPg==')] opacity-30"></div>
        <div class="relative flex items-center justify-between p-4">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-red-500 backdrop-blur-sm rounded-xl flex items-center justify-center shadow-lg">
              <span class="material-symbols-outlined text-white text-xl">policy</span>
            </div>
            <div>
              <h3 class="text-black font-bold text-base">{{ t('app.specificationRecommendations') }}</h3>
              <p class="text-black/70 text-xs">{{ t('app.aiPoweredSpecificationSuggestions') }}</p>
            </div>
          </div>
          <button 
            type="button"
            @click="closeSpecRecommendationPanel"
            data-testid="close-spec-recommendations"
            :aria-label="t('app.close')"
            :title="t('app.close')"
            class="w-8 h-8 flex items-center justify-center rounded-lg text-black/70 hover:text-black hover:bg-black/10 transition-all"
          >
            <span class="material-symbols-outlined" aria-hidden="true">close</span>
          </button>
        </div>
      </div>

      <!-- Recommendation Content -->
      <div class="p-3 space-y-3 bg-gradient-to-b from-white to-red-50/30 max-h-[500px] overflow-y-auto">
        <div class="grid grid-cols-[1fr_88px] gap-2 rounded-lg border border-red-100 bg-white p-2">
          <label class="text-xs font-medium text-slate-600">
            {{ t('app.category') }}
            <select
              v-model="specRecommendationFilters.category"
              :disabled="isRecommendingSpecs"
              class="mt-1 w-full rounded-md border border-slate-200 bg-white px-2 py-1.5 text-xs text-slate-700 focus:outline-none focus:ring-2 focus:ring-red-200 disabled:bg-slate-100"
            >
              <option
                v-for="option in specRecommendationCategories"
                :key="option.value"
                :value="option.value"
              >
                {{ t(option.labelKey) }}
              </option>
            </select>
          </label>
          <label class="text-xs font-medium text-slate-600">
            {{ t('app.count') }}
            <input
              v-model.number="specRecommendationFilters.maxRecommendations"
              :disabled="isRecommendingSpecs"
              type="number"
              min="1"
              max="10"
              class="mt-1 w-full rounded-md border border-slate-200 bg-white px-2 py-1.5 text-xs text-slate-700 focus:outline-none focus:ring-2 focus:ring-red-200 disabled:bg-slate-100"
            />
          </label>
        </div>

        <label class="block rounded-lg border border-red-100 bg-white p-2 text-xs font-medium text-slate-600">
          {{ t('app.recommendationScenario') }}
          <textarea
            v-model.trim="specRecommendationFilters.userRequirement"
            :disabled="isRecommendingSpecs"
            rows="3"
            :maxlength="AI_RECOMMENDATION_REQUIREMENT_MAX_LENGTH"
            :placeholder="t('app.recommendationScenarioPlaceholder')"
            class="mt-1 w-full resize-none rounded-md border border-slate-200 bg-white px-2 py-1.5 text-xs leading-relaxed text-slate-700 focus:outline-none focus:ring-2 focus:ring-red-200 disabled:bg-slate-100"
          ></textarea>
          <span class="mt-1 block text-[10px] font-normal leading-snug text-slate-400">
            {{ t('app.recommendationBasisHint') }}
          </span>
        </label>

        <button
          type="button"
          data-testid="generate-spec-recommendations"
          @click="fetchSpecRecommendations"
          :disabled="isRecommendationRunningForAnother('spec')"
          :class="[
            'flex w-full items-center justify-center gap-2 rounded-lg px-3 py-2.5 text-sm font-bold text-white shadow-sm transition-all active:scale-[0.98] disabled:cursor-not-allowed disabled:opacity-60',
            isRecommendingSpecs ? 'bg-red-600 hover:bg-red-700' : 'bg-red-500 hover:bg-red-600'
          ]"
        >
          <span class="material-symbols-outlined text-base">
            {{ isRecommendingSpecs ? 'stop' : 'auto_awesome' }}
          </span>
          {{ isRecommendingSpecs ? t('app.stopSpecificationRecommendations') : t('app.generateRecommendations') }}
        </button>

        <RecommendationProgressStatus
          v-if="isRecommendingSpecs"
          kind="spec"
          :elapsed-seconds="recommendationProgressElapsed"
          :stage="recommendationProgressStage"
          :template-count="deviceTemplates.length"
          :device-count="nodes.length"
          :rule-count="rules.length"
          :spec-count="specifications.length"
        />

        <div
          v-if="specRecommendationMessage && !isRecommendingSpecs"
          class="rounded-lg border border-red-100 bg-red-50 px-3 py-2 text-xs font-medium text-red-700"
        >
          {{ specRecommendationMessage }}
        </div>
        <div
          v-if="specRecommendationMessage && !isRecommendingSpecs"
          data-testid="spec-candidate-accounting"
          class="rounded-lg border border-slate-200 bg-white px-3 py-2 text-xs leading-relaxed text-slate-600"
        >
          {{ t('app.recommendationCandidateSummary', {
            raw: specRecommendationRawCandidateCount,
            inspected: specRecommendationInspectedCount,
            kept: specRecommendations.length,
            filtered: specRecommendationFilteredCount,
            truncated: specRecommendationTruncatedCount
          }) }}
        </div>
        <div
          v-if="specRecommendationFilteredCount > 0 && !isRecommendingSpecs"
          class="rounded-lg border border-slate-200 bg-slate-50 px-3 py-2 text-xs font-medium text-slate-600"
        >
          <p>{{ t('app.recommendationFilteredNotice', { count: specRecommendationFilteredCount }) }}</p>
          <ul
            v-if="specRecommendationFilteredItems.length"
            class="mt-1 max-h-32 list-disc space-y-0.5 overflow-y-auto pl-4 pr-1 font-normal leading-relaxed"
          >
            <li
              v-for="(item, index) in specRecommendationFilteredItems"
              :key="`${item.type || 'item'}-${item.index || index}-${item.reasonCode || item.reason}`"
            >
              {{ formatRecommendationFilteredItem(item) }}
            </li>
          </ul>
          <p v-else class="mt-1 font-normal text-slate-500">
            {{ t('app.recommendationFilteredNoDetails') }}
          </p>
        </div>

        <!-- Loading State -->
        <div v-if="isRecommendingSpecs" class="flex flex-col items-center justify-center py-10">
          <div class="relative">
            <span class="material-symbols-outlined text-red-500 text-5xl animate-spin">sync</span>
            <div class="absolute inset-0 bg-red-400 rounded-full animate-ping opacity-20"></div>
          </div>
          <p class="text-slate-600 text-sm mt-4 font-medium">{{ t('app.analyzingSystem') }}</p>
          <p class="text-slate-400 text-xs mt-1">{{ t('app.generatingFormalSpecifications') }}</p>
        </div>

        <!-- Setup State -->
        <div v-else-if="!specRecommendationRequested" class="flex flex-col items-center justify-center py-10">
          <div class="w-16 h-16 bg-red-50 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-red-400 text-3xl">tune</span>
          </div>
          <p class="text-slate-600 text-sm font-medium mt-2">{{ t('app.configureRecommendationParameters') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.clickGenerateRecommendations') }}</p>
        </div>

        <!-- Empty State -->
        <div v-else-if="specRecommendations.length === 0" class="flex flex-col items-center justify-center py-10">
          <div class="w-16 h-16 bg-slate-100 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-slate-300 text-3xl">policy</span>
          </div>
          <p class="text-slate-600 text-sm font-medium mt-2">{{ t('app.noRecommendationsAvailable') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.recommendationEmptyGuidance') }}</p>
        </div>

        <!-- Recommendations List -->
        <div v-else class="space-y-3">
          <!-- Header with count -->
          <div class="flex items-center justify-between px-1">
            <span class="text-xs font-medium text-slate-500">{{ t('app.specificationsRecommended', { count: specRecommendations.length }) }}</span>
            <button 
              @click="fetchSpecRecommendations"
              class="text-xs text-red-600 hover:text-red-700 font-medium flex items-center gap-1"
            >
              <span class="material-symbols-outlined text-sm">refresh</span>
              {{ t('app.regenerateRecommendations') }}
            </button>
          </div>

          <div 
            v-for="(rec, index) in specRecommendations" 
            :key="index"
            class="bg-white rounded-xl border border-slate-200 shadow-sm hover:shadow-md transition-all overflow-hidden group"
          >
            <!-- Card Header -->
            <div class="p-3 pb-2">
              <div class="flex items-start justify-between gap-2">
                <div class="flex min-w-0 items-center gap-2">
                  <!-- Specification Icon -->
                  <div class="w-10 h-10 shrink-0 bg-red-100 rounded-lg flex items-center justify-center">
                    <span class="material-symbols-outlined text-red-600">policy</span>
                  </div>
                  <div class="min-w-0">
                    <h4 class="text-sm font-bold text-slate-800 truncate" :title="recommendedSpecTemplateLabel(rec.templateId)">
                      {{ recommendedSpecTemplateLabel(rec.templateId) }}
                    </h4>
                    <p class="text-xs text-slate-500 break-words">
                      <span class="font-semibold">{{ t('app.recommendationRationale') }}:</span>
                      {{ localizedRecommendationText(rec.rationale, t('app.recommendedBasedOnCurrentDevices')) }}
                    </p>
                  </div>
                </div>
              </div>
            </div>

            <div class="px-3 pb-2">
              <p class="text-[11px] leading-4 text-slate-500">
                {{ t('app.specRecommendationRationaleAdvisory') }}
              </p>
            </div>

            <!-- Details -->
            <div class="px-3 pb-2">
              <details class="text-xs">
                <summary class="flex cursor-pointer items-center gap-1 font-medium text-red-600 hover:text-red-700">
                  <span class="material-symbols-outlined text-sm">info</span>
                  {{ t('app.viewDetails') }}
                </summary>
                <div class="mt-2 space-y-2 rounded-lg bg-slate-50 p-2 text-slate-700">
                  <div v-if="rec.aConditions && rec.aConditions.length">
                    <div class="mb-1 font-semibold text-red-700">{{ t('app.alwaysConditions') }}:</div>
                    <ul class="space-y-1">
                      <li v-for="(cond, condIndex) in rec.aConditions" :key="condIndex" class="text-xs">
                        <span class="font-mono rounded bg-white px-1 py-0.5">
                          {{ formatRecommendedSpecConditionTarget(cond) }}
                        </span>
                        <span class="mx-1">{{ cond.relation }}</span>
                        <span class="font-mono rounded bg-white px-1 py-0.5">{{ cond.value }}</span>
                      </li>
                    </ul>
                  </div>
                  <div v-if="rec.ifConditions && rec.ifConditions.length">
                    <div class="mb-1 font-semibold text-red-700">{{ t('app.ifConditions') }}:</div>
                    <ul class="space-y-1">
                      <li v-for="(cond, condIndex) in rec.ifConditions" :key="condIndex" class="text-xs">
                        <span class="font-mono rounded bg-white px-1 py-0.5">
                          {{ formatRecommendedSpecConditionTarget(cond) }}
                        </span>
                        <span class="mx-1">{{ cond.relation }}</span>
                        <span class="font-mono rounded bg-white px-1 py-0.5">{{ cond.value }}</span>
                      </li>
                    </ul>
                  </div>
                  <div v-if="rec.thenConditions && rec.thenConditions.length">
                    <div class="mb-1 font-semibold text-red-700">{{ t('app.thenConditions') }}:</div>
                    <ul class="space-y-1">
                      <li v-for="(cond, condIndex) in rec.thenConditions" :key="condIndex" class="text-xs">
                        <span class="font-mono rounded bg-white px-1 py-0.5">
                          {{ formatRecommendedSpecConditionTarget(cond) }}
                        </span>
                        <span class="mx-1">{{ cond.relation }}</span>
                        <span class="font-mono rounded bg-white px-1 py-0.5">{{ cond.value }}</span>
                      </li>
                    </ul>
                  </div>
                </div>
              </details>
            </div>

            <!-- Action Button -->
            <div class="px-3 pb-3">
              <button 
                @click="applySpecRecommendation(rec, index)"
                :disabled="appliedSpecRecommendations.has(index) || applyingSpecRecommendations.has(index)"
                :aria-busy="applyingSpecRecommendations.has(index)"
                :class="[
                  'w-full py-2 px-4 text-white text-sm font-medium rounded-lg transition-colors flex items-center justify-center gap-2',
                  appliedSpecRecommendations.has(index)
                    ? 'bg-green-500 cursor-default'
                    : applyingSpecRecommendations.has(index)
                      ? 'bg-slate-400 cursor-wait'
                      : 'bg-red-500 hover:bg-red-600'
                ]"
              >
                <span
                  class="material-symbols-outlined text-sm"
                  :class="{ 'animate-spin': applyingSpecRecommendations.has(index) }"
                >
                  {{ appliedSpecRecommendations.has(index) ? 'check' : applyingSpecRecommendations.has(index) ? 'progress_activity' : 'add' }}
                </span>
                {{ appliedSpecRecommendations.has(index)
                  ? t('app.addedToBoard')
                  : applyingSpecRecommendations.has(index)
                    ? t('app.applyingRecommendation')
                    : t('app.addThisSpecification') }}
              </button>
            </div>
          </div>
        </div>
      </div>
    </div>

    <!-- Simulation Panel (Appears when clicking simulation button) -->
    <div 
      v-if="showSimulationPanel"
      data-testid="simulation-panel"
      class="board-floating-panel board-run-panel board-surface-panel fixed top-20 z-30 w-72 max-w-[calc(100vw-2rem)] rounded-2xl shadow-2xl border overflow-hidden"
    >
      <!-- Simulation Header with gradient -->
      <div class="relative overflow-hidden">
        <div class="absolute inset-0 bg-gradient-to-br from-indigo-500 to-violet-600"></div>
        <div class="absolute inset-0 bg-[url('data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iNjAiIGhlaWdodD0iNjAiIHZpZXdCb3g9IjAgMCA2MCA2MCIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj48ZyBmaWxsPSJub25lIiBmaWxsLXJ1bGU9ImV2ZW5vZGQiPjxwYXRoIGQ9Ik0zNiAxOGMtOS45NDEgMC0xOCA4LjA1OS0xOCAxOHM4LjA1OSAxOCAxOCAxOCAxOC04LjA1OSAxOC0xOC04LjA1OS0xOC0xOC0xOHptMCAzMmMtNy43MzIgMC0xNC02LjI2OC0xNC0xNHM2LjI2OC0xNCAxNC0xNCAxNCA2LjI2OCAxNCAxNC02LjI2OCAxNC0xNCAxNHoiIGZpbGw9IiNmZmYiIGZpbGwtb3BhY2l0eT0iLjA1Ii8+PC9nPjwvc3ZnPg==')] opacity-30"></div>
        <div class="relative flex items-center justify-between p-4">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-blue-500 backdrop-blur-sm rounded-xl flex items-center justify-center shadow-lg">
              <span class="material-symbols-outlined text-white text-xl">play_circle</span>
            </div>
            <div>
              <span class="text-sm font-bold text-black">{{ t('app.simulationTitle') }}</span>
              <p class="text-indigo-900/80 text-xs">{{ t('app.configureSimulation') }}</p>
            </div>
          </div>
          <button 
            type="button"
            @click="showSimulationPanel = false"
            data-testid="close-simulation-panel"
            :aria-label="t('app.close')"
            :title="t('app.close')"
            class="w-8 h-8 flex items-center justify-center rounded-lg text-black/70 hover:text-black hover:bg-black/10 transition-all"
          >
            <span class="material-symbols-outlined" aria-hidden="true">close</span>
          </button>
        </div>
      </div>
      <!-- Simulation Content -->
      <div class="p-3 space-y-3 bg-gradient-to-b from-white to-indigo-50/30">
        <!-- Steps -->
        <div class="p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
          <div class="mb-2 flex items-center justify-between gap-3">
            <label for="simulation-steps-input" class="text-[10px] font-bold text-indigo-700 uppercase tracking-wide">
              {{ t('app.simulationSteps') }}
            </label>
            <input
              id="simulation-steps-input"
              v-model.number="simulationForm.steps"
              data-testid="simulation-steps-input"
              :disabled="isSimulating"
              type="number"
              :min="SIMULATION_STEPS_MIN"
              :max="SIMULATION_STEPS_MAX"
              step="1"
              inputmode="numeric"
              class="h-8 w-16 rounded-lg border border-indigo-200 bg-indigo-50 px-2 text-center text-sm font-bold text-indigo-700 outline-none transition focus:border-indigo-500 focus:ring-2 focus:ring-indigo-100 disabled:cursor-not-allowed disabled:opacity-60"
              @change="commitSimulationStepsInput"
              @blur="commitSimulationStepsInput"
              @keydown.enter.prevent="commitSimulationStepsInput"
            />
          </div>
          <div class="flex items-center gap-3">
            <button
              type="button"
              data-testid="simulation-steps-decrease"
              class="inline-flex h-8 w-8 shrink-0 items-center justify-center rounded-lg border border-indigo-200 bg-indigo-50 text-indigo-600 transition hover:bg-indigo-100 disabled:cursor-not-allowed disabled:opacity-40"
              :disabled="isSimulating || normalizeSimulationStepsControlValue(simulationForm.steps) <= SIMULATION_STEPS_MIN"
              :title="t('app.decreaseSimulationSteps')"
              :aria-label="t('app.decreaseSimulationSteps')"
              @click="adjustSimulationSteps(-1)"
            >
              <span class="material-symbols-outlined text-lg" aria-hidden="true">remove</span>
            </button>
            <input
              v-model.number="simulationForm.steps"
              data-testid="simulation-steps-range"
              :disabled="isSimulating"
              type="range"
              :min="SIMULATION_STEPS_MIN"
              :max="SIMULATION_STEPS_MAX"
              step="1"
              class="flex-1 h-2 bg-indigo-200 rounded-lg appearance-none cursor-pointer accent-indigo-600 disabled:cursor-not-allowed disabled:opacity-60"
            />
            <button
              type="button"
              data-testid="simulation-steps-increase"
              class="inline-flex h-8 w-8 shrink-0 items-center justify-center rounded-lg border border-indigo-200 bg-indigo-50 text-indigo-600 transition hover:bg-indigo-100 disabled:cursor-not-allowed disabled:opacity-40"
              :disabled="isSimulating || normalizeSimulationStepsControlValue(simulationForm.steps) >= SIMULATION_STEPS_MAX"
              :title="t('app.increaseSimulationSteps')"
              :aria-label="t('app.increaseSimulationSteps')"
              @click="adjustSimulationSteps(1)"
            >
              <span class="material-symbols-outlined text-lg" aria-hidden="true">add</span>
            </button>
          </div>
        </div>

        <!-- Attack Mode -->
        <div class="p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
          <div class="flex items-center justify-between gap-3">
            <div class="flex items-center gap-3">
              <div class="w-8 h-8 bg-red-100 rounded-lg flex items-center justify-center">
                <span class="material-symbols-outlined text-red-500 text-lg">warning</span>
              </div>
              <label class="text-xs font-bold text-slate-700 uppercase tracking-wide">
                {{ t('app.attackMode') }}
              </label>
            </div>
            <button
              type="button"
              data-testid="simulation-attack-toggle"
              :disabled="isSimulating || (!simulationForm.isAttack && !hasModeledAttackEffect)"
              :title="!hasModeledAttackEffect ? t('app.attackNoModeledEffect') : undefined"
              @click="simulationForm.isAttack = !simulationForm.isAttack"
              class="relative inline-flex h-6 w-11 items-center rounded-full transition-colors disabled:cursor-not-allowed disabled:opacity-60"
              :class="simulationForm.isAttack ? 'bg-red-500' : 'bg-slate-300'"
            >
              <span
                class="h-4 w-4 rounded-full bg-white shadow-md transition-all duration-300 ease-spring"
                :style="{
                  transform: simulationForm.isAttack ? 'translateX(20px)' : 'translateX(4px)',
                  willChange: 'transform'
                }"
              />
            </button>
          </div>
          <p
            v-if="!hasModeledAttackEffect"
            data-testid="simulation-attack-unavailable"
            class="mt-2 text-[10px] leading-4 text-amber-700"
          >
            {{ t('app.attackNoModeledEffect') }}
          </p>
        </div>

        <!-- Attack budget (visible when attack is enabled) -->
        <div v-if="simulationForm.isAttack && hasModeledAttackEffect" class="p-3 bg-red-50 rounded-xl border border-red-200/60">
          <div class="mb-2 flex items-center justify-between gap-2">
            <label for="simulation-attack-budget" class="min-w-0 text-[10px] font-bold text-red-700 uppercase tracking-wide">
              {{ t('app.attackBudgetLabel') }}:
              <span class="text-red-500">{{ simulationForm.attackBudget }} / {{ attackBudgetMax }}</span>
            </label>
            <InfoTooltip
              :text="t('app.simulationAttackBudgetHint', { limit: attackBudgetMax, surface: attackSurfacePointCount })"
              :label="t('app.showHelpFor', { topic: t('app.attackBudgetLabel') })"
              placement="left"
              tone="danger"
              test-id="simulation-attack-budget-help"
            />
          </div>
          <input
            id="simulation-attack-budget"
            v-model.number="simulationForm.attackBudget"
            data-testid="simulation-attack-budget"
            :disabled="isSimulating"
            type="range"
            min="1"
            :max="attackBudgetMax"
            :aria-invalid="Boolean(simulationAttackConfigurationError)"
            class="w-full h-2 bg-red-200 rounded-lg appearance-none cursor-pointer accent-red-500 disabled:cursor-not-allowed disabled:opacity-60"
          />
          <div class="flex justify-between text-[10px] text-red-400 mt-1">
            <span>1</span>
            <span>{{ attackBudgetMax }}</span>
          </div>
          <p v-if="attackBudgetIsCapped" class="mt-1 text-[10px] font-semibold leading-4 text-amber-700" data-testid="simulation-attack-budget-cap">
            {{ t('app.attackBudgetCappedHint', { surface: attackSurfacePointCount, limit: attackBudgetMax }) }}
          </p>
          <p v-if="simulationAttackConfigurationError" class="mt-1 text-[10px] font-semibold leading-4 text-red-700" data-testid="simulation-attack-budget-invalid">
            {{ simulationAttackConfigurationError }}
          </p>
        </div>

        <!-- Privacy Analysis -->
        <div class="p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
          <div class="flex items-center justify-between gap-3">
            <div class="flex min-w-0 items-center gap-3">
              <div class="w-8 h-8 shrink-0 bg-purple-100 rounded-lg flex items-center justify-center">
                <span class="material-symbols-outlined text-purple-500 text-lg">security</span>
              </div>
              <label class="text-xs font-bold text-slate-700 uppercase tracking-wide">
                {{ t('app.privacyAnalysis') }}
              </label>
              <InfoTooltip
                :text="t('app.privacyModelHint')"
                :label="t('app.showHelpFor', { topic: t('app.privacyAnalysis') })"
                placement="left"
                tone="privacy"
                test-id="simulation-privacy-help"
              />
            </div>
            <button
              type="button"
              data-testid="simulation-privacy-toggle"
              :disabled="isSimulating"
              @click="simulationForm.enablePrivacy = !simulationForm.enablePrivacy"
              class="relative inline-flex h-6 w-11 shrink-0 items-center rounded-full transition-colors disabled:cursor-not-allowed disabled:opacity-60"
              :class="simulationForm.enablePrivacy ? 'bg-purple-500' : 'bg-slate-300'"
            >
              <span
                class="h-4 w-4 rounded-full bg-white shadow-md transition-all duration-300 ease-spring"
                :style="{
                  transform: simulationForm.enablePrivacy ? 'translateX(20px)' : 'translateX(4px)',
                  willChange: 'transform'
                }"
              />
            </button>
          </div>
        </div>

        <!-- Run Mode -->
        <div class="p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
          <div class="flex items-center gap-3 mb-2">
            <div class="w-8 h-8 bg-blue-100 rounded-lg flex items-center justify-center">
              <span class="material-symbols-outlined text-blue-500 text-lg">schedule</span>
            </div>
            <label class="text-xs font-bold text-slate-700 uppercase tracking-wide">
              {{ t('app.runMode') }}
            </label>
          </div>
          <div class="grid grid-cols-2 gap-1 rounded-lg bg-slate-100 p-1">
            <button
              type="button"
              :disabled="isSimulating"
              @click="simulationForm.isAsync = false"
              data-testid="simulation-mode-sync"
              :aria-pressed="!simulationForm.isAsync"
              :title="t('app.syncSimulationModeHint')"
              class="min-w-0 rounded-md px-2 py-1.5 text-[11px] font-bold transition-all disabled:cursor-not-allowed disabled:opacity-60"
              :class="!simulationForm.isAsync ? 'bg-white text-indigo-700 shadow-sm' : 'text-slate-500 hover:text-slate-700'"
            >
              {{ t('app.previewNow') }}
            </button>
            <button
              type="button"
              :disabled="isSimulating"
              @click="simulationForm.isAsync = true"
              data-testid="simulation-mode-async"
              :aria-pressed="simulationForm.isAsync"
              :title="t('app.asyncSimulationModeHint')"
              class="min-w-0 rounded-md px-2 py-1.5 text-[11px] font-bold transition-all disabled:cursor-not-allowed disabled:opacity-60"
              :class="simulationForm.isAsync ? 'bg-white text-blue-700 shadow-sm' : 'text-slate-500 hover:text-slate-700'"
            >
              {{ t('app.saveInBackground') }}
            </button>
          </div>
          <p class="mt-2 text-[11px] leading-snug text-slate-500">
            {{ simulationForm.isAsync ? t('app.asyncSimulationModeHint') : t('app.syncSimulationModeHint') }}
          </p>
        </div>

        <!-- Save History -->
        <div class="p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
          <div class="flex items-center justify-between">
            <div class="flex items-center gap-3">
              <div class="w-8 h-8 bg-cyan-100 rounded-lg flex items-center justify-center">
                <span class="material-symbols-outlined text-cyan-600 text-lg">history</span>
              </div>
              <label class="text-xs font-bold text-slate-700 uppercase tracking-wide">
                {{ t('app.saveToHistory') }}
              </label>
            </div>
            <button
              type="button"
              @click="simulationForm.saveToHistory = !simulationForm.saveToHistory"
              data-testid="simulation-save-history"
              :disabled="simulationForm.isAsync || isSimulating"
              class="relative inline-flex h-6 w-11 items-center rounded-full transition-colors disabled:opacity-70 disabled:cursor-not-allowed"
              :class="(simulationForm.isAsync || simulationForm.saveToHistory) ? 'bg-cyan-600' : 'bg-slate-300'"
              :title="simulationForm.isAsync ? t('app.asyncSimulationsSavedAutomatically') : t('app.saveSyncSimulationToHistory')"
            >
              <span
                class="h-4 w-4 rounded-full bg-white shadow-md transition-all duration-300 ease-spring"
                :style="{
                  transform: (simulationForm.isAsync || simulationForm.saveToHistory) ? 'translateX(20px)' : 'translateX(4px)',
                  willChange: 'transform'
                }"
              />
            </button>
          </div>
          <p class="mt-2 pl-11 text-[11px] leading-snug text-slate-500">
            {{ simulationForm.isAsync ? t('app.asyncSimulationsSavedAutomatically') : t('app.saveSyncSimulationToHistory') }}
          </p>
        </div>

        <!-- Async Progress (visible when async simulation is running) -->
        <div v-if="isSimulating && asyncSimulationActive" class="space-y-1">
          <div class="flex items-center justify-between text-xs">
            <span class="text-indigo-700 font-medium">{{ t('app.progress') }}</span>
            <div v-if="asyncSimulationTask.taskId" class="flex items-center gap-2">
              <span class="text-indigo-600">{{ asyncSimulationTask.progress }}%</span>
              <button
                type="button"
                class="w-6 h-6 inline-flex items-center justify-center rounded-md border border-indigo-200 text-indigo-700 hover:bg-indigo-50 disabled:opacity-50 disabled:cursor-not-allowed"
                :disabled="cancellingSimulationTask"
                :title="t('app.cancelSimulationTask')"
                @click="cancelAsyncSimulation"
              >
                <span class="material-symbols-outlined text-sm">{{ cancellingSimulationTask ? 'hourglass_empty' : 'cancel' }}</span>
              </button>
            </div>
          </div>
          <div class="w-full h-2 bg-indigo-200 rounded-full overflow-hidden">
            <div 
              class="h-full bg-green-500 transition-all duration-300"
              :class="{ 'animate-pulse': !asyncSimulationTask.taskId }"
              :style="{ width: asyncSimulationTask.taskId ? `${asyncSimulationTask.progress}%` : '35%' }"
            ></div>
          </div>
          <div class="text-xs text-indigo-500 text-center">{{ asyncSimulationTask.status }}</div>
        </div>

        <!-- Simulate Button -->
        <button
          @click="runSimulation"
          data-testid="run-simulation"
          :disabled="isSimulating || traceAnimationState.visible || simulationAnimationState.visible || Boolean(simulationRunBlockedReason)"
          :title="simulationRunBlockedReason || undefined"
          class="w-full py-2.5 bg-indigo-600 hover:bg-indigo-700 disabled:bg-indigo-300 text-white rounded-lg text-xs font-bold uppercase tracking-wider transition-all shadow-md hover:shadow-lg hover:scale-[1.02] active:scale-[0.98] flex items-center justify-center gap-2 disabled:cursor-not-allowed disabled:hover:scale-100"
        >
          <template v-if="!isBoardDataReady && failedBoardDataKeys.length === 0">
            <span class="material-symbols-outlined text-sm animate-spin">sync</span>
            {{ t('app.loading') }}
          </template>
          <template v-else-if="isSimulating">
            <span class="material-symbols-outlined text-sm animate-spin">sync</span>
            {{ simulationForm.isAsync ? t('app.runningAsync') : t('app.running') }}
          </template>
          <template v-else>
            <span class="material-symbols-outlined text-sm">play_arrow</span>
            {{ simulationForm.isAsync ? t('app.createSimulationTask') : t('app.runSimulationNow') }}
          </template>
        </button>
      </div>
    </div>

    <!-- Floating panels -->
    <div>

    </div>

    <DeviceDialog
        v-if="dialogVisible"
        :visible="dialogVisible"
        :device-name="dialogMeta.deviceName"
        :description="dialogMeta.description"
        :label="dialogMeta.label"
        :node-id="dialogMeta.nodeId"
        :manifest="dialogMeta.manifest"
        :nodes="nodes"
        :device-templates="deviceTemplates"
        :rules="dialogMeta.rules"
        :specs="dialogMeta.specs"
        :runtime-saving="deviceRuntimeSaving"
        @update:visible="dialogVisible = $event"
        @rename="handleDialogRename"
        @delete="handleDialogDelete"
        @save-runtime="handleDeviceRuntimeSave"
    />

    <!-- Context Menu for Node Right Click -->
    <div
      v-if="contextMenu.visible"
      class="board-context-menu fixed z-50 border rounded-lg shadow-lg py-2 min-w-48"
      :style="{ left: contextMenu.x + 'px', top: contextMenu.y + 'px' }"
      @click.stop
    >
      <div class="px-3 py-2 text-xs font-semibold text-slate-500 uppercase tracking-wider border-b border-slate-100">
        {{ contextMenu.node?.label }}
      </div>
      <button
        @click="renameDevice"
        class="w-full px-3 py-2 text-left text-sm text-slate-700 hover:bg-slate-50 flex items-center gap-2"
      >
        <span class="material-icons-round text-base">edit</span>
        {{ t('app.rename') }}
      </button>
      <button
        @click="viewDeviceDetails"
        class="w-full px-3 py-2 text-left text-sm text-slate-700 hover:bg-slate-50 flex items-center gap-2"
      >
        <span class="material-icons-round text-base">visibility</span>
        {{ t('app.viewDetails') }}
      </button>
      <div class="border-t border-slate-100 my-1"></div>
      <button
        @click="deleteDevice"
        class="w-full px-3 py-2 text-left text-sm text-red-600 hover:bg-red-50 flex items-center gap-2"
      >
        <span class="material-icons-round text-base">delete</span>
        {{ t('app.deleteDevice') }}
      </button>
    </div>

    <!-- Click outside to close context menu -->
    <div
      v-if="contextMenu.visible"
      class="fixed inset-0 z-40"
      @click="closeContextMenu"
    ></div>


    <RuleBuilderDialog
        v-if="ruleBuilderVisible"
        v-model="ruleBuilderVisible"
        :nodes="nodes"
        :device-templates="deviceTemplates"
        @save-rule="handleAddRule"
    />

    <!-- Custom Rename Dialog -->
    <Teleport to="body">
      <div
        v-if="renameDialogVisible"
        class="fixed inset-0 z-[2400] flex items-center justify-center bg-slate-950/20 p-4 backdrop-blur-[2px] dark:bg-slate-950/35"
        @click.self="cancelRename"
        @keydown="handleRenameDialogKeydown"
      >
        <div
          :ref="setRenameDialogRef"
          class="w-96 max-w-[calc(100vw-2rem)] rounded-xl border border-slate-200 bg-white p-6 shadow-2xl dark:border-slate-700 dark:bg-slate-900"
          role="dialog"
          aria-modal="true"
          aria-labelledby="rename-device-dialog-title"
          tabindex="-1"
          @click.stop
        >
          <div class="mb-6">
            <h3 id="rename-device-dialog-title" class="mb-4 text-lg font-semibold text-slate-800 dark:text-slate-100">{{ t('app.renameDevice') }}</h3>
            <div class="space-y-2">
              <input
                v-model="renameDialogData.newName"
                @keyup.enter="confirmRename"
                class="w-full rounded-lg border border-slate-300 bg-white px-3 py-2 text-slate-900 transition-colors focus:border-blue-500 focus:ring-2 focus:ring-blue-500 dark:border-slate-600 dark:bg-slate-800 dark:text-slate-100"
                :placeholder="t('app.enterDeviceName')"
              />
            </div>
          </div>
          <div class="flex justify-end space-x-3">
            <button
              @click="cancelRename"
              class="rounded-lg border border-slate-300 bg-slate-100 px-4 py-2 text-sm font-medium text-slate-700 transition-colors hover:bg-slate-200 dark:border-slate-600 dark:bg-slate-800 dark:text-slate-200 dark:hover:bg-slate-700"
            >
              {{ t('app.cancel') }}
            </button>
            <button
              @click="confirmRename"
              :disabled="!renameDialogData.newName.trim() || renameDialogData.newName.trim() === renameDialogData.node?.label"
              class="rounded-lg border border-transparent bg-blue-600 px-4 py-2 text-sm font-medium text-white transition-colors hover:bg-blue-700 disabled:cursor-not-allowed disabled:opacity-50"
            >
              {{ t('app.confirm') }}
            </button>
          </div>
        </div>
      </div>
    </Teleport>

    <!-- Custom Delete Confirmation Dialog -->
    <Teleport to="body">
      <div
        v-if="deleteConfirmDialogVisible"
        class="fixed inset-0 z-[2400] flex items-center justify-center bg-slate-950/20 p-4 backdrop-blur-[2px] dark:bg-slate-950/35"
        @click.self="cancelDelete"
        @keydown="handleDeleteConfirmDialogKeydown"
      >
        <div
          :ref="setDeleteConfirmDialogRef"
          class="w-96 max-w-[calc(100vw-2rem)] rounded-xl border border-slate-200 bg-white p-6 shadow-2xl dark:border-slate-700 dark:bg-slate-900"
          role="dialog"
          aria-modal="true"
          aria-labelledby="delete-device-dialog-title"
          tabindex="-1"
          @click.stop
        >
          <div class="mb-6">
            <div class="flex items-center mb-4">
              <div class="flex-shrink-0 w-10 h-10 bg-red-100 rounded-full flex items-center justify-center dark:bg-red-950/50">
                <span class="material-symbols-outlined text-red-600 dark:text-red-300" aria-hidden="true">warning</span>
              </div>
              <div class="ml-3">
                <h3 id="delete-device-dialog-title" class="text-lg font-semibold text-slate-800 dark:text-slate-100">{{ t('app.deleteDeviceTitle') }}</h3>
                <p class="text-sm text-slate-600 dark:text-slate-400">{{ t('app.actionCannotBeUndone') }}</p>
              </div>
            </div>

            <div v-if="deleteConfirmDialogData.hasRelations" class="bg-yellow-50 border border-yellow-200 rounded-lg p-4 mb-4 dark:border-yellow-900/60 dark:bg-yellow-950/30">
              <div class="flex items-start">
                <span class="material-symbols-outlined text-yellow-600 mr-2 mt-0.5 dark:text-yellow-300" aria-hidden="true">info</span>
                <div>
                  <p class="text-sm font-medium text-yellow-800 mb-1 dark:text-yellow-100">{{ t('app.deviceDeleteConsequences') }}</p>
                  <div class="text-xs text-yellow-700 space-y-1 dark:text-yellow-200">
                    <div v-if="deleteConfirmDialogData.relationCount.rules > 0">
                      • {{ t('app.relatedRulesWillBeDeleted', { count: deleteConfirmDialogData.relationCount.rules }) }}
                      <ul class="mt-1 ml-4 list-disc break-words">
                        <li v-for="(label, index) in deleteConfirmDialogData.relatedRules" :key="`delete-rule-${index}`">
                          {{ label }}
                        </li>
                      </ul>
                    </div>
                    <div v-if="deleteConfirmDialogData.relationCount.specs > 0">
                      • {{ t('app.relatedSpecsWillBeDeleted', { count: deleteConfirmDialogData.relationCount.specs }) }}
                      <ul class="mt-1 ml-4 list-disc break-words">
                        <li v-for="(label, index) in deleteConfirmDialogData.relatedSpecs" :key="`delete-spec-${index}`">
                          {{ label }}
                        </li>
                      </ul>
                    </div>
                    <div v-if="deleteConfirmDialogData.environmentChanges.length > 0">
                      • {{ t('app.environmentVariablesWillChange', { count: deleteConfirmDialogData.environmentChanges.length }) }}
                      <ul class="mt-1 ml-4 list-disc break-words">
                        <li
                          v-for="change in deleteConfirmDialogData.environmentChanges"
                          :key="`delete-environment-${change.changeType}-${change.name}`"
                        >
                          {{ formatEnvironmentChange(change) }}
                        </li>
                      </ul>
                    </div>
                  </div>
                </div>
              </div>
            </div>
          </div>

          <div class="flex justify-end space-x-3">
            <button
              type="button"
              @click="cancelDelete"
              class="px-4 py-2 text-sm font-medium text-slate-700 bg-slate-100 border border-slate-300 rounded-lg hover:bg-slate-200 transition-colors dark:border-slate-600 dark:bg-slate-800 dark:text-slate-200 dark:hover:bg-slate-700"
            >
              {{ t('app.cancel') }}
            </button>
            <button
              type="button"
              @click="confirmDelete"
              :disabled="!deleteConfirmDialogData.impactToken"
              class="px-4 py-2 text-sm font-medium text-white bg-red-600 border border-transparent rounded-lg hover:bg-red-700 transition-colors disabled:cursor-not-allowed disabled:opacity-50 dark:bg-red-600 dark:hover:bg-red-500"
            >
              {{ t('app.deleteDevice') }}
            </button>
          </div>
        </div>
      </div>
    </Teleport>
  </div>

  <FuzzingResultDialog
    v-if="showFuzzingResultDialog"
    :visible="showFuzzingResultDialog"
    :run="fuzzingResult"
    :loading="fuzzingResultLoading"
    :error="fuzzingError"
    :action-locked="historyActionLocked"
    :board-drifted="fuzzingResultBoardDrifted"
    @close="closeFuzzingResult"
    @replay="selectAndPlayFuzzingFinding($event, fuzzingResult?.id)"
    @verify="openFormalVerificationForFuzzFinding"
    @verify-current-board="openFormalVerificationForCurrentBoard"
    @reuse-settings="reuseFuzzingSettings"
  />

  <!-- Simulation Run Details Dialog -->
  <div
    v-if="simulationResult || simulationError"
    data-testid="simulation-result-dialog"
    class="fixed inset-0 z-[2400] bg-black/60 backdrop-blur-sm flex items-center justify-center"
    @click="closeSimulationResultDialog"
    @keydown="handleSimulationResultDialogKeydown"
  >
    <div
      :ref="setSimulationResultDialogRef"
      class="min-h-0 flex max-h-[90vh] w-[760px] max-w-[95vw] flex-col overflow-hidden rounded-xl border border-slate-200 bg-white shadow-2xl"
      role="dialog"
      aria-modal="true"
      aria-labelledby="simulation-result-dialog-title"
      tabindex="-1"
      @click.stop
    >
      <header class="flex flex-shrink-0 items-center justify-between gap-4 border-b border-slate-200 bg-slate-50 px-5 py-4">
          <div class="flex min-w-0 items-center gap-3">
            <div class="flex h-10 w-10 flex-shrink-0 items-center justify-center rounded-lg bg-indigo-100 text-indigo-700">
              <span class="material-symbols-outlined text-2xl" aria-hidden="true">monitoring</span>
            </div>
            <div class="min-w-0">
              <h3 id="simulation-result-dialog-title" class="text-base font-bold text-slate-900">{{ t('app.simulationRunDetails') }}</h3>
              <p v-if="simulationResult" class="mt-0.5 text-xs leading-5 text-slate-600">
                {{ t('app.simulationStateStepSummary', {
                  states: getSimulationStateCount(simulationResult),
                  steps: getSimulationActualStepCount(simulationResult),
                  requested: getSimulationRequestedStepCount(simulationResult)
                }) }}
              </p>
              <p v-else class="mt-0.5 text-xs text-red-600">{{ t('app.simulationFailed') }}</p>
            </div>
          </div>
          <button
            type="button"
            data-testid="close-simulation-result"
            class="flex h-9 w-9 flex-shrink-0 items-center justify-center rounded-lg text-slate-500 transition-colors hover:bg-slate-200 hover:text-slate-800"
            :aria-label="t('app.close')"
            @click="closeSimulationResultDialog"
          >
            <span class="material-symbols-outlined text-xl" aria-hidden="true">close</span>
          </button>
      </header>

      <div v-if="simulationError" class="min-h-0 flex-1 overflow-y-auto p-5">
        <div class="rounded-lg border border-red-200 bg-red-50 p-4">
          <div class="flex items-start gap-2 text-red-700">
            <span class="material-symbols-outlined" aria-hidden="true">error</span>
            <span class="text-sm font-medium leading-6">{{ simulationError }}</span>
          </div>
        </div>
      </div>

      <div v-else-if="simulationResult" class="min-h-0 flex-1 space-y-4 overflow-y-auto p-5">
        <div
          v-if="!isSimulationModelComplete(simulationResult)"
          class="rounded-lg border border-amber-300 bg-amber-50 px-4 py-3 text-sm text-amber-800"
        >
          <p>{{ t('app.simulationIncompleteModelDetail', { rules: getSimulationDisabledRuleCount(simulationResult) }) }}</p>
          <ul v-if="getGenerationIssues(simulationResult).length > 0" class="mt-3 space-y-2">
            <li
              v-for="(issue, index) in getGenerationIssues(simulationResult)"
              :key="`${issue.issueType}-${issue.itemLabel}-${index}`"
              class="border-l-2 border-amber-300 pl-3"
            >
              <div class="text-xs font-bold text-amber-900">{{ issue.itemLabel }}</div>
              <div class="mt-0.5 text-xs leading-5 text-amber-800">{{ t(generationIssueReasonKey(issue)) }}</div>
            </li>
          </ul>
          <p v-else class="mt-2 text-xs text-amber-700">
            {{ t('app.generationIssueDetailsUnavailable') }}
          </p>
        </div>

        <div
          v-if="isSimulationHorizonShorterThanRequested(simulationResult)"
          class="rounded-lg border border-amber-300 bg-amber-50 px-4 py-3 text-sm text-amber-800"
          data-testid="simulation-short-horizon-warning"
        >
          {{ t('app.simulationStoppedBeforeRequestedSteps', {
            actual: getSimulationActualStepCount(simulationResult),
            requested: getSimulationRequestedStepCount(simulationResult)
          }) }}
        </div>

        <div
          v-if="!isSimulationModelSemanticsConsistent(simulationResult)"
          class="rounded-lg border border-amber-300 bg-amber-50 px-4 py-3 text-sm text-amber-800"
        >
          {{ t('app.modelSemanticsUnavailable') }}
        </div>

        <section aria-labelledby="simulation-run-summary-title">
          <div class="flex items-center justify-between gap-3">
            <h4 id="simulation-run-summary-title" class="text-sm font-bold text-slate-800">{{ t('app.runSummary') }}</h4>
            <div class="flex flex-wrap justify-end gap-1.5">
              <span v-if="simulationResult.isAttack" class="rounded-full bg-orange-100 px-2 py-1 text-[11px] font-semibold text-orange-700">
                {{ t('app.traceVisualization.attackBudget') }} {{ simulationResult.attackBudget ?? 0 }}
              </span>
              <span v-else class="rounded-full bg-slate-100 px-2 py-1 text-[11px] font-semibold text-slate-600">
                {{ t('app.traceVisualization.noAttackModelShort') }}
              </span>
              <span v-if="simulationResult.enablePrivacy" class="rounded-full bg-fuchsia-100 px-2 py-1 text-[11px] font-semibold text-fuchsia-700">
                {{ t('app.traceVisualization.privacyPropagationEnabled') }}
              </span>
              <span v-else class="rounded-full bg-slate-100 px-2 py-1 text-[11px] font-semibold text-slate-600">
                {{ t('app.traceVisualization.privacyPropagationNotModeled') }}
              </span>
            </div>
          </div>
          <div class="mt-3 grid grid-cols-2 gap-px overflow-hidden rounded-lg border border-slate-200 bg-slate-200 sm:grid-cols-4">
            <div class="bg-white p-3">
              <div class="text-[10px] font-bold uppercase text-slate-500">{{ t('app.modelStates') }}</div>
              <div class="mt-1 text-xl font-bold text-slate-900">{{ getSimulationStateCount(simulationResult) }}</div>
            </div>
            <div class="bg-white p-3">
              <div class="text-[10px] font-bold uppercase text-slate-500">{{ t('app.actualSimulationSteps') }}</div>
              <div class="mt-1 text-xl font-bold text-slate-900">{{ getSimulationActualStepCount(simulationResult) }}</div>
            </div>
            <div class="bg-white p-3">
              <div class="text-[10px] font-bold uppercase text-slate-500">{{ t('app.requestedSimulationSteps') }}</div>
              <div class="mt-1 text-xl font-bold text-slate-900">{{ getSimulationRequestedStepCount(simulationResult) }}</div>
            </div>
            <div class="bg-white p-3">
              <div class="text-[10px] font-bold uppercase text-slate-500">{{ t('app.modelCoverage') }}</div>
              <div class="mt-1 text-sm font-bold" :class="isSimulationModelComplete(simulationResult) ? 'text-emerald-700' : 'text-amber-700'">
                {{ isSimulationModelComplete(simulationResult) ? t('app.completeModel') : t('app.incompleteModel') }}
              </div>
            </div>
          </div>
          <p class="mt-3 text-xs leading-5 text-slate-600">{{ t('app.simulationTimelineIsPrimaryView') }}</p>
        </section>

        <details class="group border-t border-slate-200 pt-3" data-testid="simulation-state-snapshots">
          <summary class="flex cursor-pointer list-none items-center justify-between text-sm font-bold text-slate-700 hover:text-slate-900">
            <span class="inline-flex items-center gap-2">
              <span class="material-symbols-outlined text-lg text-slate-500" aria-hidden="true">table_rows</span>
              {{ t('app.simulationStates') }} ({{ getSimulationStateCount(simulationResult) }})
            </span>
            <span class="material-symbols-outlined transition-transform group-open:rotate-180" aria-hidden="true">expand_more</span>
          </summary>
          <div class="mt-3 max-h-64 overflow-y-auto rounded-lg border border-slate-200">
            <table class="w-full text-xs">
              <thead class="sticky top-0 bg-slate-50">
                <tr>
                  <th class="border-b p-2 text-left font-bold text-slate-600">{{ t('app.stateNumber') }}</th>
                  <th class="border-b p-2 text-left font-bold text-slate-600">{{ t('app.devicesColumn') }}</th>
                </tr>
              </thead>
              <tbody>
                <tr v-for="(state, idx) in simulationResult.states" :key="idx" class="border-b border-slate-100 last:border-b-0">
                  <td class="p-2 align-top font-mono text-indigo-700">{{ state.stateIndex }}</td>
                  <td class="p-2">
                    <div class="flex flex-wrap gap-1">
                      <span
                        v-for="(device, dIdx) in state.devices"
                        :key="dIdx"
                        class="inline-flex items-center gap-1 rounded bg-slate-100 px-2 py-0.5 text-slate-700"
                      >
                        <span class="font-medium">{{ device.deviceLabel || t('app.unknownModelItem') }}</span>
                        <span class="text-slate-400">:</span>
                        <span class="text-indigo-700">{{ device.state || 'N/A' }}</span>
                      </span>
                    </div>
                  </td>
                </tr>
              </tbody>
            </table>
          </div>
        </details>

        <details class="group border-t border-slate-200 pt-3" data-testid="simulation-execution-logs">
          <summary class="flex cursor-pointer list-none items-center justify-between text-sm font-bold text-slate-700 hover:text-slate-900">
            <span class="inline-flex items-center gap-2">
              <span class="material-symbols-outlined text-lg text-slate-500" aria-hidden="true">terminal</span>
              {{ t('app.executionLogs') }}
            </span>
            <span class="material-symbols-outlined transition-transform group-open:rotate-180" aria-hidden="true">expand_more</span>
          </summary>
          <p class="mt-2 text-xs leading-5 text-slate-500">{{ t('app.executionLogsDiagnosticHint') }}</p>
          <div class="mt-2 max-h-48 overflow-y-auto rounded-lg bg-slate-950 p-3">
            <pre class="whitespace-pre-wrap font-mono text-xs leading-5 text-emerald-300">{{ simulationResult.logs?.join('\n') || t('app.noLogsAvailableShort') }}</pre>
          </div>
        </details>

        <details class="group border-t border-slate-200 pt-3">
          <summary class="flex cursor-pointer list-none items-center justify-between text-sm font-bold text-slate-700 hover:text-slate-900">
            <span class="inline-flex items-center gap-2">
              <span class="material-symbols-outlined text-lg text-slate-500" aria-hidden="true">code</span>
              {{ t('app.showRawNusmvOutput') }}
            </span>
            <span class="material-symbols-outlined transition-transform group-open:rotate-180" aria-hidden="true">expand_more</span>
          </summary>
          <div class="mt-2 max-h-56 overflow-y-auto rounded-lg bg-slate-950 p-3">
            <pre class="whitespace-pre-wrap font-mono text-xs leading-5 text-slate-300">{{ simulationResult.nusmvOutput || t('app.noOutput') }}</pre>
          </div>
        </details>
      </div>

      <footer class="flex flex-shrink-0 justify-end gap-3 border-t border-slate-200 bg-white px-5 py-4">
        <button
          v-if="simulationResult && simulationResult.states && simulationResult.states.length > 0"
          type="button"
          :disabled="traceAnimationState.visible"
          :class="[
            'flex items-center gap-2 rounded-lg px-4 py-2 text-sm font-semibold transition-colors',
            traceAnimationState.visible
              ? 'cursor-not-allowed bg-slate-200 text-slate-500'
              : 'bg-indigo-600 text-white hover:bg-indigo-700'
          ]"
          @click="handleSimulationTimelineAction"
        >
          <span class="material-symbols-outlined text-lg" aria-hidden="true">play_circle</span>
          {{ simulationAnimationState.visible ? t('app.returnToTimeline') : t('app.viewTimeline') }}
          <span v-if="traceAnimationState.visible" class="text-xs ml-1">({{ t('app.active') }})</span>
        </button>
        <button
          type="button"
          class="rounded-lg bg-slate-200 px-4 py-2 text-sm font-semibold text-slate-700 transition-colors hover:bg-slate-300"
          @click="closeSimulationResultDialog"
        >
          {{ t('app.close') }}
        </button>
      </footer>
    </div>
  </div>

  <!-- Verification Result Dialog -->
  <div
    v-if="showResultDialog"
    data-testid="verification-result-dialog"
    class="fixed inset-0 z-[2400] bg-black/60 backdrop-blur-sm flex items-center justify-center"
    @click="closeResultDialog"
  >
    <div class="min-h-0 max-h-[85vh] w-[650px] max-w-[95vw] overflow-hidden rounded-2xl border border-slate-200 bg-white shadow-2xl flex flex-col" @click.stop>
      <!-- Header -->
      <div data-testid="verification-result-header" class="relative flex-shrink-0 overflow-hidden rounded-t-2xl border-b" :class="verificationResultStatus.headerClass">
        <div class="relative flex items-center justify-between p-5">
          <div class="flex items-center gap-4">
            <div class="w-12 h-12 rounded-xl flex items-center justify-center shadow-sm" :class="verificationResultStatus.iconBgClass">
              <span class="material-symbols-outlined text-2xl" :class="verificationResultStatus.iconTextClass">
                {{ verificationResultStatus.icon }}
              </span>
            </div>
            <div>
              <h3 class="text-xl font-bold text-slate-800">{{ t('app.verificationResult') }}</h3>
              <p class="text-sm text-slate-600">{{ verificationResultStatus.detail }}</p>
            </div>
          </div>
          <button
            type="button"
            data-testid="close-verification-result"
            @click="closeResultDialog"
            :aria-label="t('app.close')"
            :title="t('app.close')"
            class="w-9 h-9 flex items-center justify-center rounded-lg text-slate-500 hover:text-slate-700 hover:bg-slate-200 transition-all"
          >
            <span class="material-symbols-outlined text-xl" aria-hidden="true">close</span>
          </button>
        </div>
      </div>

      <div data-testid="verification-result-scroll" class="min-h-0 flex-1 overflow-y-auto p-6">
        <div v-if="verificationError" class="mb-4 p-4 bg-red-50 border border-red-200 rounded-xl">
          <div class="flex items-center gap-2 text-red-600">
            <span class="material-symbols-outlined">error</span>
            <span class="font-medium">{{ verificationError }}</span>
          </div>
        </div>

        <div v-else-if="verificationResult" class="space-y-4">
          <!-- Status Card -->
          <div class="p-5 rounded-xl" :class="verificationResultStatus.cardClass">
            <div class="flex items-center gap-3">
              <div class="w-10 h-10 rounded-xl flex items-center justify-center" :class="verificationResultStatus.iconBgClass">
                <span class="material-symbols-outlined" :class="verificationResultStatus.iconTextClass">
                  {{ verificationResultStatus.icon }}
                </span>
              </div>
              <div>
                <span class="text-lg font-bold" :class="verificationResultStatus.titleClass">
                  {{ verificationResultStatus.title }}
                </span>
                <p class="text-sm" :class="verificationResultStatus.detailClass">
                  {{ verificationResultStatus.detail }}
                </p>
              </div>
            </div>
          </div>

          <div class="p-4 rounded-xl border border-slate-200 bg-white" data-testid="verification-model-snapshot">
            <div class="flex items-start gap-2">
              <span class="material-symbols-outlined text-lg text-slate-600" aria-hidden="true">inventory_2</span>
              <div class="min-w-0">
                <h4 class="text-sm font-bold text-slate-700">{{ t('app.modelRunSnapshotTitle') }}</h4>
                <p class="mt-1 text-xs leading-5 text-slate-600">
                  {{ t('app.modelRunSnapshotSummary', {
                    time: formatRunTimestamp(verificationResult.modelSnapshot.capturedAt),
                    devices: verificationResult.modelSnapshot.deviceCount,
                    rules: verificationResult.modelSnapshot.ruleCount,
                    specs: verificationResult.modelSnapshot.specificationCount,
                    variables: verificationResult.modelSnapshot.environmentVariableCount,
                    templates: verificationResult.modelSnapshot.deviceTemplateCount
                  }) }}
                </p>
                <p class="mt-1 text-xs leading-5 text-slate-600">{{ t('app.modelRunSnapshotScope') }}</p>
              </div>
            </div>
            <div
              class="mt-3 rounded-md border px-3 py-2 text-xs font-semibold leading-5"
              :class="verificationBoardComparison === 'UNCHANGED'
                ? 'border-emerald-200 bg-emerald-50 text-emerald-800'
                : verificationBoardComparison === 'CHANGED'
                  ? 'border-amber-300 bg-amber-50 text-amber-900'
                  : 'border-slate-200 bg-slate-50 text-slate-700'"
              data-testid="verification-board-comparison"
            >
              {{ verificationBoardComparison === 'UNCHANGED'
                ? t('app.runBoardInputUnchanged')
                : verificationBoardComparison === 'CHANGED'
                  ? t('app.runBoardInputChanged')
                  : verificationBoardComparison === 'UNAVAILABLE'
                    ? t('app.runBoardComparisonUnavailable')
                    : t('app.runBoardNotCompared') }}
            </div>
          </div>

          <div class="p-4 rounded-xl bg-slate-50 border border-slate-200">
            <h4 class="text-sm font-bold text-slate-700 mb-2">{{ t('app.modelAssumptions') }}</h4>
            <div
              v-if="!verificationModelSemanticsConsistent"
              class="mb-2 rounded border border-amber-200 bg-amber-50 px-2 py-1.5 text-xs font-semibold text-amber-800"
            >
              {{ t('app.modelSemanticsUnavailable') }}
            </div>
            <div class="space-y-2 text-xs leading-5 text-slate-600">
              <div v-if="verificationModelSemanticsConsistent" class="flex items-start gap-2">
                <span class="material-symbols-outlined text-base text-cyan-700">landscape</span>
                <span>{{ t('app.environmentEvolutionIncluded') }}</span>
              </div>
              <div v-if="verificationModelSemanticsConsistent" class="flex items-start gap-2">
                <span class="material-symbols-outlined text-base text-emerald-600">verified_user</span>
                <span>{{ t('app.trustPropagationIncluded') }}</span>
              </div>
              <div v-if="verificationModelSemanticsConsistent" class="flex items-start gap-2">
                <span class="material-symbols-outlined text-base text-violet-600">sync_alt</span>
                <span>{{ t('app.labelPropagationScopeSummary') }}</span>
              </div>
              <div v-if="verificationModelSemanticsConsistent" class="flex items-start gap-2">
                <span class="material-symbols-outlined text-base" :class="verificationResult.isAttack ? 'text-red-500' : 'text-slate-400'">security</span>
                <span>
                  {{ verificationResult.isAttack
                    ? t('app.verificationAttackCoverage', {
                        count: verificationResult.attackBudget ?? 0,
                        total: verificationResult.modelSemantics?.modeledAttackPointCount ?? 0,
                        devices: verificationResult.modelSemantics?.modeledDeviceAttackPointCount ?? 0,
                        falsifiable: verificationResult.modelSemantics?.modeledFalsifiableReadingDeviceCount ?? 0,
                        links: verificationResult.modelSemantics?.modeledAutomationLinkAttackPointCount ?? 0
                      })
                    : t('app.verificationNoAttackCoverage') }}
                </span>
              </div>
              <div v-if="verificationModelSemanticsConsistent" class="flex items-start gap-2">
                <span class="material-symbols-outlined text-base" :class="verificationResult.enablePrivacy ? 'text-fuchsia-600' : 'text-slate-400'">shield_lock</span>
                <span>
                  {{ verificationResult.enablePrivacy
                    ? t('app.privacyPropagationIncluded')
                    : t('app.privacyPropagationNotIncluded') }}
                </span>
              </div>
            </div>
          </div>

          <div v-if="verificationSpecResultSummary.total > 0" class="p-4 rounded-xl bg-slate-50 border border-slate-200">
            <div class="flex items-start justify-between gap-3 mb-3">
              <div>
                <h4 class="text-sm font-bold text-slate-700">{{ t('app.specResults') }}</h4>
                <p class="text-xs text-slate-500 mt-1">
                  {{ t('app.specResultsSummary', {
                    total: verificationSpecResultSummary.total,
                    satisfied: verificationSpecResultSummary.satisfied,
                    violated: verificationSpecResultSummary.violated,
                    inconclusive: verificationSpecResultSummary.inconclusive
                  }) }}
                </p>
              </div>
              <span
                class="material-symbols-outlined text-lg"
                :class="verificationSpecResultSummary.violated > 0
                  ? 'text-red-500'
                  : verificationSpecResultSummary.inconclusive > 0 ? 'text-amber-500' : 'text-green-500'"
              >
                {{ verificationSpecResultSummary.violated > 0
                  ? 'rule'
                  : verificationSpecResultSummary.inconclusive > 0 ? 'help' : 'verified' }}
              </span>
            </div>
            <div class="space-y-2 max-h-72 overflow-y-auto pr-1">
              <div
                v-for="(result, index) in verificationSpecResultSummary.results"
                :key="`${result.specId}-${index}`"
                class="rounded-lg border bg-white px-3 py-2"
                :class="result.presentation.borderClass"
              >
                <div class="flex items-start justify-between gap-3">
                  <div class="min-w-0 flex-1">
                    <div class="flex flex-wrap items-center gap-2">
                      <span class="text-xs font-semibold text-slate-500">#{{ Number(index) + 1 }}</span>
                      <span class="text-xs font-semibold text-slate-700">{{ result.displayTitle }}</span>
                      <span class="rounded bg-slate-100 px-1.5 py-0.5 text-[10px] font-bold text-slate-600">{{ result.formulaKind }}</span>
                    </div>
                    <div class="mt-2 rounded-md bg-slate-50 px-2 py-1.5">
                      <p class="mb-1 text-[10px] font-bold uppercase tracking-wide text-slate-400">{{ t('app.formulaPreview') }}</p>
                      <p class="max-w-full font-mono text-xs leading-5 text-slate-600 break-all">
                        {{ result.formulaPreview }}
                      </p>
                    </div>
                    <details v-if="result.specId || result.expression" class="mt-2 text-[11px] text-slate-500">
                      <summary class="cursor-pointer font-semibold">{{ t('app.technicalDetails') }}</summary>
                      <div class="mt-1 grid gap-1 sm:grid-cols-[9rem_minmax(0,1fr)]">
                        <span class="font-medium">{{ t('app.actualCheckedExpression') }}</span>
                        <code class="break-all rounded bg-slate-50 px-2 py-1 text-[11px] text-slate-700">{{ result.expression }}</code>
                        <span class="font-medium">{{ t('app.specificationTechnicalId') }}</span>
                        <code class="break-all rounded bg-slate-50 px-2 py-1 text-[11px] text-slate-700">{{ result.specId }}</code>
                      </div>
                    </details>
                  </div>
                  <span
                    class="inline-flex shrink-0 items-center gap-1 rounded-full border px-2 py-0.5 text-xs font-semibold"
                    :class="result.presentation.badgeClass"
                  >
                    <span class="material-symbols-outlined text-sm">{{ result.presentation.icon }}</span>
                    {{ result.presentation.label }}
                  </span>
                </div>
              </div>
            </div>
          </div>

          <div v-if="verificationGenerationWarningCounts.total > 0" class="p-4 rounded-xl bg-amber-50 border border-amber-200 text-amber-800">
            <div class="flex items-start gap-3">
              <span class="material-symbols-outlined text-amber-600">report</span>
              <div>
                <div class="text-sm font-bold">{{ t('app.generationWarnings') }}</div>
                <p class="text-sm mt-1">
                  {{ t('app.disabledRulesSkippedSpecs', { rules: verificationGenerationWarningCounts.disabledRuleCount, specs: verificationGenerationWarningCounts.skippedSpecCount }) }}
                </p>
                <ul v-if="verificationGenerationIssues.length > 0" class="mt-3 space-y-2">
                  <li
                    v-for="(issue, index) in verificationGenerationIssues"
                    :key="`${issue.issueType}-${issue.itemLabel}-${index}`"
                    class="border-l-2 border-amber-300 pl-3"
                  >
                    <div class="text-xs font-bold text-amber-900">{{ issue.itemLabel }}</div>
                    <div class="mt-0.5 text-xs leading-5 text-amber-800">{{ t(generationIssueReasonKey(issue)) }}</div>
                  </li>
                </ul>
                <p v-else class="mt-2 text-xs text-amber-700">
                  {{ t('app.generationIssueDetailsUnavailable') }}
                </p>
              </div>
            </div>
          </div>

          <div v-if="verificationCheckLogs.length > 0" class="p-4 rounded-xl bg-slate-50 border border-slate-200">
            <h4 class="text-sm font-bold text-slate-700 mb-2">{{ t('app.checkLogs') }}</h4>
            <div class="space-y-1 max-h-44 overflow-y-auto">
              <div
                v-for="(log, index) in verificationCheckLogs"
                :key="index"
                class="text-xs font-mono text-slate-700 bg-white border border-slate-100 rounded px-2 py-1 break-words"
              >
                {{ log }}
              </div>
            </div>
          </div>

          <details v-if="verificationResult.nusmvOutput" class="p-4 rounded-xl bg-slate-50 border border-slate-200">
            <summary class="text-sm font-bold text-slate-700 cursor-pointer hover:text-slate-900">
              {{ t('app.showRawNusmvOutput') }}
            </summary>
            <div class="mt-3 bg-slate-900 rounded-lg p-3 max-h-40 overflow-y-auto">
              <pre class="text-xs text-slate-300 font-mono whitespace-pre-wrap">{{ verificationResult.nusmvOutput || t('app.noOutput') }}</pre>
            </div>
          </details>
        </div>

        <div v-if="verificationResult && getVerificationOutcome(verificationResult) === 'VIOLATED' && verificationResult.traces && verificationResult.traces.length > 0">
          <h4 class="text-sm font-bold text-slate-700 mb-2">{{ t('app.violationsTitle') }} ({{ verificationResult.traces.length }})</h4>
          <div class="space-y-2">
            <div v-for="(trace, i) in verificationResult.traces" :key="i" class="border border-slate-200 rounded p-3">
              <div class="flex items-center justify-between mb-1">
                <div class="text-xs font-bold text-red-600">{{ t('app.violationNumber', { index: Number(i) + 1 }) }}</div>
                <div class="flex gap-1">
                  <button
                    @click="openFixDialog(trace.id, trace.violatedSpecId)"
                    class="px-2 py-1 bg-blue-500 hover:bg-blue-600 text-white rounded text-xs font-medium transition-colors flex items-center gap-1"
                    :disabled="simulationAnimationState.visible"
                    :class="simulationAnimationState.visible ? 'bg-slate-300 cursor-not-allowed' : ''"
                  >
                    <span class="material-symbols-outlined text-xs">build</span>
                    {{ t('app.fix') }}
                  </button>
                  <button
                    @click="selectAndPlayTrace(Number(i))"
                    :disabled="simulationAnimationState.visible"
                    :class="[
                      'px-2 py-1 rounded text-xs font-medium transition-colors flex items-center gap-1',
                      simulationAnimationState.visible 
                        ? 'bg-slate-300 text-slate-500 cursor-not-allowed' 
                        : 'bg-red-500 hover:bg-red-600 text-white'
                    ]"
                  >
                    <span class="material-symbols-outlined text-xs">play_arrow</span>
                    {{ t('app.viewTrace') }}
                    <span v-if="simulationAnimationState.visible" class="text-[10px]">({{ t('app.active') }})</span>
                  </button>
                </div>
              </div>
              <div class="text-xs font-bold text-slate-600 mb-1">
                {{ t('app.traceVisualization.violatedSpecification') }}: {{ getTraceSpecDisplayTitle(trace) }}
              </div>
              <details v-if="trace.violatedSpecId" class="mt-1 text-[11px] text-slate-500">
                <summary class="cursor-pointer font-semibold">{{ t('app.technicalDetails') }}</summary>
                <div class="mt-1 grid gap-1 sm:grid-cols-[9rem_minmax(0,1fr)]">
                  <span class="font-medium">{{ t('app.specificationTechnicalId') }}</span>
                  <code class="break-all rounded bg-slate-50 px-2 py-1 text-[11px] text-slate-700">{{ trace.violatedSpecId }}</code>
                </div>
              </details>
              <div class="text-xs text-slate-500 mt-1">
                {{ t('app.statesCount', { count: trace.states?.length || 0 }) }}
              </div>
            </div>
          </div>
        </div>
      </div>

      
    </div>
  </div>

  <!-- Trace Animation Control Bar (Bottom) -->
  <div 
    v-if="traceAnimationState.visible && currentTrace"
    class="board-timeline-host board-timeline-host--trace"
    data-testid="trace-timeline-host"
    :style="boardShellStyle"
    role="region"
    :aria-label="t('app.traceVisualization.stateSequence')"
  >
    <div
      class="board-timeline board-timeline--trace"
      data-testid="trace-timeline"
      :data-selected-state-index="traceAnimationState.selectedStateIndex"
    >
      
      <!-- Keep the checked specification visible throughout playback. -->
      <div 
        v-if="formattedSpec"
        class="mb-3 pb-3 border-b border-slate-200"
      >
        <!-- Violated Spec -->
        <div v-if="formattedSpec" class="p-2 bg-red-50 border border-red-200 rounded-lg">
          <div class="flex items-center justify-between mb-2">
            <div class="text-xs font-semibold text-red-600 uppercase">
              {{ t('app.traceVisualization.violatedSpecification') }}
            </div>
            <button type="button" @click="closeTraceAnimation" class="text-slate-400 hover:text-slate-600" :aria-label="t('app.close')">
              <span class="material-symbols-outlined" aria-hidden="true">close</span>
            </button>
          </div>
          <div class="text-xs text-slate-800">{{ formattedSpec }}</div>
          <details v-if="currentTrace.checkedExpression" class="mt-2 text-[11px] text-slate-600">
            <summary class="cursor-pointer font-semibold text-red-700">{{ t('app.technicalDetails') }}</summary>
            <div class="mt-1 text-[10px] font-bold uppercase text-slate-500">{{ t('app.actualCheckedExpression') }}</div>
            <code class="mt-1 block max-h-20 overflow-auto break-all rounded bg-white px-2 py-1 text-[10px] text-slate-700">
              {{ currentTrace.checkedExpression }}
            </code>
          </details>
        </div>
      </div>

      <!-- Timeline -->
      <div class="mb-3">
        <div class="flex items-center justify-between mb-3">
          <div class="flex items-center gap-2 flex-wrap">
            <div class="min-w-0">
              <div class="flex items-center gap-1">
                <div class="text-sm font-bold text-slate-700">
                  {{ activeFuzzingFinding
                    ? t('app.fuzzFindingReplay')
                    : t('app.traceVisualization.counterexampleTracePlayback') }}
                </div>
                <InfoTooltip
                  :text="counterexampleTraceHelpText"
                  :label="t('app.showHelpFor', {
                    topic: activeFuzzingFinding
                      ? t('app.fuzzFindingReplay')
                      : t('app.traceVisualization.counterexampleTracePlayback')
                  })"
                  placement="right"
                  tone="danger"
                  test-id="counterexample-trace-help"
                />
              </div>
            </div>
            <span class="px-2 py-0.5 bg-red-100 text-red-600 text-xs rounded-full" aria-live="polite">
              {{ traceAnimationState.selectedStateIndex + 1 }} / {{ totalStates }}
            </span>
            <span
              v-if="activeFuzzingFinding && traceAnimationState.selectedStateIndex === activeFuzzingFinding.firstViolationStep"
              class="inline-flex items-center gap-1 rounded-full bg-red-100 px-2 py-0.5 text-xs font-bold text-red-700"
              data-testid="fuzzing-timeline-first-violation"
            >
              <span class="material-symbols-outlined text-[12px]" aria-hidden="true">warning</span>
              {{ t('app.fuzzFirstViolation') }}
            </span>
            <span
              v-if="!activeFuzzingFinding && traceModelSemanticsConsistent && !activeTraceContext.isAttack"
              class="px-2 py-0.5 bg-slate-100 text-slate-600 text-xs rounded-full"
            >
              {{ t('app.traceVisualization.noAttackModelShort') }}
            </span>
            <span
              v-if="!activeFuzzingFinding && !traceModelSemanticsConsistent"
              data-testid="trace-model-semantics-warning"
              class="px-2 py-0.5 bg-amber-100 text-amber-700 text-xs font-semibold rounded-full"
            >
              {{ t('app.traceVisualization.modelSemanticsUnavailableShort') }}
            </span>
            <!-- Verification Info (from the viewed trace's own context, not the live form) -->
            <span v-if="!activeFuzzingFinding && activeTraceContext.isAttack" class="px-2 py-0.5 bg-red-500 text-white text-xs rounded-full flex items-center gap-1">
              <span class="material-symbols-outlined text-[10px]">warning</span>
              {{ t('app.traceVisualization.attack') }}
            </span>
            <span v-if="!activeFuzzingFinding && activeTraceContext.isAttack" class="px-2 py-0.5 bg-orange-100 text-orange-600 text-xs rounded-full">
              {{ t('app.traceVisualization.attackBudget') }}: {{ activeTraceContext.attackBudget }}
            </span>
            <span v-if="currentTraceCompromisedPointCount !== null" class="px-2 py-0.5 bg-red-100 text-red-700 text-xs rounded-full">
              {{ t('app.traceVisualization.runtimeCompromisedPoints') }}: {{ currentTraceCompromisedPointCount }}
            </span>
            <span v-if="!activeFuzzingFinding && activeTraceContext.enablePrivacy && traceModelSemanticsConsistent" class="px-2 py-0.5 bg-fuchsia-100 text-fuchsia-700 text-xs rounded-full">
              {{ t('app.traceVisualization.privacyPropagationEnabled') }}
            </span>
            <span v-if="!activeFuzzingFinding && !activeTraceContext.enablePrivacy && traceModelSemanticsConsistent" class="px-2 py-0.5 bg-slate-100 text-slate-600 text-xs rounded-full">
              {{ t('app.traceVisualization.privacyPropagationNotModeled') }}
            </span>
          </div>
          <div class="flex items-center gap-2">
            <button
              type="button"
              @click="toggleTraceAnimation"
              data-testid="trace-timeline-play"
              :disabled="totalStates <= 1"
              class="px-3 py-1.5 rounded-lg text-xs font-medium transition-colors flex items-center gap-1 disabled:cursor-not-allowed"
              :aria-label="traceAnimationState.isPlaying ? t('app.traceVisualization.pause') : t('app.traceVisualization.play')"
              :class="traceAnimationState.isPlaying 
                ? 'bg-red-500 text-white' 
                : totalStates <= 1
                  ? 'bg-slate-100 text-slate-400'
                  : 'bg-slate-100 text-slate-700 hover:bg-slate-200'"
            >
              <span class="material-symbols-outlined text-sm" aria-hidden="true">{{ traceAnimationState.isPlaying ? 'pause' : 'play_arrow' }}</span>
              {{ traceAnimationState.isPlaying ? t('app.traceVisualization.pause') : t('app.traceVisualization.play') }}
            </button>
            <button
              type="button"
              @click="closeTraceAnimation"
              data-testid="trace-timeline-close"
              class="p-1.5 hover:bg-slate-100 rounded-lg transition-colors"
              :title="t('app.close')"
              :aria-label="t('app.close')"
            >
              <span class="material-symbols-outlined text-slate-500" aria-hidden="true">close</span>
            </button>
          </div>
        </div>

        <div
          v-if="!activeFuzzingFinding && currentTrace.modelComplete === false"
          class="mb-3 rounded-lg border border-amber-300 bg-amber-50 px-3 py-2 text-[11px] font-medium leading-4 text-amber-800"
          data-testid="trace-timeline-incomplete-warning"
        >
          {{ t('app.traceVisualization.verificationModelIncompletePlayback', {
            rules: currentTrace.disabledRuleCount || 0,
            specs: currentTrace.skippedSpecCount || 0
          }) }}
        </div>

        <div
          v-if="activeFuzzingFinding"
          class="mb-3 rounded-lg border border-indigo-200 bg-indigo-50 px-3 py-2 text-[11px] font-medium leading-4 text-indigo-900"
          data-testid="fuzzing-playback-notice"
        >
          {{ t('app.fuzzFindingReplayHint') }}
        </div>

        <details class="group mb-2" data-testid="trace-timeline-state-details">
          <summary class="flex cursor-pointer list-none items-center justify-between gap-3 rounded-lg border border-slate-200 px-2 py-1.5 text-[11px] font-semibold text-slate-600 hover:bg-slate-100">
            <span class="inline-flex items-center gap-1.5">
              <span class="material-symbols-outlined text-base" aria-hidden="true">tune</span>
              {{ t('app.traceVisualization.stateDetails') }}
            </span>
            <span class="material-symbols-outlined text-base transition-transform group-open:rotate-180" aria-hidden="true">expand_more</span>
          </summary>
          <div class="mt-1.5">
        <div class="mb-3 rounded-lg border border-sky-200 bg-sky-50 px-3 py-2 text-[11px] font-medium leading-4 text-sky-800" data-testid="trace-timeline-snapshot-notice">
          {{ t('app.traceVisualization.playbackSnapshotReadOnly') }}
        </div>

        <div class="mb-3 rounded-lg border border-slate-200 bg-white/70 px-3 py-2" data-testid="trace-timeline-triggered-rules">
          <div class="text-[10px] font-bold uppercase text-slate-500">
            {{ traceAnimationState.selectedStateIndex === 0
              ? t('app.traceVisualization.initialModelState')
              : t('app.traceVisualization.rulesAppliedToReachState') }}
          </div>
          <div v-if="traceAnimationState.selectedStateIndex > 0 && currentTraceTriggeredRules.length > 0" class="mt-1.5 flex flex-wrap gap-1.5">
            <span
              v-for="(rule, index) in currentTraceTriggeredRules"
              :key="rule.ruleId || `${rule.ruleLabel}-${index}`"
              class="inline-flex max-w-full items-center gap-1 rounded-full border px-2 py-1 text-[10px] font-semibold"
              :class="traceTriggeredRuleExistsOnBoard(rule)
                ? 'border-emerald-200 bg-emerald-50 text-emerald-700'
                : 'border-amber-300 bg-amber-50 text-amber-800'"
              :title="traceTriggeredRuleExistsOnBoard(rule) ? undefined : t('app.traceVisualization.historicalRuleNotOnCurrentBoard')"
            >
              <span class="max-w-[14rem] truncate">{{ traceTriggeredRuleLabel(rule, Number(index)) }}</span>
              <span v-if="!traceTriggeredRuleExistsOnBoard(rule)" class="material-symbols-outlined text-[12px]" aria-hidden="true">history</span>
            </span>
          </div>
          <div v-else-if="traceAnimationState.selectedStateIndex > 0" class="mt-1 text-[11px] text-slate-500">
            {{ t('app.traceVisualization.noRulesApplied') }}
          </div>
        </div>

        <div
          v-if="currentTraceCompromisedAutomationLinks.length > 0"
          class="mb-3 rounded-lg border border-red-200 bg-red-50 px-3 py-2"
          data-testid="trace-timeline-compromised-links"
        >
          <div class="text-[10px] font-bold uppercase text-red-700">
            {{ t('app.traceVisualization.compromisedAutomationLinks') }}
          </div>
          <div class="mt-1.5 flex flex-wrap gap-1.5">
            <span
              v-for="(rule, index) in currentTraceCompromisedAutomationLinks"
              :key="rule.ruleId || `${rule.ruleLabel}-${index}`"
              class="inline-flex max-w-full items-center gap-1 rounded-full border border-red-200 bg-white px-2 py-1 text-[10px] font-semibold text-red-700"
              :title="traceTriggeredRuleExistsOnBoard(rule) ? t('app.traceVisualization.compromisedAutomationLinkHint') : t('app.traceVisualization.historicalRuleNotOnCurrentBoard')"
            >
              <span class="material-symbols-outlined text-[12px]" aria-hidden="true">link_off</span>
              <span class="max-w-[14rem] truncate">{{ traceTriggeredRuleLabel(rule, Number(index)) }}</span>
              <span v-if="!traceTriggeredRuleExistsOnBoard(rule)" class="material-symbols-outlined text-[12px]" aria-hidden="true">history</span>
            </span>
          </div>
        </div>

        <div class="mb-3 grid gap-2 rounded-lg border border-slate-200 bg-white/70 p-2 md:grid-cols-[minmax(0,1fr)_auto]">
          <label class="flex min-w-0 items-center gap-2 text-[11px] font-bold text-slate-600">
            <span class="whitespace-nowrap">{{ t('app.traceVisualization.jumpToState') }}</span>
            <input
              v-model.number="selectedTraceStateRangeIndex"
              data-testid="trace-timeline-range"
              type="range"
              :min="0"
              :max="Math.max(totalStates - 1, 0)"
              :disabled="totalStates <= 1"
              class="min-w-0 flex-1 accent-red-500"
            >
          </label>
          <input
            v-model.number="selectedTraceStateNumber"
            data-testid="trace-timeline-step-input"
            type="number"
            :min="1"
            :max="Math.max(totalStates, 1)"
            :disabled="totalStates <= 0"
            class="h-8 w-20 rounded-lg border border-slate-200 bg-white px-2 text-center text-xs font-bold text-slate-700 outline-none focus:border-red-500 focus:ring-2 focus:ring-red-200"
            :aria-label="t('app.traceVisualization.jumpToState')"
          >
        </div>

        <div v-if="currentTraceDevices.length > 0" class="mb-3 flex flex-wrap gap-1.5" data-testid="trace-timeline-devices">
          <span class="mr-1 inline-flex items-center gap-1 text-[10px] font-bold uppercase text-slate-500">
            <span class="material-symbols-outlined text-[13px]" aria-hidden="true">devices</span>
            {{ t('app.traceVisualization.devicesInCurrentState') }}
          </span>
          <span
            v-for="device in currentTraceDevices"
            :key="device.deviceId"
            class="inline-flex max-w-full flex-wrap items-center gap-1 rounded border px-2 py-1 text-[10px] font-semibold"
            :class="!traceDeviceExistsOnBoard(device)
              ? 'border-amber-300 bg-amber-50 text-amber-800'
              : traceDeviceChanged(device)
                ? 'border-red-300 bg-red-50 text-red-800'
                : 'border-slate-200 bg-slate-50 text-slate-700'"
            :title="traceDeviceExistsOnBoard(device) ? undefined : t('app.traceVisualization.historicalDeviceNotOnCurrentBoard')"
          >
            <span class="font-bold">{{ device.deviceLabel || device.deviceId }}</span>
            <span class="max-w-[20rem] break-words font-mono font-normal">{{ traceDeviceSummary(device) }}</span>
            <span v-if="traceDeviceChanged(device)" class="rounded bg-red-200 px-1 text-[9px] text-red-800">
              {{ t('app.traceVisualization.changed') }}
            </span>
            <span v-if="isPlaybackDeviceAttacked(device)" class="rounded bg-red-100 px-1 text-[9px] text-red-700">
              {{ t('app.traceVisualization.attacked') }}
            </span>
            <span
              v-if="traceDeviceSecurityFacts(device).untrustedLabels.length > 0"
              class="rounded bg-amber-100 px-1 text-[9px] text-amber-800"
              :title="t('app.traceVisualization.untrustedLabelDetails', { labels: traceDeviceSecurityFacts(device).untrustedLabels.join(', ') })"
            >
              {{ t('app.traceVisualization.includesUntrustedSource') }}
            </span>
            <span
              v-if="traceDeviceSecurityFacts(device).privateLabels.length > 0"
              class="rounded bg-fuchsia-100 px-1 text-[9px] text-fuchsia-800"
              :title="t('app.traceVisualization.privateLabelDetails', { labels: traceDeviceSecurityFacts(device).privateLabels.join(', ') })"
            >
              {{ t('app.traceVisualization.includesPrivateData') }}
            </span>
            <span v-if="!traceDeviceExistsOnBoard(device)" class="material-symbols-outlined text-[12px]" aria-hidden="true">history</span>
          </span>
        </div>

        <div v-if="currentTraceEnvironmentVariables.length > 0" class="mb-3 flex flex-wrap gap-1.5" data-testid="trace-timeline-env">
          <span class="mr-1 inline-flex items-center gap-1 text-[10px] font-bold uppercase tracking-wide text-slate-500">
            <span class="material-symbols-outlined text-[13px]" aria-hidden="true">terrain</span>
            {{ t('app.traceVisualization.environmentVariables') }}
          </span>
          <span
            v-for="envVar in currentTraceEnvironmentVariables"
            :key="envVar.name"
            class="inline-flex max-w-full items-center gap-1 rounded-full border px-2 py-1 text-[10px] font-bold"
            :class="traceEnvironmentVariableChanged(envVar.name, envVar.value)
              ? 'border-amber-300 bg-amber-50 text-amber-700'
              : 'border-slate-200 bg-slate-50 text-slate-600'"
            :title="traceEnvironmentVariableTitle(envVar.name, envVar.value)"
          >
            <span class="max-w-[7rem] truncate">{{ envVar.name }}</span>
            <span class="font-mono">{{ envVar.value }}</span>
            <span v-if="traceEnvironmentVariableChanged(envVar.name, envVar.value)" class="rounded-full bg-amber-200 px-1 text-[9px] text-amber-800">
              {{ t('app.traceVisualization.changed') }}
            </span>
          </span>
        </div>
          </div>
        </details>
        
        <!-- Timeline bar with horizontal scroll support -->
        <div class="overflow-x-auto scrollbar-thin py-2">
          <div 
            class="relative h-14"
            data-testid="trace-timeline-track"
            :style="{ width: (currentTrace?.states?.length || 0) > 15 ? 'max-content' : '100%', minWidth: (currentTrace?.states?.length || 0) > 15 ? `${Math.max((currentTrace?.states?.length || 0) * 38, 500)}px` : '100%' }"
            @pointerdown="selectTraceStateFromTimelinePointer"
          >
            <!-- Progress line background -->
            <div class="absolute top-1/2 left-2 right-2 h-3 bg-slate-200 rounded -translate-y-1/2"></div>
            <!-- Red progress bar - from start to current node -->
            <div 
              v-if="traceAnimationState.selectedStateIndex > 0 && totalStates > 1"
              class="absolute top-1/2 h-3 bg-red-500 rounded transition-all duration-300 -translate-y-1/2"
              :style="{ 
                left: '8px',
                width: `calc((100% - 16px) * ${traceAnimationState.selectedStateIndex / (totalStates - 1)})`
              }"
            ></div>
            
            <!-- State nodes -->
            <div class="absolute top-1/2 left-2 right-2 flex justify-between items-center -translate-y-1/2">
              <button
                v-for="(_, index) in currentTrace.states || []"
                :key="index"
                type="button"
                @click="goToState(Number(index))"
                @keydown="handleTraceStateKeydown($event, Number(index))"
                :tabindex="Number(index) === traceAnimationState.selectedStateIndex ? 0 : -1"
                :aria-label="getTraceStateAriaLabel(Number(index))"
                :aria-current="Number(index) === traceAnimationState.selectedStateIndex ? 'step' : undefined"
                :data-testid="`trace-timeline-state-${Number(index)}`"
                class="w-7 h-7 rounded-full border-3 transition-all flex items-center justify-center relative z-10 flex-shrink-0 focus:outline-none focus:ring-2 focus:ring-red-500 focus:ring-offset-2"
                :class="[
                  Number(index) === traceAnimationState.selectedStateIndex
                    ? 'bg-red-500 border-red-500 scale-125 shadow-lg'
                    : Number(index) < traceAnimationState.selectedStateIndex
                      ? 'bg-red-200 border-red-300'
                      : 'bg-white border-slate-300 hover:border-red-300',
                  activeFuzzingFinding?.firstViolationStep === Number(index)
                    ? 'ring-2 ring-amber-400 ring-offset-2'
                    : ''
                ]"
              >
                <span
                  v-if="activeFuzzingFinding?.firstViolationStep === Number(index)"
                  class="absolute -top-4 text-[10px] font-black text-red-700"
                  aria-hidden="true"
                >!</span>
                <span 
                  v-if="Number(index) === traceAnimationState.selectedStateIndex" 
                  class="text-white text-[8px] font-bold"
                >★</span>
                <span v-else class="text-slate-500 text-[6px] font-medium">{{ Number(index) + 1 }}</span>
              </button>
            </div>
          </div>
        </div>
      </div>
    </div>
  </div>

  <!-- Simulation Timeline 组件 -->
  <SimulationTimeline
    v-if="simulationAnimationState.visible"
    :visible="simulationAnimationState.visible"
    :states="savedSimulationStates"
    :actual-steps="lastSimulationResult?.steps"
    :requested-steps="lastSimulationResult?.requestedSteps"
    :model-complete="lastSimulationResult?.modelComplete"
    :disabled-rule-count="lastSimulationResult?.disabledRuleCount"
    :is-attack="lastSimulationResult?.isAttack"
    :attack-budget="lastSimulationResult?.attackBudget"
    :enable-privacy="lastSimulationResult?.enablePrivacy"
    :model-semantics="lastSimulationResult?.modelSemantics"
    :model-snapshot="lastSimulationResult?.modelSnapshot"
    :board-comparison="simulationBoardComparison"
    :current-rule-ids="currentBoardRuleIds"
    :current-device-ids="currentBoardDeviceIds"
    :style="boardShellStyle"
    @update:visible="handleSimulationTimelineClose"
    @highlight-state="handleHighlightTrace"
    @open-run-details="openSimulationRunDetails"
  />

  <!-- Fix Result Dialog 组件 -->
  <FixResultDialog
    v-if="showFixDialog"
    :visible="showFixDialog"
    :trace-id="fixTraceId || 0"
    :violated-spec-id="fixViolatedSpecId"
    @update:visible="showFixDialog = $event"
    @applied="handleFixApplied"
    @outcome-uncertain="handleFixOutcomeUncertain"
  />
</template>

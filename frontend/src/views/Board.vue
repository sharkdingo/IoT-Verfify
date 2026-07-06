<script setup lang="ts">
/* =================================================================================
 * 1. Imports & Setup
 * ================================================================================= */
import {ref, reactive, computed, nextTick, onMounted, onBeforeUnmount, watch} from 'vue'
import { useRouter } from 'vue-router'
import { useI18n } from 'vue-i18n'
import { useChatStore } from '@/stores/chat'
import { useAuth } from '@/stores/auth'
import { authApi } from '@/api/auth'
import LogoutConfirmDialog from '@/components/LogoutConfirmDialog.vue'
import { ElMessage, ElMessageBox } from 'element-plus'
// Icons

// Types
import type {DeviceDialogMeta, DeviceTemplate} from '../types/device'
import type { BoardLayoutDto, CanvasPan } from '../types/canvas'
import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { RuleForm } from '../types/rule'
import type { SpecCondition, Specification } from '../types/spec'
import type { SpecResult, Trace, VerificationResult, VerificationTask, VerificationTaskSummary } from '@/types/verify'
import type { SimulationTaskSummary, SimulationTraceSummary } from '@/types/simulation'
// Panel types removed

// Utils
import {getNodeIcon} from '../utils/device'
import { getUniqueLabel } from '../utils/canvas/nodeCreate'
import {
  isSpecRelatedToNode,
  removeSpecsForNode
} from '../utils/spec'
import { assertRuleHasTrigger, getLinkPoints } from '../utils/rule'
import { cacheManifestForNode, getCachedManifestForNode, hydrateManifestCacheForNodes } from '@/utils/templateCache'
import { canOpenTracePlayback, deriveTraceContext } from '@/utils/traceView'
import { buildSimulationRequestPayload, buildVerificationRequestPayload } from '@/utils/modelRequest'

// Config
import { defaultSpecTemplates } from '../assets/config/specTemplates'

// API
import boardApi from '@/api/board'
import simulationApi from '@/api/simulation'
import rulesApi, { type RuleRecommendation } from '@/api/rules'

// Components
import DeviceDialog from '../components/DeviceDialog.vue'
import CanvasBoard from '../components/CanvasBoard.vue'
import ControlCenter from '../components/ControlCenter.vue'
import SystemInspector from '../components/SystemInspector.vue'
import RuleBuilderDialog from '../components/RuleBuilderDialog.vue'
import SimulationTimeline from '../components/SimulationTimeline.vue'
import FixResultDialog from '../components/FixResultDialog.vue'
import TraceHistoryPanel from '../components/TraceHistoryPanel.vue'
import LanguageToggle from '@/components/common/LanguageToggle.vue'
import ThemeToggle from '@/components/common/ThemeToggle.vue'
import { useModalAccessibility } from '@/composables/useModalAccessibility'

const { t } = useI18n()
const router = useRouter()
const { toggleChat } = useChatStore()
const { logout } = useAuth()

const showLogoutDialog = ref(false)

const handleLogout = () => {
  showLogoutDialog.value = true
}

const handleLogoutConfirm = async () => {
  // 调用后端 logout 把 JWT 加入黑名单；失败也要清本地登录态（与 Header.vue 保持一致）。
  try {
    await authApi.logout()
  } catch {
    // API 失败不影响本地登出
  } finally {
    logout()
    showLogoutDialog.value = false
    router.push('/login')
  }
}

const handleLogoutCancel = () => {
  showLogoutDialog.value = false
}

/* =================================================================================
 * 2. Constants & Configuration
 * ================================================================================= */

// Panel constants removed

const NODE_GRID_COLS = 4
const NODE_SPACING_X = 160
const NODE_SPACING_Y = 120

const MIN_ZOOM = 0.4
const MAX_ZOOM = 2
const ZOOM_STEP = 0.1
const LAYOUT_SAVE_DEBOUNCE_MS = 700
const DEFAULT_CONTROL_PANEL_WIDTH = 320
const DEFAULT_INSPECTOR_PANEL_WIDTH = 320

const BASE_NODE_WIDTH = 160
const BASE_FONT_SIZE = 16
const ASYNC_TASK_POLL_INTERVAL_MS = 1000
const ASYNC_TASK_MAX_POLLS = 600
const TASK_INBOX_REFRESH_INTERVAL_MS = 5000
const pollingAborted = ref(false)

class PollingAbortedError extends Error {
  constructor() {
    super('Polling aborted')
    this.name = 'PollingAbortedError'
  }
}

const throwIfPollingAborted = () => {
  if (pollingAborted.value) {
    throw new PollingAbortedError()
  }
}

const isPollingAbortedError = (error: unknown): boolean =>
  error instanceof PollingAbortedError

const waitForNextPoll = async () => {
  await new Promise(resolve => setTimeout(resolve, ASYNC_TASK_POLL_INTERVAL_MS))
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

type ControlCenterSection = 'devices' | 'templates' | 'rules' | 'specs'
type InspectorSection = 'devices' | 'rules' | 'specs'

const isNarrowViewport = () =>
  typeof window !== 'undefined' && window.innerWidth < 768

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
    activeSection: 'devices' as ControlCenterSection
  },
  inspector: {
    collapsed: isNarrowViewport(),
    width: DEFAULT_INSPECTOR_PANEL_WIDTH,
    activeSection: 'devices' as InspectorSection
  }
})

const layoutHydrated = ref(false)
let layoutSaveErrorShown = false

const boardShellStyle = computed(() => ({
  '--board-control-width': `${boardPanels.control.collapsed ? 64 : boardPanels.control.width}px`,
  '--board-inspector-width': `${boardPanels.inspector.collapsed ? 48 : boardPanels.inspector.width}px`
}))

const applyViewportPanelConstraints = () => {
  if (!isNarrowViewport()) return
  boardPanels.control.collapsed = true
  boardPanels.inspector.collapsed = true
}

// --- Core Data State ---
const deviceTemplates = ref<DeviceTemplate[]>([])
const nodes = ref<DeviceNode[]>([])
const edges = ref<DeviceEdge[]>([])
const internalVariableEdges = ref<DeviceEdge[]>([])  // 内部变量连线
const rules = ref<RuleForm[]>([])  // 独立存储规则列表

// 合并所有连线（规则连线 + 内部变量连线）
const allEdges = computed(() => {
  return [...edges.value, ...internalVariableEdges.value]
})
const specifications = ref<Specification[]>([])

const resolveNodeRef = (refValue?: string | null): DeviceNode | undefined => {
  if (!refValue) return undefined
  return nodes.value.find(n => n.label === refValue || n.id === refValue)
}

const resolveNodeLabel = (refValue?: string | null): string => {
  return resolveNodeRef(refValue)?.label || refValue || ''
}

const isNodeReference = (refValue: string | undefined, node: DeviceNode): boolean => {
  return !!refValue && (refValue === node.id || refValue === node.label)
}

const assertRulesHaveTriggers = (candidateRules: RuleForm[]): boolean => {
  try {
    candidateRules.forEach((rule, index) => assertRuleHasTrigger(rule, index))
    return true
  } catch (error: any) {
    ElMessage.warning({ message: error.message || t('app.ruleTriggerSourceRequired'), type: 'warning' })
    return false
  }
}

const countLogMarker = (logs: string[] | undefined, marker: string): number => {
  return (logs || []).filter(log => String(log).includes(marker)).length
}

const getGenerationWarningCounts = (result: any) => {
  const logs = result?.checkLogs || []
  const disabledRuleCount = Number(result?.disabledRuleCount ?? countLogMarker(logs, '[rule-disabled]') ?? 0)
  const skippedSpecCount = Number(result?.skippedSpecCount ?? countLogMarker(logs, '[spec-skipped]') ?? 0)
  return {
    disabledRuleCount,
    skippedSpecCount,
    total: disabledRuleCount + skippedSpecCount
  }
}

const extractApiErrorMessage = (error: any, fallback: string): string => {
  return error?.response?.data?.message || error?.message || fallback
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

const buildVerificationResultFromTask = (task: VerificationTask, traces: Trace[] = []): VerificationResult => ({
  safe: !!task.isSafe,
  traces,
  specResults: normalizeSpecResults(task.specResults),
  checkLogs: task.checkLogs || [],
  nusmvOutput: task.nusmvOutput || '',
  disabledRuleCount: task.disabledRuleCount,
  skippedSpecCount: task.skippedSpecCount
})

const normalizeSpecResult = (value: unknown, index: number): SpecResult => {
  const candidate = value as Partial<SpecResult> | undefined
  return {
    specId: candidate?.specId || `spec-${index + 1}`,
    passed: !!candidate?.passed,
    expression: candidate?.expression || ''
  }
}

const normalizeSpecResults = (results?: unknown[]): SpecResult[] =>
  (results || []).map((result, index) => normalizeSpecResult(result, index))

const countVerificationFailures = (result: any): number => {
  const failedSpecs = normalizeSpecResults(result?.specResults).filter(specResult => !specResult.passed).length
  const traceCount = result?.traces?.length || 0
  return Math.max(failedSpecs, traceCount)
}

const getVerificationFailureMessage = (result: any): string => {
  const failureCount = countVerificationFailures(result)
  return failureCount > 0
    ? t('app.verificationFailedWithViolations', { count: failureCount })
    : t('app.verificationFailedNoSpecResults')
}

const notifyVerificationOutcome = (result: any) => {
  const counts = getGenerationWarningCounts(result)
  if (counts.total > 0) {
    const outcome = result?.safe
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

  if (result?.safe) {
    ElMessage.success({ message: t('app.verificationPassedSystemSafe'), type: 'success' })
  } else {
    ElMessage.warning({ message: getVerificationFailureMessage(result), type: 'warning' })
  }
}

const draggingTplName = ref<string | null>(null)

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
  }
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

/* =================================================================================
 * 5. Canvas Interaction (Zoom & Pan)
 * ================================================================================= */

const onBoardWheel = (e: WheelEvent) => {
  if (e.ctrlKey) {
    if (e.deltaY > 0) {
      canvasZoom.value = Math.max(MIN_ZOOM, canvasZoom.value - ZOOM_STEP)
    } else {
      canvasZoom.value = Math.min(MAX_ZOOM, canvasZoom.value + ZOOM_STEP)
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
        canvasZoom.value = Math.min(MAX_ZOOM, canvasZoom.value + ZOOM_STEP)
      } else if (e.key === '-') {
        canvasZoom.value = Math.max(MIN_ZOOM, canvasZoom.value - ZOOM_STEP)
      } else if (e.key === '0') {
        canvasZoom.value = 1
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
    x: panOrigin.x + dx / canvasZoom.value,
    y: panOrigin.y + dy / canvasZoom.value
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


const createDeviceInstanceAt = async (tpl: DeviceTemplate, pos: { x: number; y: number }) => {
  // 快照，保存失败时回滚本次新增的全部节点/连线，避免本地与后端分叉。
  const idsBefore = new Set(nodes.value.map(n => n.id))
  const edgeIdsBefore = new Set(internalVariableEdges.value.map(edge => edge.id))
  const uniqueLabel = getUniqueLabel(tpl.manifest.Name, nodes.value)
  const node: DeviceNode = {
    id: uniqueLabel,
    templateName: tpl.manifest.Name,
    label: uniqueLabel,
    position: pos,
    state: tpl.manifest.InitState || 'Working',
    width: 110,
    height: 90
  }
  nodes.value.push(node)

  // 如果有内部变量，创建变量节点和连线
  const internalVariables = tpl.manifest.InternalVariables || []
  if (internalVariables.length > 0) {
    // 变量节点从主设备右侧开始排列，使用圆形设计
    const variableStartX = pos.x + 160
    const variableSpacingY = 70  // 变量节点垂直间距

    internalVariables.forEach((variable, index) => {
      const variableId = `${uniqueLabel}_${variable.Name}`
      const variableNode: DeviceNode = {
        id: variableId,
        templateName: `variable_${variable.Name}`,  // 使用variable_前缀标识为变量节点
        label: variable.Name,
        position: {
          x: variableStartX,
          y: pos.y + index * variableSpacingY
        },
        state: 'variable',
        width: 60,   // 圆形宽度
        height: 60   // 圆形高度
      }
      nodes.value.push(variableNode)

      // 创建从主设备到变量节点的连线
      const edgeId = `edge_${uniqueLabel}_to_${variableId}`
      const edge: DeviceEdge = {
        id: edgeId,
        from: uniqueLabel,
        to: variableId,
        fromLabel: uniqueLabel,
        toLabel: variable.Name,
        fromPos: { x: pos.x + 110, y: pos.y + 45 },  // 主设备右侧中间
        toPos: { x: variableStartX, y: pos.y + index * variableSpacingY + 30 },  // 变量节点左侧中间
        itemType: 'variable',
        relation: 'contains',
        value: variable.Name
      }
      internalVariableEdges.value.push(edge)
    })
  }

  try {
    await saveNodesToServer()
  } catch (e) {
    // 回滚本次新增的节点与内部变量连线（saveNodesToServer 已弹出失败提示），再向上抛出让调用方感知。
    nodes.value = nodes.value.filter(n => idsBefore.has(n.id))
    internalVariableEdges.value = internalVariableEdges.value.filter(edge => edgeIdsBefore.has(edge.id))
    throw e
  }
}

/**
 * 根据已加载的节点和设备模板，重新生成内部变量节点和连线
 * 用于从服务器加载画布后恢复内部变量连接
 */
const regenerateInternalVariableEdges = () => {
  // 清空现有的内部变量连线
  internalVariableEdges.value = []

  // 找出所有变量节点（templateName 以 variable_ 开头）
  const variableNodes = nodes.value.filter(n => n.templateName.startsWith('variable_'))

  // 为每个变量节点创建连线
  variableNodes.forEach(varNode => {
    // 变量节点 ID 格式是 `${deviceId}_${variableName}`；deviceId 自身也可能包含下划线。
    const deviceNode = nodes.value
      .filter(n => !n.templateName?.startsWith('variable_'))
      .sort((a, b) => b.id.length - a.id.length)
      .find(n => varNode.id.startsWith(`${n.id}_`))
    if (!deviceNode) return

    const variableName = varNode.id.slice(deviceNode.id.length + 1)

    // 查找设备模板以确认这是内部变量
    const template = deviceTemplates.value.find(t => t.manifest.Name === deviceNode.templateName)
    const internalVar = template?.manifest.InternalVariables?.find(v => v.Name === variableName)
    if (!internalVar) return

    // 创建连线
    const edgeId = `edge_${deviceNode.id}_to_${varNode.id}`
    const edge: DeviceEdge = {
      id: edgeId,
      from: deviceNode.id,
      to: varNode.id,
      fromLabel: deviceNode.label,
      toLabel: variableName,
      fromPos: { x: deviceNode.position.x + 110, y: deviceNode.position.y + 45 },
      toPos: { x: varNode.position.x, y: varNode.position.y + 30 },
      itemType: 'variable',
      relation: 'contains',
      value: variableName
    }
    internalVariableEdges.value.push(edge)
  })
}



const onCanvasDragOver = (e: DragEvent) => {
  if (e.dataTransfer) e.dataTransfer.dropEffect = 'copy'
}

const onCanvasDrop = async (e: DragEvent) => {
  if (!draggingTplName.value) return
  const tpl = deviceTemplates.value.find(d => d.manifest.Name === draggingTplName.value)
  if (!tpl) return

  const rect = (e.currentTarget as HTMLElement).getBoundingClientRect()
  const Sx = e.clientX - rect.left
  const Sy = e.clientY - rect.top

  const x = (Sx - canvasPan.value.x) / canvasZoom.value
  const y = (Sy - canvasPan.value.y) / canvasZoom.value

  // createDeviceInstanceAt 失败会回滚并抛错，这里吞掉（失败提示已弹出），确保 draggingTplName 被清理。
  try {
    await createDeviceInstanceAt(tpl, { x, y })
  } catch { /* 已回滚并提示 */ }
  draggingTplName.value = null
}

// 处理 AI 推荐的设备添加
const handleAISuggestionAddDevice = async (event: Event) => {
  const customEvent = event as CustomEvent
  const { templateName } = customEvent.detail || {}
  
  if (!templateName) {
    console.warn('AI Suggestion: No template name provided')
    return
  }

  // 查找模板
  const tpl = deviceTemplates.value.find(d => 
    d.manifest.Name.toLowerCase() === templateName.toLowerCase()
  )

  if (!tpl) {
    console.warn(`AI Suggestion: Template not found: ${templateName}`)
    return
  }

  // 计算新设备的位置（画布中心附近）
  const canvasEl = document.querySelector('.canvas-container')
  if (!canvasEl) return
  
  const rect = canvasEl.getBoundingClientRect()
  const centerX = rect.width / 2
  const centerY = rect.height / 2
  
  const x = (centerX - canvasPan.value.x) / canvasZoom.value
  const y = (centerY - canvasPan.value.y) / canvasZoom.value

  // 创建设备实例（失败会回滚并抛错，失败提示已弹出）
  try {
    await createDeviceInstanceAt(tpl, { x, y })
  } catch { /* 已回滚并提示 */ }
}

const handleNodeMovedOrResized = async () => {
  // 更新内部变量连线的位置
  updateInternalVariableEdgePositions()

  // 保存失败提示已由 saveNodesToServer 弹出；位置类更新失败不做回滚（重开会重新拉取），只吞掉未处理拒绝。
  try {
    await saveNodesToServer()
  } catch { /* 已提示 */ }
  // edges 由 rules 动态生成，不需要单独保存
}

/**
 * 更新内部变量连线的位置（当节点移动时调用）
 */
const updateInternalVariableEdgePositions = () => {
  internalVariableEdges.value.forEach(edge => {
    const fromNode = nodes.value.find(n => n.id === edge.from)
    const toNode = nodes.value.find(n => n.id === edge.to)

    if (fromNode && toNode) {
      edge.fromPos = { x: fromNode.position.x + fromNode.width, y: fromNode.position.y + fromNode.height / 2 }
      edge.toPos = { x: toNode.position.x, y: toNode.position.y + toNode.height / 2 }
    }
  })
}

const handleAddRule = async (payload: RuleForm) => {
  const { sources, toId, toApi } = payload
  if (!sources || !sources.length || !toId || !toApi) {
    ElMessage.warning(t('app.fillAllRuleFields'))
    return
  }
  if (!assertRulesHaveTriggers([payload])) {
    return
  }

  const toNode = resolveNodeRef(toId)
  if (!toNode) return

  // 为新规则生成 ID
  const ruleId = 'rule_' + Date.now()
  const newRule: RuleForm = {
    ...payload,
    id: ruleId,
    name: payload.name || `Rule ${ruleId}`
  }

  if (sources.length > 0) {
    try {
      // 只保存 rules（edges 由 rules 动态生成）
      // 将 Proxy 对象转换为普通对象后再发送
      const allRules = JSON.parse(JSON.stringify([...rules.value, newRule]))
      await boardApi.saveRules(allRules)

      // 更新前端状态
      rules.value = allRules
      // 动态生成 edges
      edges.value = generateEdgesFromRules()

      ElMessage.success(t('app.addRuleSuccess'))
    } catch (e: any) {
      console.error('saveRules error', e)
      // 如果后端返回了错误信息，显示它
      const errorMsg = e?.response?.data?.message || e?.message || t('app.saveRulesFailed')
      ElMessage.error(errorMsg)
    }
  }
}

// 应用推荐的规则
const applyRecommendation = async (rec: RuleRecommendation) => {
  try {
    // 将推荐转换为 RuleForm 格式
    const ruleId = 'rule_' + Date.now()
    
    const newRule: RuleForm = {
      id: ruleId,
      name: rec.description.substring(0, 30) + (rec.description.length > 30 ? '...' : ''),
      sources: rec.conditions?.map(c => ({
        fromId: c.deviceName,
        fromApi: c.attribute,
        relation: c.relation || '=',
        value: c.value
      })) || [],
      toId: rec.command?.deviceName || '',
      toApi: rec.command?.action || ''
    }

    // 验证必要字段
    if (!newRule.sources.length || !newRule.toId || !newRule.toApi) {
      ElMessage.warning(t('app.invalidRecommendationFormat'))
      return
    }
    if (!assertRulesHaveTriggers([newRule])) {
      return
    }

    // 保存到后端
    const allRules = JSON.parse(JSON.stringify([...rules.value, newRule]))
    await boardApi.saveRules(allRules)

    // 更新前端状态
    rules.value = allRules
    edges.value = generateEdgesFromRules()

    ElMessage.success(t('app.ruleAppliedSuccessfully'))
    
    // 不关闭面板，允许继续应用更多规则
  } catch (e: any) {
    console.error('applyRecommendation error', e)
    const errorMsg = e?.response?.data?.message || e?.message || t('app.failedToApplyRule')
    ElMessage.error(errorMsg)
  }
}


/* =================================================================================
 * 8. Context Menu & Deletion
 * ================================================================================= */

const onDeviceListClick = (deviceId: string) => {
  const node = nodes.value.find(n => n.id === deviceId)
  if (!node) return

  // Resolve template by name; if missing (e.g. template deleted), fallback to cached manifest snapshot
  const resolveTemplateForNode = (n: DeviceNode) => {
    let template = deviceTemplates.value.find(t => t.manifest?.Name === n.templateName)
    if (!template && n.templateName) {
      template = deviceTemplates.value.find(t => t.manifest?.Name?.toLowerCase() === n.templateName?.toLowerCase())
    }
    if (!template && n.templateName) {
      template = deviceTemplates.value.find(t =>
        n.templateName.toLowerCase().includes(t.manifest?.Name?.toLowerCase() || '') ||
        (t.manifest?.Name?.toLowerCase() || '').includes(n.templateName.toLowerCase())
      )
    }
    return template || null
  }

  const tpl = resolveTemplateForNode(node)
  const cachedManifest = getCachedManifestForNode(node.id)
  const manifest = tpl?.manifest || cachedManifest || null

  // If we have a manifest (from template or cache), snapshot it for future template deletion
  if (manifest) cacheManifestForNode(node.id, manifest)
  dialogMeta.nodeId = node.id
  dialogMeta.label = node.label
  dialogMeta.deviceName = manifest?.Name || tpl?.manifest?.Name || node.templateName
  dialogMeta.description = manifest?.Description || tpl?.manifest?.Description || ''
  dialogMeta.manifest = manifest
  dialogMeta.rules = edges.value.filter(e => e.from === node.id || e.to === node.id)
  dialogMeta.specs = specifications.value.filter(spec =>
    isSpecRelatedToNode(spec, node.id) || isSpecRelatedToNode(spec, node.label)
  )
  dialogVisible.value = true
}

// 右键菜单状态
const contextMenu = ref({
  visible: false,
  x: 0,
  y: 0,
  node: null as DeviceNode | null
})

const onNodeContext = (node: DeviceNode, event: MouseEvent) => {
  event.preventDefault()
  
  // 禁止内部变量节点右击操作
  if (node.templateName?.startsWith('variable_')) {
    return
  }
  
  contextMenu.value = {
    visible: true,
    x: event.clientX,
    y: event.clientY,
    node: node
  }
}

const onNodeKeyboardContext = (node: DeviceNode, position: { x: number; y: number }) => {
  if (node.templateName?.startsWith('variable_')) {
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
  onDeviceListClick(node.id)
}

const closeContextMenu = () => {
  contextMenu.value.visible = false
}

// 右键菜单操作
const renameDevice = () => {
  if (!contextMenu.value.node) return
  // 打开自定义重命名对话框
  const node = contextMenu.value.node
  renameDialogData.node = node
  renameDialogData.newName = node.label
  renameDialogVisible.value = true
  closeContextMenu()
}

const deleteDevice = () => {
  if (!contextMenu.value.node) return
  deleteCurrentNodeWithConfirm(contextMenu.value.node.id)
  closeContextMenu()
}

// 设备重命名时，把引用旧 label 的规约条件/关联设备同步为新 label。
// 返回是否有改动（用于决定是否需要保存 specs）。
const renameSpecDeviceRefs = (oldLabel: string, newLabel: string): boolean => {
  if (!oldLabel || oldLabel === newLabel) return false
  let changed = false
  const renameCond = (cond: any) => {
    if (cond.deviceId === oldLabel) { cond.deviceId = newLabel; changed = true }
    if (cond.deviceLabel === oldLabel) { cond.deviceLabel = newLabel; changed = true }
  }
  for (const spec of specifications.value) {
    ;(spec.aConditions || []).forEach(renameCond)
    ;(spec.ifConditions || []).forEach(renameCond)
    ;(spec.thenConditions || []).forEach(renameCond)
    if (spec.deviceId === oldLabel) { spec.deviceId = newLabel; changed = true }
    if (spec.deviceLabel === oldLabel) { spec.deviceLabel = newLabel; changed = true }
    ;(spec.devices || []).forEach(d => {
      if (d.deviceId === oldLabel) { d.deviceId = newLabel; changed = true }
      if (d.deviceLabel === oldLabel) { d.deviceLabel = newLabel; changed = true }
    })
  }
  return changed
}

// 设备重命名时，把引用旧 label 的规则触发源(sources.fromId)与命令目标(toId)同步为新 label。
// RuleBuilderDialog 里这两个字段绑定的就是 node.label（见 fromId/toId 的 <option :value="node.label">），
// 所以重命名后不同步会让规则指向已不存在的旧 label，后续 verify/fix 找不到当前设备。
const renameRuleDeviceRefs = (oldLabel: string, newLabel: string): boolean => {
  if (!oldLabel || oldLabel === newLabel) return false
  let changed = false
  for (const rule of rules.value) {
    ;(rule.sources || []).forEach((s: any) => {
      if (s.fromId === oldLabel) { s.fromId = newLabel; changed = true }
    })
    if (rule.toId === oldLabel) { rule.toId = newLabel; changed = true }
  }
  return changed
}

const handleRenameDevice = async (nodeId: string, newLabel: string) => {
  const exists = nodes.value.some(n => n.label === newLabel && n.id !== nodeId)
  if (exists) {
    ElMessage.error(t('app.nameExists'))
    return
  }

  const node = nodes.value.find(n => n.id === nodeId)
  if (node) {
    // 快照旧值，保存失败时回滚，避免本地已改名但后端未改的分叉，也避免误报成功。
    const previousLabel = node.label
    // 同步更新引用该设备的规约条件与规则引用（都存的是旧 label）。
    const specsSnapshot = JSON.parse(JSON.stringify(specifications.value))
    const rulesSnapshot = JSON.parse(JSON.stringify(rules.value))
    const specsChanged = renameSpecDeviceRefs(previousLabel, newLabel)
    const rulesChanged = renameRuleDeviceRefs(previousLabel, newLabel)

    node.label = newLabel
    try {
      // 原子保存节点+规则+规约（后端单事务）：避免「node 已改名但 rule/spec 引用未更新」的部分持久化。
      const nodesToSave = JSON.parse(JSON.stringify(nodes.value))
      const specsToSave = specsChanged ? JSON.parse(JSON.stringify(specifications.value)) : undefined
      const rulesToSave = rulesChanged ? JSON.parse(JSON.stringify(rules.value)) : undefined
      await boardApi.saveBoardBatch({ nodes: nodesToSave, rules: rulesToSave, specs: specsToSave })
      ElMessage.success(t('app.renameSuccess'))
    } catch {
      // 单事务保证未落库，回滚本地 node label / rules / specs 即完全一致。
      node.label = previousLabel
      if (specsChanged) {
        specifications.value = specsSnapshot
      }
      if (rulesChanged) {
        rules.value = rulesSnapshot
      }
      ElMessage.error(t('app.saveNodesFailed'))
    }
  }
}

const viewDeviceDetails = () => {
  if (!contextMenu.value.node) return
  // 显示设备详情 - 复用左侧列表点击的逻辑
  onDeviceListClick(contextMenu.value.node.id)
  closeContextMenu()
}


const forceDeleteNode = async (nodeId: string) => {
  // 删除会同时改动 nodes/rules/edges/内部变量连线/specs，且下面用 Promise.all 分三次保存，
  // 可能部分成功导致后端三者不一致。先做整体快照，保存失败时回滚到删除前状态。
  const nodesSnapshot = JSON.parse(JSON.stringify(nodes.value))
  const rulesSnapshot = JSON.parse(JSON.stringify(rules.value))
  const specsSnapshot = JSON.parse(JSON.stringify(specifications.value))
  const edgesSnapshot = JSON.parse(JSON.stringify(edges.value))
  const internalEdgesSnapshot = JSON.parse(JSON.stringify(internalVariableEdges.value))

  const deletedNode = nodes.value.find(n => n.id === nodeId)
  // 先找出要删除的内部变量节点ID（在删除主节点之前）
  const variableNodeIds = nodes.value
    .filter(n => n.id.startsWith(`${nodeId}_`) && n.templateName?.startsWith('variable_'))
    .map(n => n.id)
  
  // 删除设备及其内部变量节点
  nodes.value = nodes.value.filter(n => n.id !== nodeId && !n.id.startsWith(`${nodeId}_`))

  // 删除与该设备相关的规则
  const rulesToDelete = rules.value.filter(rule =>
    (deletedNode && isNodeReference(rule.toId, deletedNode))
    || rule.toId === nodeId
    || rule.sources.some(source => (deletedNode && isNodeReference(source.fromId, deletedNode)) || source.fromId === nodeId)
  )
  const ruleIdsToDelete = rulesToDelete.map(rule => rule.id)
  rules.value = rules.value.filter(rule => !ruleIdsToDelete.includes(rule.id))

  // 动态生成 edges（自动删除与该设备相关的边）
  edges.value = generateEdgesFromRules()

  // 删除相关的内部变量连线
  internalVariableEdges.value = internalVariableEdges.value.filter(
    edge => edge.from !== nodeId && !variableNodeIds.includes(edge.to)
  )

  const { nextSpecs, removed } = removeSpecsForNode(specifications.value, nodeId)
  const labelRemoval = deletedNode?.label && deletedNode.label !== nodeId
    ? removeSpecsForNode(nextSpecs, deletedNode.label)
    : { nextSpecs, removed: [] as Specification[] }
  specifications.value = labelRemoval.nextSpecs
  const removedSpecs = [...removed, ...labelRemoval.removed]

  // 原子保存 nodes+rules+specs（后端单事务）。要么三者全部落库，要么全部不落库，
  // 不再有「节点删了但规则没删」的半删状态。失败时回滚到删除前快照即为精确恢复。
  try {
    const nodesToSave = JSON.parse(JSON.stringify(nodes.value))
    const rulesToSave = JSON.parse(JSON.stringify(rules.value))
    const specsToSave = JSON.parse(JSON.stringify(specifications.value))
    await boardApi.saveBoardBatch({ nodes: nodesToSave, rules: rulesToSave, specs: specsToSave })

    if (ruleIdsToDelete.length > 0) {
      ElMessage.info(t('app.relatedRulesRemoved', { count: ruleIdsToDelete.length }))
    }
    if (removedSpecs.length > 0) {
      ElMessage.info(t('app.relatedSpecsRemoved'))
    }
  } catch (error) {
    console.error('删除设备保存失败，回滚本地状态', error)
    // 后端单事务保证未落库，回滚到删除前快照即完全一致，无需再拉后端。
    nodes.value = nodesSnapshot
    rules.value = rulesSnapshot
    specifications.value = specsSnapshot
    edges.value = edgesSnapshot
    internalVariableEdges.value = internalEdgesSnapshot
    ElMessage.error(t('app.deleteDeviceSaveFailedRollback'))
  }
}

const deleteCurrentNodeWithConfirm = (nodeId: string) => {
  const node = nodes.value.find(n => n.id === nodeId)
  if (!node) return

  const hasEdges = edges.value.some(e => e.from === nodeId || e.to === nodeId)
  const hasSpecs = specifications.value.some(spec =>
    isSpecRelatedToNode(spec, nodeId) || isSpecRelatedToNode(spec, node.label)
  )

  // 显示自定义确认对话框
  deleteConfirmDialogData.node = node
  deleteConfirmDialogData.hasRelations = hasEdges || hasSpecs
  deleteConfirmDialogData.relationCount = {
    rules: edges.value.filter(e => e.from === nodeId || e.to === nodeId).length,
    specs: specifications.value.filter(spec =>
      isSpecRelatedToNode(spec, nodeId) || isSpecRelatedToNode(spec, node.label)
    ).length
  }
  deleteConfirmDialogVisible.value = true
}

const handleDialogDelete = () => {
  if (!dialogMeta.nodeId) return
  deleteCurrentNodeWithConfirm(dialogMeta.nodeId)
}

// Custom dialog handlers
const confirmRename = async () => {
  if (!renameDialogData.node || !renameDialogData.newName.trim()) return

  await handleRenameDevice(renameDialogData.node.id, renameDialogData.newName.trim())
  renameDialogVisible.value = false
  renameDialogData.node = null
  renameDialogData.newName = ''
}

const cancelRename = () => {
  renameDialogVisible.value = false
  renameDialogData.node = null
  renameDialogData.newName = ''
}

const confirmDelete = async () => {
  if (!deleteConfirmDialogData.node) return

  try {
    await forceDeleteNode(deleteConfirmDialogData.node!.id)
    // 如果设备详情对话框是打开的，也要关闭它
    if (dialogVisible.value) {
      dialogVisible.value = false
    }
    deleteConfirmDialogVisible.value = false
    deleteConfirmDialogData.node = null
  } catch (error) {
    console.error('删除设备失败:', error)
    ElMessage.error(t('app.deleteDeviceFailedRetry'))
  }
}

const cancelDelete = () => {
  deleteConfirmDialogVisible.value = false
  deleteConfirmDialogData.node = null
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
  const ruleToDelete = rules.value.find(r => r.id === ruleId)
  if (!ruleToDelete) return

  // 删除规则
  rules.value = rules.value.filter(r => r.id !== ruleId)

  // 动态生成 edges（自动删除与该规则相关的边）
  edges.value = generateEdgesFromRules()

  // 只保存 rules
  try {
    // 将 Proxy 对象转换为普通对象后再发送
    const rulesToSave = JSON.parse(JSON.stringify(rules.value))
    await boardApi.saveRules(rulesToSave)
    ElMessage.success(t('app.deleteRuleSuccess'))
  } catch (e) {
    console.error('删除规则失败', e)
    // 保存失败，回滚（重新获取）
    await refreshRules()
    ElMessage.error(t('app.deleteRuleFailed'))
  }
}

const deleteSpecification = async (specId: string) => {
  const specToDelete = specifications.value.find(s => s.id === specId)
  if (!specToDelete) return

  // 删除规约
  specifications.value = specifications.value.filter(s => s.id !== specId)

  try {
    await saveSpecsToServer()
    ElMessage.success(t('app.deleteSpecSuccess'))
  } catch (e) {
    console.error('删除规约失败', e)
    // 保存失败，回滚（重新获取）
    await refreshSpecifications()
    ElMessage.error(t('app.deleteSpecFailed'))
  }
}

/* =================================================================================
 * 9. API Interactions (Save)
 * ================================================================================= */

const buildBoardLayoutPayload = (): BoardLayoutDto => ({
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
})

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

  const control = layout.panels?.control
  if (control) {
    boardPanels.control.collapsed = Boolean(control.collapsed)
    boardPanels.control.width = clampPanelWidth(control.width, DEFAULT_CONTROL_PANEL_WIDTH)
    boardPanels.control.activeSection = isControlCenterSection(control.activeSection)
      ? control.activeSection
      : 'devices'
  }

  const inspector = layout.panels?.inspector
  if (inspector) {
    boardPanels.inspector.collapsed = Boolean(inspector.collapsed)
    boardPanels.inspector.width = clampPanelWidth(inspector.width, DEFAULT_INSPECTOR_PANEL_WIDTH)
    boardPanels.inspector.activeSection = isInspectorSection(inspector.activeSection)
      ? inspector.activeSection
      : 'devices'
  }

  applyViewportPanelConstraints()
}

const saveBoardLayout = async () => {
  try {
    await boardApi.saveLayout(buildBoardLayoutPayload())
    layoutSaveErrorShown = false
  } catch (e) {
    console.error('保存画布布局失败', e)
    if (!layoutSaveErrorShown) {
      layoutSaveErrorShown = true
      ElMessage.error(t('app.saveLayoutFailed'))
    }
  }
}

const scheduleBoardLayoutSave = () => {
  if (!layoutHydrated.value) return
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

const saveNodesToServer = async () => {
  try {
    await boardApi.saveNodes(nodes.value)
  } catch (e) {
    ElMessage.error(t('app.saveNodesFailed'))
    // 必须 rethrow：否则调用方以为保存成功（会误报成功/无法回滚），本地状态与后端分叉。
    throw e
  }
}

const openControlSection = (section: InspectorSection) => {
  const controlSection: ControlCenterSection = section === 'rules'
    ? 'rules'
    : section === 'specs'
      ? 'specs'
      : 'devices'

  boardPanels.control.collapsed = false
  boardPanels.control.activeSection = controlSection
}

// 从 rules 动态生成 edges（不单独存储到服务器）
const generateEdgesFromRules = (): DeviceEdge[] => {
  const result: DeviceEdge[] = []
  
  for (const rule of rules.value) {
    if (!rule.sources || !rule.toId) continue
    
    const toNode = resolveNodeRef(rule.toId)
    if (!toNode) continue
    
    for (const source of rule.sources) {
      const fromId = source.fromId
      if (!fromId) continue
      
      const fromNode = resolveNodeRef(fromId)
      if (!fromNode) continue
      
      const { fromPoint, toPoint } = getLinkPoints(fromNode, toNode)
      
      result.push({
        id: `edge_${rule.id}_${fromId}`,
        from: fromNode.id,
        to: toNode.id,
        fromLabel: fromNode.label,
        toLabel: toNode.label,
        fromPos: fromPoint,
        toPos: toPoint,
        fromApi: source.fromApi || '',
        toApi: rule.toApi || '',
        itemType: source.itemType as 'api' | 'variable' | undefined,
        relation: source.relation || '',
        value: source.value || ''
      })
    }
  }
  
  return result
}

const saveSpecsToServer = async () => {
  try {
    // 将 Proxy 对象转换为普通对象后再发送
    const specsToSave = JSON.parse(JSON.stringify(specifications.value))
    await boardApi.saveSpecs(specsToSave)
  }
  catch (e: any) {
    console.error('[Board] Save specs failed:', e)
    // 打印更详细的错误信息
    if (e.response) {
      console.error('[Board] Server error response:', e.response.data)
      console.error('[Board] Server error status:', e.response.status)
    }
    ElMessage.error(t('app.saveSpecsFailed'))
    // 必须 rethrow：deleteSpecification 等调用方依赖抛错触发回滚（refreshSpecifications）。
    throw e
  }
}

const ruleBuilderVisible = ref(false)

const refreshDeviceTemplates = async () => {
  try {
    // 普通刷新只 GET 模板列表。默认模板在注册时已由后端 initDefaultTemplates 播种，
    // 不能在这里调用 reloadDeviceTemplates()：它会删除该用户全部模板（含自定义模板）再重建默认，
    // 会导致「创建/导入自定义模板后跳回 Board 立刻被删」「删除模板后刷新又重建默认」。
    const res = await boardApi.getDeviceTemplates()
    deviceTemplates.value = res || []
  } catch (e) {
    console.error('加载设备模板失败:', e)
    deviceTemplates.value = []
  }
}

// 显式「重置为默认模板」：会删除用户全部自定义模板并重建默认模板，仅在用户主动确认时调用。
const resetDeviceTemplatesToDefault = async () => {
  await boardApi.reloadDeviceTemplates()
  await refreshDeviceTemplates()
}



/* =================================================================================
 * 10. Lifecycle & Watchers
 * ================================================================================= */

// 1. 定义刷新设备的函数
const refreshDevices = async () => {
  try { nodes.value = await boardApi.getNodes() } catch(e) {
    console.error('加载设备失败', e)
    nodes.value = [] }

  // 重新生成内部变量连线（根据已加载的节点和设备模板）
  regenerateInternalVariableEdges()
}

// 2.定义刷新规则的函数（edges 由 rules 动态生成）
const refreshRules = async () => {
  try {
    // 只获取规则列表
    const rulesData = await boardApi.getRules()
    rules.value = rulesData
    // 动态生成 edges
    edges.value = generateEdgesFromRules()
  } catch (e) {
    console.error('加载规则失败', e)
    rules.value = []
    edges.value = []
  }
}

// 3.定义刷新规约的函数
const refreshSpecifications = async () => {
  try { specifications.value = await boardApi.getSpecs() } catch(e) {
    console.error('加载规约失败', e)
    specifications.value = []
  }
}

onMounted(async () => {
  await refreshDeviceTemplates()

  // Load Data
  await refreshDevices()
  await refreshRules()
  await refreshSpecifications()
  await loadTaskInbox(false, { showLoading: false })
  taskInboxRefreshTimer = setInterval(() => {
    if (activeBackgroundTaskCount.value > 0 || showHistoryPanel.value) {
      void loadTaskInbox(false, { showLoading: false })
    }
  }, TASK_INBOX_REFRESH_INTERVAL_MS)

  // 监听 AI 推荐的设备添加事件
  window.addEventListener('ai-suggestion-add-device', handleAISuggestionAddDevice as EventListener)

  // Snapshot manifests for all nodes while templates still exist.
  // This ensures deleting templates later won't affect existing nodes’ details (variables/states/APIs).
  const resolveTemplateForHydration = (n: DeviceNode) => {
    let template = deviceTemplates.value.find(t => t.manifest?.Name === n.templateName)
    if (!template && n.templateName) {
      template = deviceTemplates.value.find(t => t.manifest?.Name?.toLowerCase() === n.templateName?.toLowerCase())
    }
    if (!template && n.templateName) {
      template = deviceTemplates.value.find(t =>
        n.templateName.toLowerCase().includes(t.manifest?.Name?.toLowerCase() || '') ||
        (t.manifest?.Name?.toLowerCase() || '').includes(n.templateName.toLowerCase())
      )
    }
    return template || null
  }
  hydrateManifestCacheForNodes(nodes.value, resolveTemplateForHydration as any)

  // Load Layout (only canvas)
  try {
    const layout = await boardApi.getLayout()
    applyBoardLayout(layout)
  } catch {
    // Layout loading failed
  } finally {
    layoutHydrated.value = true
  }

  window.addEventListener('keydown', onGlobalKeydown)
})


// Color utilities (matching CanvasBoard colors)
const getCanvasMapColorIndex = (nodeId: string): number => {
  // 内部变量节点使用父设备的颜色
  if (nodeId.includes('_') && !nodeId.startsWith('edge_')) {
    const parentDeviceId = nodeId.substring(0, nodeId.lastIndexOf('_'))
    return getCanvasMapColorIndex(parentDeviceId)
  }
  
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
  // 内部变量连线使用灰色
  if (nodeId.startsWith('edge_') || isInternalVariableEdgeById(nodeId)) {
    return '#94a3b8' // 灰色
  }
  
  // Return actual color values instead of Tailwind classes
  const colorIndex = getCanvasMapColorIndex(nodeId)
  const colorValues = [
    '#2563eb', '#0891b2', '#0f766e', '#7c3aed',
    '#475569', '#0284c7', '#4f46e5', '#0d9488'
  ] // non-alert map colors; red is reserved for actual warnings elsewhere
  return colorValues[colorIndex] || colorValues[0]
}

// 辅助函数：判断是否是内部变量连线
const isInternalVariableEdgeById = (edgeId: string): boolean => {
  const edge = allEdges.value.find(e => e.id === edgeId)
  return edge?.itemType === 'variable' && edge?.relation === 'contains'
}

const getCanvasMapSize = (): string => {
  // All nodes use the same size for consistency
  return 'size-2'
}

// Canvas map calculations
const canvasMapData = computed(() => {
  if (nodes.value.length === 0) return { dots: [], lines: [] }

  // Calculate canvas bounds
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity

  nodes.value.forEach(node => {
    const x = node.position.x
    const y = node.position.y
    const width = node.width || 110
    const height = node.height || 90

    minX = Math.min(minX, x)
    minY = Math.min(minY, y)
    maxX = Math.max(maxX, x + width)
    maxY = Math.max(maxY, y + height)
  })

  // Add some padding
  const padding = 100
  minX -= padding
  minY -= padding
  maxX += padding
  maxY += padding

  const canvasWidth = maxX - minX
  const canvasHeight = maxY - minY

  // Map dimensions match the compact w-56 / p-3 / h-24 canvas map viewport.
  const mapWidth = 200
  const mapHeight = 96
  const mapInset = 8

  // Convert node positions to mini map coordinates
  const dots = nodes.value.map((node) => {
    const nodeX = canvasWidth > 0
      ? mapInset + ((node.position.x - minX) / canvasWidth) * (mapWidth - mapInset * 2)
      : mapWidth / 2
    const nodeY = canvasHeight > 0
      ? mapInset + ((node.position.y - minY) / canvasHeight) * (mapHeight - mapInset * 2)
      : mapHeight / 2

    return {
      id: node.id,
      x: Math.max(mapInset / 2, Math.min(mapWidth - mapInset - 4, nodeX)),
      y: Math.max(mapInset / 2, Math.min(mapHeight - mapInset - 4, nodeY)),
      size: getCanvasMapSize(),
      color: getCanvasMapColor(node.id)
    }
  })

  // Create node lookup map for easy access
  const nodeMap = new Map(dots.map(dot => [dot.id, dot]))

  // Generate lines for edges (including internal variable edges)
  const lines = allEdges.value.map((edge) => {
    const fromDot = nodeMap.get(edge.from)
    const toDot = nodeMap.get(edge.to)

    if (!fromDot || !toDot) return null

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

    return {
      id: edge.id,
      fromId: edge.from,
      x1: fromDot.x + 4, // Center of dot (assuming 8px diameter)
      y1: fromDot.y + 4 + offsetY,
      x2: toDot.x + 4,
      y2: toDot.y + 4 + offsetY,
      // 内部变量连线使用灰色，其他连线使用源设备颜色
      color: (edge.itemType === 'variable' && edge.relation === 'contains') ? '#94a3b8' : getCanvasMapColor(edge.from),
      isBidirectional
    }
  }).filter(Boolean)

  return { dots, lines }
})

const canvasMapDots = computed(() => canvasMapData.value.dots)
const canvasMapLines = computed(() => canvasMapData.value.lines.filter(line => line !== null && line !== undefined))

const getNodeBounds = (targetNodes: DeviceNode[] = nodes.value) => {
  if (targetNodes.length === 0) return null
  return targetNodes.reduce((bounds, node) => {
    const x = node.position.x
    const y = node.position.y
    const width = node.width || 110
    const height = node.height || 90
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

const getVisibleCanvasFrame = () => {
  const canvasEl = document.querySelector('.canvas-container')
  if (!canvasEl) return null
  const rect = canvasEl.getBoundingClientRect()
  const leftInset = boardPanels.control.collapsed ? 64 : boardPanels.control.width
  const rightInset = boardPanels.inspector.collapsed ? 48 : boardPanels.inspector.width
  const topInset = 64
  const timelineVisible = simulationAnimationState.value.visible || traceAnimationState.value.visible
  const bottomInset = timelineVisible
    ? Math.min(260, Math.max(160, window.innerHeight * 0.28))
    : 24
  const availableWidth = Math.max(240, rect.width - leftInset - rightInset)
  const availableHeight = Math.max(180, rect.height - topInset - bottomInset)
  return {
    left: leftInset,
    top: topInset,
    width: availableWidth,
    height: availableHeight
  }
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
  fitNodesToCanvas(nodes.value)
}

const centerSelection = () => {
  const stateIndex = highlightedTrace.value?.selectedStateIndex
  const traceState = typeof stateIndex === 'number'
    ? highlightedTrace.value?.states?.[stateIndex]
    : null
  const highlightedNodes = traceState?.devices
    ? nodes.value.filter(node => traceState.devices.some((device: any) =>
        device.deviceId === node.id || device.deviceLabel === node.label
      ))
    : []

  fitNodesToCanvas(highlightedNodes.length > 0 ? highlightedNodes : nodes.value)
}

const handleCreateDevice = async (data: { template: DeviceTemplate, customName: string }) => {
  const { template, customName } = data

  // 快照，保存失败时回滚本次新增节点/连线，避免本地与后端分叉。
  const idsBefore = new Set(nodes.value.map(n => n.id))
  const edgeIdsBefore = new Set(internalVariableEdges.value.map(edge => edge.id))

  // Create device with custom name
  const uniqueLabel = getUniqueLabel(customName, nodes.value)
  const node: DeviceNode = {
    id: uniqueLabel,
    templateName: template.manifest.Name,
    label: uniqueLabel,
    position: getNextNodePosition(),
    state: template.manifest.InitState || 'Working',
    width: 110,
    height: 90
  }
  nodes.value.push(node)

  // 如果有内部变量，创建变量节点和连线（圆形设计）
  const internalVariables = template.manifest.InternalVariables || []
  if (internalVariables.length > 0) {
    const pos = node.position
    const variableStartX = pos.x + 160
    const variableSpacingY = 70

    internalVariables.forEach((variable, index) => {
      const variableId = `${uniqueLabel}_${variable.Name}`
      const variableNode: DeviceNode = {
        id: variableId,
        templateName: `variable_${variable.Name}`,
        label: variable.Name,
        position: {
          x: variableStartX,
          y: pos.y + index * variableSpacingY
        },
        state: 'variable',
        width: 60,   // 圆形宽度
        height: 60   // 圆形高度
      }
      nodes.value.push(variableNode)

      const edgeId = `edge_${uniqueLabel}_to_${variableId}`
      const edge: DeviceEdge = {
        id: edgeId,
        from: uniqueLabel,
        to: variableId,
        fromLabel: uniqueLabel,
        toLabel: variable.Name,
        fromPos: { x: pos.x + 110, y: pos.y + 45 },
        toPos: { x: variableStartX, y: pos.y + index * variableSpacingY + 30 },
        itemType: 'variable',
        relation: 'contains',
        value: variable.Name
      }
      internalVariableEdges.value.push(edge)
    })
  }

  try {
    await saveNodesToServer()
    // 成功提示放在保存成功后（ControlCenter 的 emit 不会 await 本函数，不能在子组件里提前报成功）。
    ElMessage.success(t('app.deviceAdded'))
  } catch {
    // 回滚本次新增的节点与内部变量连线（saveNodesToServer 已弹出失败提示）。
    nodes.value = nodes.value.filter(n => idsBefore.has(n.id))
    internalVariableEdges.value = internalVariableEdges.value.filter(edge => edgeIdsBefore.has(edge.id))
  }
}

const openRuleBuilder = () => {
  openControlSection('rules')
  ruleBuilderVisible.value = true
}

const handleAddSpec = async (data: { 
  templateId: string, 
  devices: Array<{deviceId: string, deviceLabel: string, selectedApis: string[]}>, 
  formula: string,
  aConditions: SpecCondition[],
  ifConditions: SpecCondition[],
  thenConditions: SpecCondition[]
}) => {
  const { templateId, devices, formula, aConditions, ifConditions, thenConditions } = data

  // Create specification with LTL formula
  const specId = 'spec_' + Date.now()
  
  // Get template label from spec templates or use templateId
  const specTemplate = defaultSpecTemplates.find(t => t.id === templateId)
  const templateLabel = specTemplate?.label || templateId

  const newSpec: Specification = {
    id: specId,
    templateId: templateId as any,
    templateLabel: templateLabel,
    aConditions: aConditions || [],
    ifConditions: ifConditions || [],
    thenConditions: thenConditions || [],
    formula: formula,
    devices: devices
  }

  specifications.value.push(newSpec)
  try {
    await saveSpecsToServer()
  } catch {
    // 回滚本次新增的规约（saveSpecsToServer 已弹出失败提示），避免本地已加但后端未保存。
    specifications.value = specifications.value.filter(s => s.id !== newSpec.id)
  }
}

const handleDeleteTemplate = async () => {
  // Template deletion is handled in ControlCenter component
  // Just refresh the templates list after deletion
  await refreshDeviceTemplates()
}

const getNextNodePosition = (): { x: number; y: number } => {
  // 将节点放置在画布网格中央附近，确保无重叠
  const count = nodes.value.length

  // 基础节点尺寸（用于碰撞检测）
  const nodeWidth = 110
  const nodeHeight = 90
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
    const hasOverlap = nodes.value.some(node => {
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
  pollingAborted.value = true
  stopTraceAnimation()
  stopSimulationAnimation()
  if (taskInboxRefreshTimer) {
    clearInterval(taskInboxRefreshTimer)
    taskInboxRefreshTimer = null
  }
  if (layoutSaveTimer) {
    clearTimeout(layoutSaveTimer)
    layoutSaveTimer = null
    if (layoutHydrated.value) {
      void saveBoardLayout()
    }
  }
  window.removeEventListener('keydown', onGlobalKeydown)
  window.removeEventListener('pointermove', onCanvasPointerMove)
  window.removeEventListener('pointerup', onCanvasPointerUp)
  window.removeEventListener('ai-suggestion-add-device', handleAISuggestionAddDevice as EventListener)
})

defineExpose({
  refreshDevices,
  refreshRules,
  refreshSpecifications,
  refreshDeviceTemplates,
  resetDeviceTemplatesToDefault,
})

// ==== Verification Logic ====
const isVerifying = ref(false)
const verificationResult = ref<any>(null)
const verificationError = ref<string | null>(null)

// ==== Rule Recommendation Logic ====
const isRecommendingRules = ref(false)
const ruleRecommendations = ref<RuleRecommendation[]>([])
const showRecommendationPanel = ref(false)
const ruleRecommendationFilters = reactive({
  maxRecommendations: 5,
  category: 'all'
})
const ruleRecommendationCategories = [
  { labelKey: 'app.recommendationCategoryAll', value: 'all' },
  { labelKey: 'app.recommendationCategorySecurity', value: 'security' },
  { labelKey: 'app.recommendationCategoryEnergySaving', value: 'energy_saving' },
  { labelKey: 'app.recommendationCategoryComfort', value: 'comfort' },
  { labelKey: 'app.recommendationCategoryAutomation', value: 'automation' }
]

const normalizeRecommendationCount = (value: unknown): number => {
  const parsed = Number(value)
  if (!Number.isFinite(parsed)) return 5
  return Math.min(10, Math.max(1, Math.trunc(parsed)))
}

const formatRecommendationPriority = (priority: unknown): string => {
  switch (String(priority || 'medium').toLowerCase()) {
    case 'high':
      return t('app.priorityHigh')
    case 'low':
      return t('app.priorityLow')
    case 'medium':
      return t('app.priorityMedium')
    default:
      return String(priority || t('app.priorityMedium'))
  }
}

const fetchRuleRecommendations = async () => {
  // 如果正在推荐中，点击按钮则停止推荐
  if (isRecommendingRules.value) {
    // 调用取消函数
    rulesApi.cancelRecommendRules()
    isRecommendingRules.value = false
    ElMessage.info(t('app.ruleRecommendationCancelled'))
    return
  }

  // 互斥检查：如果模拟动画或反例路径动画正在显示，则不允许打开推荐面板
  if (simulationAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCurrentSimulationFirst'), type: 'warning' })
    return
  }
  if (traceAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCounterexampleFirst'), type: 'warning' })
    return
  }
  // 互斥检查：如果设备推荐面板正在显示
  if (showDeviceRecommendationPanel.value) {
    ElMessage.warning({ message: t('app.closeDeviceRecommendationFirst'), type: 'warning' })
    return
  }
  // 互斥检查：如果规约推荐面板正在显示
  if (showSpecRecommendationPanel.value) {
    ElMessage.warning({ message: t('app.closeSpecRecommendationFirst'), type: 'warning' })
    return
  }
  if (showHistoryPanel.value) {
    ElMessage.warning({ message: t('app.closeHistoryFirst'), type: 'warning' })
    return
  }
  
  isRecommendingRules.value = true
  showRecommendationPanel.value = true
  try {
    const response = await rulesApi.recommendRules(
      normalizeRecommendationCount(ruleRecommendationFilters.maxRecommendations),
      ruleRecommendationFilters.category
    )
    ruleRecommendations.value = response.recommendations || []
  } catch (error: any) {
    // 如果是取消请求，不显示错误
    if (error.name === 'CanceledError' || error.code === 'ERR_CANCELED') {
      return
    }
    console.error('Failed to fetch rule recommendations:', error)
    ElMessage.error(t('app.failedToFetchRuleRecommendations'))
  } finally {
    isRecommendingRules.value = false
  }
}

// 关闭推荐面板
const closeRecommendationPanel = () => {
  // 如果正在推荐中，先取消请求
  if (isRecommendingRules.value) {
    rulesApi.cancelRecommendRules()
    isRecommendingRules.value = false
  }
  showRecommendationPanel.value = false
}

// ==== Device Recommendation Logic ====
const isRecommendingDevices = ref(false)
const deviceRecommendations = ref<any[]>([])
const showDeviceRecommendationPanel = ref(false)
const deviceRecommendationAbortController = ref<AbortController | null>(null)

// ==== Specification Recommendation Logic ====
const isRecommendingSpecs = ref(false)
const specRecommendations = ref<any[]>([])
const showSpecRecommendationPanel = ref(false)
const specRecommendationAbortController = ref<AbortController | null>(null)
const specRecommendationFilters = reactive({
  maxRecommendations: 5,
  category: 'all'
})
const specRecommendationCategories = [
  { labelKey: 'app.recommendationCategoryAll', value: 'all' },
  { labelKey: 'app.recommendationCategorySafety', value: 'safety' },
  { labelKey: 'app.recommendationCategoryResponse', value: 'response' },
  { labelKey: 'app.recommendationCategoryConsistency', value: 'consistency' },
  { labelKey: 'app.recommendationCategoryPrivacy', value: 'privacy' }
]

const fetchDeviceRecommendations = async () => {
  // 如果正在推荐中，点击按钮则停止推荐
  if (isRecommendingDevices.value) {
    if (deviceRecommendationAbortController.value) {
      deviceRecommendationAbortController.value.abort()
    }
    isRecommendingDevices.value = false
    ElMessage.info(t('app.deviceRecommendationCancelled'))
    return
  }

  // 互斥检查
  if (simulationAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCurrentSimulationFirst'), type: 'warning' })
    return
  }
  if (traceAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCounterexampleFirst'), type: 'warning' })
    return
  }
  if (showRecommendationPanel.value) {
    ElMessage.warning({ message: t('app.closeRuleRecommendationFirst'), type: 'warning' })
    return
  }
  if (showSpecRecommendationPanel.value) {
    ElMessage.warning({ message: t('app.closeSpecRecommendationFirst'), type: 'warning' })
    return
  }
  if (showHistoryPanel.value) {
    ElMessage.warning({ message: t('app.closeHistoryFirst'), type: 'warning' })
    return
  }
  if (isAnimationLocked.value) {
    ElMessage.warning({ message: t('app.animationRunningWait'), type: 'warning' })
    return
  }
  
  isRecommendingDevices.value = true
  showDeviceRecommendationPanel.value = true
  deviceRecommendationAbortController.value = new AbortController()
  
  try {
    const response = await boardApi.recommendRelatedDevices(
      nodes.value,
      deviceTemplates.value,
      deviceRecommendationAbortController.value.signal
    )
    deviceRecommendations.value = response.recommendations || []
  } catch (error: any) {
    if (error.name === 'CanceledError' || error.code === 'ERR_CANCELED') {
      return
    }
    console.error('Failed to fetch device recommendations:', error)
    ElMessage.error(t('app.failedToFetchDeviceRecommendations'))
  } finally {
    isRecommendingDevices.value = false
  }
}

// 关闭设备推荐面板
const closeDeviceRecommendationPanel = () => {
  if (isRecommendingDevices.value) {
    if (deviceRecommendationAbortController.value) {
      deviceRecommendationAbortController.value.abort()
    }
    isRecommendingDevices.value = false
  }
  showDeviceRecommendationPanel.value = false
}

// 获取规约推荐
const fetchSpecRecommendations = async () => {
  // 如果正在推荐中，点击按钮则停止推荐
  if (isRecommendingSpecs.value) {
    if (specRecommendationAbortController.value) {
      specRecommendationAbortController.value.abort()
    }
    isRecommendingSpecs.value = false
    ElMessage.info(t('app.specificationRecommendationCancelled'))
    return
  }

  // 互斥检查
  if (simulationAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCurrentSimulationFirst'), type: 'warning' })
    return
  }
  if (traceAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCounterexampleFirst'), type: 'warning' })
    return
  }
  if (showRecommendationPanel.value) {
    ElMessage.warning({ message: t('app.closeRuleRecommendationFirst'), type: 'warning' })
    return
  }
  if (showDeviceRecommendationPanel.value) {
    ElMessage.warning({ message: t('app.closeDeviceRecommendationFirst'), type: 'warning' })
    return
  }
  if (showHistoryPanel.value) {
    ElMessage.warning({ message: t('app.closeHistoryFirst'), type: 'warning' })
    return
  }
  if (isAnimationLocked.value) {
    ElMessage.warning({ message: t('app.animationRunningWait'), type: 'warning' })
    return
  }
  
  isRecommendingSpecs.value = true
  showSpecRecommendationPanel.value = true
  specRecommendationAbortController.value = new AbortController()
  
  try {
    const response = await boardApi.recommendSpecifications(
      normalizeRecommendationCount(specRecommendationFilters.maxRecommendations),
      specRecommendationFilters.category,
      specRecommendationAbortController.value.signal
    )
    specRecommendations.value = response.recommendations || []
  } catch (error: any) {
    if (error.name === 'CanceledError' || error.code === 'ERR_CANCELED') {
      return
    }
    console.error('Failed to fetch specification recommendations:', error)
    ElMessage.error(t('app.failedToFetchSpecificationRecommendations'))
  } finally {
    isRecommendingSpecs.value = false
    specRecommendationAbortController.value = null
  }
}

// 关闭规约推荐面板
const closeSpecRecommendationPanel = () => {
  if (isRecommendingSpecs.value && specRecommendationAbortController.value) {
    specRecommendationAbortController.value.abort()
  }
  isRecommendingSpecs.value = false
  showSpecRecommendationPanel.value = false
}

// 应用规约推荐 - 将推荐的规约添加到画布
const applySpecRecommendation = async (recommendation: any) => {
  // 后端 SpecificationDto.templateId 受 @Pattern("^[1-7]$") 约束；非法值会让整批
  // saveSpecs 返回 400（全量替换，会牵连已有规约）。此处显式校验并跳过，避免发送注定失败的请求。
  const templateId = recommendation.templateId
  if (!/^[1-7]$/.test(String(templateId ?? ''))) {
    ElMessage.warning({
      message: t('app.invalidRecommendedTemplateId', { templateId: templateId ?? '' }),
      type: 'warning'
    })
    return
  }

  // 构建规约数据
  const newSpec = {
    id: 'spec_' + Date.now() + '_' + Math.random().toString(36).substr(2, 9),
    templateId,
    templateLabel: recommendation.templateLabel || t('app.customSpecification'),
    aConditions: recommendation.aConditions || [],
    ifConditions: recommendation.ifConditions || [],
    thenConditions: recommendation.thenConditions || []
  }

  // 获取现有规约
  const currentSpecs = [...specifications.value]
  currentSpecs.push(newSpec)
  
  try {
    await boardApi.saveSpecs(currentSpecs)
    specifications.value = currentSpecs
    ElMessage.success(t('app.specificationAddedSuccessfully'))
    
    // 关闭面板
    closeSpecRecommendationPanel()
  } catch (error) {
    console.error('Failed to save specification:', error)
    ElMessage.error(t('app.failedToSaveSpecification'))
  }
}

// 应用设备推荐 - 将推荐的设备添加到画布
const applyDeviceRecommendation = async (recommendation: any) => {
  const templateName = recommendation.templateName
  const template = deviceTemplates.value.find(t => 
    t.manifest.Name.toLowerCase() === templateName.toLowerCase()
  )
  
  if (!template) {
    ElMessage.error(t('app.templateNotFoundWithName', { name: templateName }))
    return
  }
  
  // 计算新设备位置（画布中央附近）
  const canvasEl = document.querySelector('.canvas-container')
  if (!canvasEl) return
  
  const rect = canvasEl.getBoundingClientRect()
  const centerX = rect.width / 2
  const centerY = rect.height / 2
  
  const x = (centerX - canvasPan.value.x) / canvasZoom.value
  const y = (centerY - canvasPan.value.y) / canvasZoom.value
  
  // createDeviceInstanceAt 内部已保存并在失败时回滚+抛错，这里只需处理成功/失败提示。
  try {
    await createDeviceInstanceAt(template, { x, y })
    ElMessage.success(t('app.deviceAddedWithName', { name: templateName }))
  } catch {
    // 失败提示已由 saveNodesToServer 弹出，节点已回滚，无需额外处理。
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
  intensity: 3,
  enablePrivacy: false,
  isAsync: false,
  saveToHistory: true
})

// Verification form state (similar to simulation)
const verificationForm = reactive({
  isAttack: false,
  intensity: 3,
  enablePrivacy: false,
  isAsync: false
})

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

type HistoryTab = 'tasks' | 'verification' | 'simulation'

// History records are loaded through the same persisted-trace APIs used by AI tools.
const verificationTasks = ref<VerificationTaskSummary[]>([])
const simulationTasks = ref<SimulationTaskSummary[]>([])
const verificationTraces = ref<Trace[]>([])
const simulationTraces = ref<SimulationTraceSummary[]>([])
const showHistoryPanel = ref(false)
const activeHistoryTab = ref<HistoryTab>('tasks')
const loadingTaskHistory = ref(false)
const loadingVerificationHistory = ref(false)
const loadingSimulationHistory = ref(false)
let taskInboxRefreshTimer: ReturnType<typeof setInterval> | null = null

const historyActionLocked = computed(() =>
  traceAnimationState.value.visible ||
  simulationAnimationState.value.visible ||
  isAnimationLocked.value
)

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

const activeVerificationTasks = computed(() =>
  verificationTasks.value.filter(task => isActiveTaskStatus(task.status))
)

const activeSimulationTasks = computed(() =>
  simulationTasks.value.filter(task => isActiveTaskStatus(task.status))
)

const activeBackgroundTaskCount = computed(() =>
  activeVerificationTasks.value.length + activeSimulationTasks.value.length
)

const miniTaskItems = computed(() => {
  const items: Array<{
    key: string
    kind: 'verification' | 'simulation'
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
      status: formatAsyncTaskStatus(task.status),
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
      status: formatAsyncTaskStatus(task.status),
      progress: normalizeTaskProgress(task.progress)
    })
  }

  return items
})

const upsertVerificationTaskSummary = (task: Partial<VerificationTaskSummary> & { id?: number }) => {
  if (!task.id) return
  const existing = verificationTasks.value.findIndex(item => item.id === task.id)
  const next = task as VerificationTaskSummary
  verificationTasks.value = existing >= 0
    ? verificationTasks.value.map(item => item.id === task.id ? { ...item, ...next } : item)
    : [next, ...verificationTasks.value]
}

const upsertSimulationTaskSummary = (task: Partial<SimulationTaskSummary> & { id?: number }) => {
  if (!task.id) return
  const existing = simulationTasks.value.findIndex(item => item.id === task.id)
  const next = task as SimulationTaskSummary
  simulationTasks.value = existing >= 0
    ? simulationTasks.value.map(item => item.id === task.id ? { ...item, ...next } : item)
    : [next, ...simulationTasks.value]
}

const loadVerificationTasks = async () => {
  const excludedIds = watchedVerificationTaskIds.value
  const tasks = await boardApi.getTasks(excludedIds)
  verificationTasks.value = mergeTaskSummariesPreservingExcluded(
    verificationTasks.value,
    tasks || [],
    excludedIds
  )
}

const loadSimulationTasks = async () => {
  const excludedIds = watchedSimulationTaskIds.value
  const tasks = await simulationApi.getTasks(excludedIds)
  simulationTasks.value = mergeTaskSummariesPreservingExcluded(
    simulationTasks.value,
    tasks || [],
    excludedIds
  )
}

const loadTaskInbox = async (
  showError = true,
  options: { showLoading?: boolean } = {}
) => {
  const showLoading = options.showLoading ?? true
  if (showLoading) {
    loadingTaskHistory.value = true
  }
  try {
    await Promise.all([loadVerificationTasks(), loadSimulationTasks()])
  } catch (e: any) {
    console.error('Failed to load async tasks:', e)
    if (showError) {
      ElMessage.error({ message: t('app.failedToLoadTasks'), type: 'error' })
    }
  } finally {
    if (showLoading) {
      loadingTaskHistory.value = false
    }
  }
}

const loadVerificationTraces = async () => {
  loadingVerificationHistory.value = true
  try {
    const traces = await boardApi.getVerificationTraces()
    verificationTraces.value = traces || []
  } catch (e: any) {
    console.error('Failed to load verification traces:', e)
    ElMessage.error({ message: t('app.failedToLoadVerificationTraces'), type: 'error' })
  } finally {
    loadingVerificationHistory.value = false
  }
}

const loadSimulationTraces = async () => {
  loadingSimulationHistory.value = true
  try {
    const traces = await simulationApi.getUserSimulations()
    simulationTraces.value = traces || []
  } catch (e: any) {
    console.error('Failed to load simulation traces:', e)
    ElMessage.error({ message: t('app.failedToLoadSimulationHistory'), type: 'error' })
  } finally {
    loadingSimulationHistory.value = false
  }
}

const refreshHistoryTab = async (tab: HistoryTab = activeHistoryTab.value) => {
  if (tab === 'tasks') {
    await loadTaskInbox()
  } else if (tab === 'verification') {
    await loadVerificationTraces()
  } else {
    await loadSimulationTraces()
  }
}

const setHistoryTab = async (tab: HistoryTab) => {
  activeHistoryTab.value = tab
  await refreshHistoryTab(tab)
}

const closeHistoryPanel = () => {
  showHistoryPanel.value = false
}

const toggleHistoryPanel = async (tab: HistoryTab = activeHistoryTab.value) => {
  if (showHistoryPanel.value && activeHistoryTab.value === tab) {
    closeHistoryPanel()
    return
  }

  showSimulationPanel.value = false
  showVerificationPanel.value = false
  closeRecommendationPanel()
  closeDeviceRecommendationPanel()
  closeSpecRecommendationPanel()

  activeHistoryTab.value = tab
  showHistoryPanel.value = true
  await refreshHistoryTab(tab)
}

const deleteVerificationTrace = async (traceId: number) => {
  try {
    await ElMessageBox.confirm(
      t('app.deleteVerificationTraceMessage', { id: traceId }),
      t('app.deleteTraceTitle'),
      {
        confirmButtonText: t('app.delete'),
        cancelButtonText: t('app.cancel'),
        type: 'warning'
      }
    )
    await boardApi.deleteVerificationTrace(traceId)
    verificationTraces.value = verificationTraces.value.filter(t => t.id !== traceId)
    ElMessage.success({ message: t('app.traceDeleted'), type: 'success' })
  } catch (e: any) {
    if (e === 'cancel' || e === 'close') return
    console.error('Failed to delete trace:', e)
    ElMessage.error({ message: t('app.failedToDeleteTrace'), type: 'error' })
  }
}

const openVerificationTaskResult = async (taskId: number) => {
  try {
    const task = await boardApi.getTask(taskId)
    upsertVerificationTaskSummary(task)
    const traces = task.isSafe ? [] : await boardApi.getTaskTraces(taskId)
    verificationResult.value = buildVerificationResultFromTask(task, traces)
    closeHistoryPanel()
  } catch (e: any) {
    console.error('Failed to load verification task:', e)
    ElMessage.error({ message: t('app.failedToLoadTask'), type: 'error' })
  }
}

const openSimulationTaskResult = async (taskId: number) => {
  try {
    const task = await simulationApi.getTask(taskId)
    upsertSimulationTaskSummary(task)
    if (!task.simulationTraceId) {
      ElMessage.warning({ message: t('app.taskCompletedNoTraceFound'), type: 'warning' })
      return
    }
    await selectAndPlaySimulationTrace(task.simulationTraceId)
  } catch (e: any) {
    console.error('Failed to load simulation task:', e)
    ElMessage.error({ message: t('app.failedToLoadTask'), type: 'error' })
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
    status: formatAsyncTaskStatus(taskSummary?.status) || t('app.taskInitializing')
  }
  closeHistoryPanel()
  try {
    await pollAsyncVerification(taskId, { presentResult: true })
  } catch (error: any) {
    if (!isPollingAbortedError(error)) {
      const message = extractApiErrorMessage(error, t('app.verificationFailed'))
      if (verificationCancelRequested.value && message.toLowerCase().includes('cancel')) {
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
    await loadTaskInbox(false, { showLoading: false })
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
    status: formatAsyncTaskStatus(taskSummary?.status) || t('app.taskInitializing')
  }
  closeHistoryPanel()
  try {
    const result = await pollAsyncSimulation(taskId)
    lastSimulationResult.value = result
    if (result.traceId) {
      simulationTraces.value = [
        {
          id: result.traceId,
          requestedSteps: result.requestedSteps,
          steps: result.steps,
          createdAt: result.createdAt || new Date().toISOString()
        },
        ...simulationTraces.value.filter(item => item.id !== result.traceId)
      ]
    }
    if (result.states && result.states.length > 0) {
      if (traceAnimationState.value.visible || simulationAnimationState.value.visible) {
        ElMessage.success({
          message: t('app.simulationTaskCompletedSaved', { count: result.states.length }),
          type: 'success'
        })
        return
      }
      savedSimulationStates.value = [...result.states]
      simulationAnimationState.value = {
        visible: true,
        selectedStateIndex: 0,
        isPlaying: false
      }
      highlightedTrace.value = {
        states: savedSimulationStates.value,
        selectedStateIndex: 0
      }
      ElMessage.success({
        message: t('app.simulationCompletedWithStates', { count: result.states.length }),
        type: 'success'
      })
    }
  } catch (error: any) {
    if (!isPollingAbortedError(error)) {
      const message = extractApiErrorMessage(error, t('app.simulationFailed'))
      if (simulationCancelRequested.value && message.toLowerCase().includes('cancel')) {
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
    await loadTaskInbox(false, { showLoading: false })
  }
}

const cancelVerificationTaskFromInbox = async (taskId: number) => {
  if (asyncVerificationTask.value.taskId === taskId) {
    await cancelAsyncVerification()
  } else {
    const cancelled = await boardApi.cancelTask(taskId)
    ElMessage.info({
      message: cancelled ? t('app.verificationCancellationRequested') : t('app.verificationTaskNotCancellable'),
      type: 'info'
    })
  }
  await loadTaskInbox(false, { showLoading: false })
}

const cancelSimulationTaskFromInbox = async (taskId: number) => {
  if (asyncSimulationTask.value.taskId === taskId) {
    await cancelAsyncSimulation()
  } else {
    const cancelled = await simulationApi.cancelTask(taskId)
    ElMessage.info({
      message: cancelled ? t('app.simulationCancellationRequested') : t('app.simulationTaskNotCancellable'),
      type: 'info'
    })
  }
  await loadTaskInbox(false, { showLoading: false })
}

const openTaskInbox = async () => {
  showSimulationPanel.value = false
  showVerificationPanel.value = false
  closeRecommendationPanel()
  closeDeviceRecommendationPanel()
  closeSpecRecommendationPanel()
  activeHistoryTab.value = 'tasks'
  showHistoryPanel.value = true
  await loadTaskInbox(false)
}

const cancelMiniTask = async (kind: 'verification' | 'simulation', taskId: number) => {
  if (kind === 'verification') {
    await cancelVerificationTaskFromInbox(taskId)
  } else {
    await cancelSimulationTaskFromInbox(taskId)
  }
}

const selectAndPlayVerificationTrace = async (traceId: number) => {
  // Same mutual-exclusion guards as selectAndPlayTrace: a historical trace opens the same animation
  // surface, so it must not stack on top of a running simulation timeline or the recommendations panel.
  const guard = canOpenTracePlayback({
    simulationVisible: simulationAnimationState.value.visible,
    recommendationPanelVisible: showRecommendationPanel.value
  })
  if (!guard.allowed) {
    ElMessage.warning({ message: guard.reason, type: 'warning' })
    return
  }
  try {
    const trace = await boardApi.getVerificationTrace(traceId)
    if (!trace?.states?.length) {
      ElMessage.warning({ message: t('app.traceHasNoStates'), type: 'warning' })
      return
    }
    // Take the animation lock and close the result dialog, mirroring the current-result path so lock
    // state and open panels stay consistent regardless of which entry point started the animation.
    isAnimationLocked.value = true
    closeResultDialog()
    closeHistoryPanel()
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
    console.error('Failed to load trace:', e)
    isAnimationLocked.value = false
    ElMessage.error({ message: t('app.failedToLoadTrace'), type: 'error' })
  }
}

const openFixForVerificationTrace = (trace: Trace) => {
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
  if (showRecommendationPanel.value || showDeviceRecommendationPanel.value || showSpecRecommendationPanel.value) {
    ElMessage.warning({ message: t('app.closeRecommendationPanelsFirst'), type: 'warning' })
    return
  }

  try {
    const trace = await simulationApi.getSimulation(traceId)
    if (!trace?.states?.length) {
      ElMessage.warning({ message: t('app.simulationRunHasNoStates'), type: 'warning' })
      return
    }

    const result = {
      states: trace.states,
      steps: trace.steps,
      requestedSteps: trace.requestedSteps,
      logs: trace.logs || [],
      nusmvOutput: trace.nusmvOutput || ''
    }

    isAnimationLocked.value = true
    closeHistoryPanel()
    lastSimulationResult.value = result
    simulationResult.value = null
    savedSimulationStates.value = [...trace.states]
    simulationAnimationState.value = {
      visible: true,
      selectedStateIndex: 0,
      isPlaying: false
    }
    highlightedTrace.value = {
      states: savedSimulationStates.value,
      selectedStateIndex: 0
    }
  } catch (e: any) {
    console.error('Failed to load simulation trace:', e)
    isAnimationLocked.value = false
    ElMessage.error({ message: t('app.failedToLoadSimulationRun'), type: 'error' })
  }
}

const deleteSimulationTrace = async (traceId: number) => {
  try {
    await ElMessageBox.confirm(
      t('app.deleteSimulationRunMessage', { id: traceId }),
      t('app.deleteSimulationRunTitle'),
      {
        confirmButtonText: t('app.delete'),
        cancelButtonText: t('app.cancel'),
        type: 'warning'
      }
    )
    await simulationApi.deleteSimulation(traceId)
    simulationTraces.value = simulationTraces.value.filter(t => t.id !== traceId)
    ElMessage.success({ message: t('app.simulationRunDeleted'), type: 'success' })
  } catch (e: any) {
    if (e === 'cancel' || e === 'close') return
    console.error('Failed to delete simulation trace:', e)
    ElMessage.error({ message: t('app.failedToDeleteSimulationRun'), type: 'error' })
  }
}

// Floating panel visibility state
const showVerificationPanel = ref(false)

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
    const cancelled = await boardApi.cancelTask(taskId)
    if (cancelled) {
      ElMessage.info({ message: t('app.verificationCancellationRequested'), type: 'info' })
    } else {
      verificationCancelRequested.value = false
      ElMessage.warning({ message: t('app.verificationTaskNotCancellable'), type: 'warning' })
    }
  } catch (error: any) {
    verificationCancelRequested.value = false
    const msg = error?.response?.data?.message || error?.message || t('app.failedToCancelVerificationTask')
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
    const cancelled = await simulationApi.cancelTask(taskId)
    if (cancelled) {
      ElMessage.info({ message: t('app.simulationCancellationRequested'), type: 'info' })
    } else {
      simulationCancelRequested.value = false
      ElMessage.warning({ message: t('app.simulationTaskNotCancellable'), type: 'warning' })
    }
  } catch (error: any) {
    simulationCancelRequested.value = false
    const msg = error?.response?.data?.message || error?.message || t('app.failedToCancelSimulationTask')
    ElMessage.error({ message: msg, type: 'error' })
  } finally {
    cancellingSimulationTask.value = false
  }
}

// Fix 应用后的回调
const handleFixApplied = async () => {
  // 修复已落库到后端规则集，重新拉取规则并重建连线，使画布与后端一致。
  await refreshRules()
}

// 面板互斥切换函数
const togglePanel = (panel: 'simulation' | 'verification') => {
  // 互斥检查：如果 Rule Recommendations 或 Device Recommendations 或 Specification Recommendations 面板正在显示，则不允许打开模拟/验证面板
  if (showRecommendationPanel.value) {
    ElMessage.warning({ message: t('app.closeRuleRecommendationFirst'), type: 'warning' })
    return
  }
  
  if (showDeviceRecommendationPanel.value) {
    ElMessage.warning({ message: t('app.closeDeviceRecommendationFirst'), type: 'warning' })
    return
  }
  
  if (showSpecRecommendationPanel.value) {
    ElMessage.warning({ message: t('app.closeSpecRecommendationFirst'), type: 'warning' })
    return
  }
  closeHistoryPanel()
  
  if (panel === 'simulation') {
    if (showSimulationPanel.value) {
      showSimulationPanel.value = false
    } else {
      showSimulationPanel.value = true
      showVerificationPanel.value = false
    }
  } else {
    if (showVerificationPanel.value) {
      showVerificationPanel.value = false
    } else {
      showVerificationPanel.value = true
      showSimulationPanel.value = false
    }
  }
}

// 模拟时间轴动画状态
const simulationAnimationState = ref({
  visible: false,
  selectedStateIndex: 0,
  isPlaying: false
})

// 独立保存的模拟 states 数据（用于对话框关闭后）
const savedSimulationStates = ref<any[]>([])

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

// 动画互斥锁 - 防止同时打开两个动画
const isAnimationLocked = ref(false)

let playInterval: ReturnType<typeof setInterval> | null = null

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
// (backend TraceDto) rather than the live verificationForm — so a historical trace shows the
// parameters it was actually run under. Falls back to the live form for legacy traces that predate
// the stored snapshot (isAttack undefined).
const activeTraceContext = computed(() => {
  return deriveTraceContext(currentTrace.value, {
    isAttack: verificationForm.isAttack,
    intensity: verificationForm.intensity
  })
})

// 选择并播放指定索引的反例路径动画
const selectAndPlayTrace = (traceIndex: number) => {
  // 互斥检查：如果模拟动画正在显示，则不允许打开反例路径动画
  if (simulationAnimationState.value.visible) {
    ElMessage.warning({ message: t('app.closeCurrentSimulationFirst'), type: 'warning' })
    return
  }
  
  // 互斥检查：如果 Rule Recommendations 面板正在显示，则不允许打开反例路径动画
  if (showRecommendationPanel.value) {
    ElMessage.warning({ message: t('app.closeRuleRecommendationFirst'), type: 'warning' })
    return
  }
  
  if (verificationResult.value?.traces?.length > 0 && traceIndex < verificationResult.value.traces.length) {
    // 设置互斥锁
    isAnimationLocked.value = true
    
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
  // 重置互斥锁
  isAnimationLocked.value = false
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
  void nextTick(() => {
    document.querySelector<HTMLButtonElement>(`[data-testid="trace-timeline-state-${nextIndex}"]`)?.focus()
  })
}

const getTraceStateAriaLabel = (index: number) => {
  return `${t('app.traceVisualization.state', { index: index + 1 })} (${index + 1}/${totalStates.value})`
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
  
  traceAnimationState.value.isPlaying = true
  playInterval = setInterval(() => {
    const trace = currentTrace.value
    if (!trace) {
      stopTraceAnimation()
      return
    }
    if (traceAnimationState.value.selectedStateIndex < totalStates.value - 1) {
      traceAnimationState.value.selectedStateIndex++
      highlightedTrace.value = {
        ...trace,
        selectedStateIndex: traceAnimationState.value.selectedStateIndex
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

// 格式化规约为易读格式
const formatSpec = (specJson: string): string => {
  try {
    const spec = JSON.parse(specJson)
    
    //: Always □(condition)
    if (spec.templateId === '1' && spec.aConditions) {
      const conditions = spec.aConditions.map((c: any) => {
        const device = c.deviceId || c.deviceLabel || 'device'
        const key = c.key || ''
        const relation = formatRelation(c.relation)
        const value = c.value ? `"${c.value}"` : ''
        return `${device}_${key} ${relation} ${value}`.trim()
      }).join(' ∧ ')
      return `□(${conditions})`
    }
    
    // Response: □(A → ◇B)
    if (spec.templateId === '5') {
      const ifPart = spec.ifConditions?.map((c: any) => 
        `${c.deviceId}_${c.key} ${formatRelation(c.relation)} "${c.value}"`
      ).join(' ∧ ') || ''
      const thenPart = spec.thenConditions?.map((c: any) => 
        `${c.deviceId}_${c.key} = "${c.value}"`
      ).join(' ∧ ') || ''
      return `□(${ifPart} → ◇(${thenPart}))`
    }
    
    return spec.templateLabel || 'Spec'
  } catch {
    return specJson
  }
}

const formatRelation = (relation: string): string => {
  const relations: Record<string, string> = {
    '=': '=',
    '!=': '≠',
    '>': '>',
    '<': '<',
    '>=': '≥',
    '<=': '≤'
  }
  return relations[relation] || relation
}

// 当前规约的格式化显示
const formattedSpec = computed(() => {
  if (!currentTrace.value?.violatedSpecJson) return ''
  return formatSpec(currentTrace.value.violatedSpecJson)
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
  
  // 互斥检查：如果 Rule Recommendations 面板正在显示，则不允许打开模拟动画
  if (showRecommendationPanel.value) {
    ElMessage.warning({ message: t('app.closeRuleRecommendationFirst'), type: 'warning' })
    return
  }
  
  if (simulationResult.value?.states?.length > 0) {
    // 设置互斥锁
    isAnimationLocked.value = true
    
    // 保存模拟 states 数据到独立变量
    savedSimulationStates.value = [...simulationResult.value.states]
    
    // 关闭模拟结果对话框
    simulationResult.value = null
    
    // 打开模拟时间轴动画
    simulationAnimationState.value = {
      visible: true,
      selectedStateIndex: 0,
      isPlaying: false
    }
    
    // 高亮第一个状态
    highlightedTrace.value = {
      states: savedSimulationStates.value,
      selectedStateIndex: 0
    }
  }
}

// 关闭模拟时间轴动画
const closeSimulationTimeline = () => {
  stopSimulationAnimation()
  simulationAnimationState.value.visible = false
  highlightedTrace.value = null
  // 重置互斥锁
  isAnimationLocked.value = false
}

// 处理 SimulationTimeline 组件的关闭事件
const handleSimulationTimelineClose = (visible: boolean) => {
  if (!visible) {
    closeSimulationTimeline()
  }
}

// 跳转到指定状态
// 播放/停止模拟动画
let simulationPlayInterval: ReturnType<typeof setInterval> | null = null

const stopSimulationAnimation = () => {
  simulationAnimationState.value.isPlaying = false
  if (simulationPlayInterval) {
    clearInterval(simulationPlayInterval)
    simulationPlayInterval = null
  }
}

const handleVerify = async (): Promise<boolean> => {
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
      rules: rules.value,
      specifications: specifications.value,
      resolveNodeLabel,
      isAttack: verificationForm.isAttack,
      intensity: verificationForm.intensity,
      enablePrivacy: verificationForm.enablePrivacy
    })

    // Handle async or sync verification
    if (verificationForm.isAsync) {
      // Async verification. IMPORTANT: await the polling promise so the outer `finally`
      // (which sets isVerifying=false) only runs after polling truly ends — otherwise
      // the progress UI vanishes immediately and the button re-enables mid-run,
      // letting the user launch duplicate tasks.
      asyncVerificationActive.value = true
      asyncVerificationTask.value = { taskId: null, progress: 0, status: t('app.taskInitializing') }

      const taskId = await boardApi.verifyAsync(req)
      asyncVerificationTask.value.taskId = taskId
      asyncVerificationTask.value.status = t('app.verificationRunning')
      upsertVerificationTaskSummary({
        id: taskId,
        status: 'PENDING',
        createdAt: new Date().toISOString(),
        progress: 0
      })

      await pollAsyncVerification(taskId)
      return true
    }

    // Sync verification (original logic)
    const result = await boardApi.verify(req)
    verificationResult.value = {
      ...result,
      specResults: normalizeSpecResults((result as any).specResults)
    }
    notifyVerificationOutcome(verificationResult.value)
    return true

  } catch (error: any) {
    if (isPollingAbortedError(error)) {
      return false
    }
    const message = extractApiErrorMessage(error, t('app.verificationFailed'))
    if (verificationCancelRequested.value && message.toLowerCase().includes('cancel')) {
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
    showVerificationPanel.value = false
  }
}

// Run simulation with proper panel handling
const runSimulation = async () => {
  await handleSimulate({ ...simulationForm })
}

const handleSimulate = async (simConfig: {
  steps: number
  isAttack: boolean
  intensity: number
  enablePrivacy: boolean
  isAsync: boolean
  saveToHistory?: boolean
}): Promise<boolean> => {
  if (nodes.value.length === 0) {
    ElMessage.warning({ message: t('app.noDevicesToSimulate'), type: 'warning' })
    return false
  }
  if (!assertRulesHaveTriggers(rules.value)) {
    return false
  }

  isSimulating.value = true
  asyncSimulationActive.value = false
  simulationCancelRequested.value = false
  cancellingSimulationTask.value = false
  simulationError.value = null
  simulationResult.value = null

  // 重置异步任务状态
  if (simConfig.isAsync) {
    asyncSimulationActive.value = true
    asyncSimulationTask.value = { taskId: null, progress: 0, status: t('app.taskInitializing') }
  }

  try {
    const req = buildSimulationRequestPayload({
      nodes: nodes.value,
      deviceTemplates: deviceTemplates.value,
      rules: rules.value,
      resolveNodeLabel,
      steps: simConfig.steps,
      isAttack: simConfig.isAttack,
      intensity: simConfig.intensity,
      enablePrivacy: simConfig.enablePrivacy
    })
    
    let result: any

    if (simConfig.isAsync) {
      // 异步模拟：创建任务并轮询进度
      const taskId = await simulationApi.simulateAsync(req)
      asyncSimulationTask.value.taskId = taskId
      asyncSimulationTask.value.status = t('app.simulationTaskCreatedWaiting')
      upsertSimulationTaskSummary({
        id: taskId,
        status: 'PENDING',
        createdAt: new Date().toISOString(),
        progress: 0,
        requestedSteps: req.steps,
        steps: 0
      })

      // 轮询任务进度
      result = await pollAsyncSimulation(taskId)
    } else {
      // 同步模拟
      if (simConfig.saveToHistory) {
        const trace = await simulationApi.simulateAndSave(req)
        result = {
          traceId: trace.id,
          states: trace.states,
          steps: trace.steps,
          requestedSteps: trace.requestedSteps,
          createdAt: trace.createdAt,
          logs: trace.logs || [],
          nusmvOutput: trace.nusmvOutput || ''
        }
      } else {
        result = await simulationApi.simulate(req)
      }
    }
    
    // Keep the full result so its logs / raw NuSMV output remain reachable from the timeline via
    // openSimulationLogs(); the success path opens the timeline (below), not the result dialog.
    lastSimulationResult.value = result
    if (result.traceId) {
      simulationTraces.value = [
        {
          id: result.traceId,
          requestedSteps: result.requestedSteps,
          steps: result.steps,
          createdAt: result.createdAt || new Date().toISOString()
        },
        ...simulationTraces.value.filter(item => item.id !== result.traceId)
      ]
    }

    // 直接打开时间轴动画，不显示结果对话框
    if (result.states && result.states.length > 0) {
      if (simConfig.isAsync) {
        ElMessage.success({
          message: t('app.simulationTaskCompletedSaved', { count: result.states.length }),
          type: 'success'
        })
        return true
      }

      // 保存模拟 states 数据
      savedSimulationStates.value = [...result.states]

      // 关闭模拟配置面板
      showSimulationPanel.value = false
      
      // 打开模拟时间轴动画
      simulationAnimationState.value = {
        visible: true,
        selectedStateIndex: 0,
        isPlaying: false
      }
      
      // 高亮第一个状态
      highlightedTrace.value = {
        states: savedSimulationStates.value,
        selectedStateIndex: 0
      }
      
      ElMessage.success({
        message: t('app.simulationCompletedWithStates', { count: result.states.length }),
        type: 'success'
      })
      return true
    } else {
      ElMessage.warning({
        message: t('app.simulationCompletedNoStates'),
        type: 'warning'
      })
      return false
    }

  } catch (error: any) {
    if (isPollingAbortedError(error)) {
      return false
    }
    const message = extractApiErrorMessage(error, t('app.simulationFailed'))
    if (simulationCancelRequested.value && message.toLowerCase().includes('cancel')) {
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

// Open the result dialog for the last successful simulation on demand, so its execution logs and raw
// NuSMV output are reachable even though the success path goes straight to the timeline.
const openSimulationLogs = () => {
  if (!lastSimulationResult.value) {
    ElMessage.info({ message: t('app.noSimulationLogsAvailable'), type: 'info' })
    return
  }
  simulationResult.value = lastSimulationResult.value
}

// A status/progress fetch error is "permanent" (fail fast, don't retry to timeout) when
// it is an auth/not-found/client error — retrying will never succeed. Network blips and
// 5xx are treated as transient.
const isPermanentPollError = (error: any): boolean => {
  const status = error?.response?.status
  return typeof status === 'number' && status >= 400 && status < 500
}

// 轮询异步验证任务：await 到终态/超时/永久错误为止，供 handleVerify await。
// 用 while + await sleep（而非 setInterval + async 回调）：串行执行，天然无重入——
// 若某次状态查询超过 1s 也不会并发发起下一轮、不会重复 toast 或旧响应覆盖新进度。
const pollAsyncVerification = async (
  taskId: number,
  options: { presentResult?: boolean } = {}
): Promise<void> => {
  let pollCount = 0

  while (pollCount < ASYNC_TASK_MAX_POLLS) {
    throwIfPollingAborted()
    let task: VerificationTask
    try {
      const progress = await boardApi.getTaskProgress(taskId)
      throwIfPollingAborted()
      asyncVerificationTask.value.progress = normalizeTaskProgress(progress)
      task = await boardApi.getTask(taskId)
      throwIfPollingAborted()
      asyncVerificationTask.value.status = formatAsyncTaskStatus(task.status)
      upsertVerificationTaskSummary(task)
    } catch (e: any) {
      if (isPollingAbortedError(e)) {
        throw e
      }
      // Permanent errors (401/403/404/…) fail fast; transient errors retry.
      if (isPermanentPollError(e)) {
        throw new Error(e?.message || 'Failed to get verification status')
      }
      await waitForNextPoll()
      pollCount++
      continue
    }

    // Terminal-state handling outside the try so its logic isn't swallowed by the catch.
    if (task.status === 'COMPLETED') {
      const traces = task.isSafe ? [] : await boardApi.getTaskTraces(taskId)
      throwIfPollingAborted()
      const result = buildVerificationResultFromTask(task, traces)
      upsertVerificationTaskSummary({ ...task, progress: 100 })
      if (options.presentResult || showVerificationPanel.value) {
        verificationResult.value = result
        notifyVerificationOutcome(verificationResult.value)
        showVerificationPanel.value = false
      } else if (result.safe) {
        ElMessage.success({ message: t('app.verificationTaskCompletedSafe'), type: 'success' })
      } else {
        ElMessage.warning({ message: getVerificationFailureMessage(result), type: 'warning' })
      }
      await loadVerificationTraces()
      return
    } else if (task.status === 'FAILED' || task.status === 'CANCELLED') {
      throw new Error(task.errorMessage || t('app.verificationFailed'))
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
    let task: any
    try {
      // 获取任务进度 + 状态（瞬时网络错误容忍：进入 catch 后继续轮询）
      const progress = await simulationApi.getTaskProgress(taskId)
      throwIfPollingAborted()
      asyncSimulationTask.value.progress = normalizeTaskProgress(progress)

      task = await simulationApi.getTask(taskId)
      throwIfPollingAborted()
      asyncSimulationTask.value.status = formatAsyncTaskStatus(task.status)
      upsertSimulationTaskSummary(task)
    } catch (error: any) {
      if (isPollingAbortedError(error)) {
        throw error
      }
      // Permanent errors (401/403/404/task-not-found) fail fast; only transient
      // errors (network blips, 5xx) retry until the poll ceiling.
      if (isPermanentPollError(error)) {
        throw new Error(error?.message || t('app.failedToGetSimulationStatus'))
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
        await loadSimulationTraces()
        return {
          traceId: trace.id,
          states: trace.states,
          steps: trace.steps,
          requestedSteps: trace.requestedSteps,
          createdAt: trace.createdAt,
          logs: trace.logs || [],
          nusmvOutput: trace.nusmvOutput
        }
      }
      upsertSimulationTaskSummary({ ...task, progress: 100 })
      return { states: [], steps: 0, requestedSteps: 0, logs: [t('app.taskCompletedNoTraceFound')] }
    } else if (task.status === 'FAILED') {
      throw new Error(task.errorMessage || t('app.asyncSimulationFailed'))
    } else if (task.status === 'CANCELLED') {
      throw new Error(t('app.simulationTaskCancelledByServer'))
    }

    // 仍在 PENDING/RUNNING，等待后继续
    await waitForNextPoll()
    pollCount++
  }

  // 超出最大轮询次数
  throw new Error(t('app.simulationTimeout'))
}

// ==== Results Dialog ====
const showResultDialog = computed(() => !!verificationResult.value || !!verificationError.value)
const verificationGenerationWarningCounts = computed(() => getGenerationWarningCounts(verificationResult.value))
const verificationCheckLogs = computed(() => verificationResult.value?.checkLogs || [])
const verificationSpecResultSummary = computed(() => {
  const results = normalizeSpecResults(verificationResult.value?.specResults)
  const passed = results.filter(result => result.passed).length
  return {
    results,
    total: results.length,
    passed,
    failed: results.length - passed
  }
})
const verificationViolationCount = computed(() =>
  Math.max(verificationSpecResultSummary.value.failed, verificationResult.value?.traces?.length || 0)
)
const verificationUnsafeDetail = computed(() =>
  verificationViolationCount.value > 0
    ? t('app.foundViolations', { count: verificationViolationCount.value })
    : t('app.verificationResultUnreliable')
)

const closeResultDialog = () => {
  verificationResult.value = null
  verificationError.value = null
}
</script>

<template>
  <!-- [Fix] @wheel.ctrl.prevent 阻止浏览器原生缩放 -->
  <div
    class="iot-board"
    data-testid="board-root"
    :style="boardShellStyle"
    @wheel.ctrl.prevent="onBoardWheel"
  >
    <!-- Navigation Bar - 与首页风格一致 -->
    <nav class="board-nav-bar">
      <div class="nav-content">
        <div class="logo-left" @click="router.push('/board')">
          IoT-Verify<sup class="logo-sup">®</sup>
        </div>

        <div class="nav-actions">
          <ThemeToggle tone="dark" compact />
          <LanguageToggle tone="dark" compact />
          <button class="nav-action-btn ai-assistant-btn" @click="toggleChat">
            <span class="material-symbols-outlined">smart_toy</span>
            <span>{{ t('app.aiAssistant') }}</span>
          </button>
          <button class="nav-logout-btn" @click="handleLogout">
            <span class="material-symbols-outlined">logout</span>
          </button>
        </div>
      </div>
    </nav>

    <!-- Logout Confirmation Dialog -->
    <LogoutConfirmDialog
      v-model:visible="showLogoutDialog"
      @confirm="handleLogoutConfirm"
      @cancel="handleLogoutCancel"
    />

    <!-- Left Sidebar - Control Center -->
    <ControlCenter
      :device-templates="deviceTemplates"
      :nodes="nodes"
      :edges="edges"
      :canvas-pan="canvasPan"
      :canvas-zoom="canvasZoom"
      :collapsed="boardPanels.control.collapsed"
      :width="boardPanels.control.width"
      :active-section="boardPanels.control.activeSection"
      @create-device="handleCreateDevice"
      @open-rule-builder="openRuleBuilder"
      @add-spec="handleAddSpec"
      @refresh-templates="refreshDeviceTemplates"
      @delete-template="handleDeleteTemplate"
      @update:collapsed="boardPanels.control.collapsed = $event"
      @update:active-section="boardPanels.control.activeSection = $event"
    />

    <!-- Right Sidebar - System Inspector -->
    <SystemInspector
      :devices="nodes"
      :rules="rules"
      :edges="edges"
      :specifications="specifications"
      :collapsed="boardPanels.inspector.collapsed"
      :width="boardPanels.inspector.width"
      :active-section="boardPanels.inspector.activeSection"
      @delete-device="deleteNodeFromStatus"
      @delete-rule="deleteRule"
      @delete-spec="deleteSpecification"
      @device-click="onDeviceListClick"
      @open-rule-builder="openRuleBuilder"
      @open-control-section="openControlSection"
      @update:collapsed="boardPanels.inspector.collapsed = $event"
      @update:active-section="boardPanels.inspector.activeSection = $event"
    />

    <!-- Canvas Area -->
    <div class="canvas-container">
      <!-- Canvas Board -->
      <CanvasBoard
          :nodes="nodes"
          :edges="allEdges"
          :pan="canvasPan"
          :zoom="canvasZoom"
          :get-node-icon="getNodeIcon"
          :get-node-label-style="getNodeLabelStyle"
          :highlighted-trace="highlightedTrace"
          @canvas-pointerdown="onCanvasPointerDown"
          @canvas-dragover="onCanvasDragOver"
          @canvas-drop="onCanvasDrop"
          @canvas-enter="onCanvasEnter"
          @canvas-leave="onCanvasLeave"
          @node-context="onNodeContext"
          @node-keyboard-context="onNodeKeyboardContext"
          @node-open="openNodeFromCanvas"
          @node-delete="deleteNodeFromStatus"
          @node-moved-or-resized="handleNodeMovedOrResized"
      />

    </div>

    <!-- Floating Action Rail - Left of System Inspector -->
    <div
      class="board-floating-actions fixed top-20 z-40 flex flex-col"
      role="toolbar"
      :aria-label="t('app.boardTools')"
    >
      <div class="board-tool-group" data-testid="run-tool-group" role="group" :aria-label="t('app.runTools')">
        <span class="board-tool-group-label">{{ t('app.runTools') }}</span>

        <div class="board-tool-wrapper group">
          <div
            v-if="simulationAnimationState.visible"
            class="board-tool-pulse bg-blue-400"
          ></div>
          <button
            type="button"
            @click="togglePanel('simulation')"
            data-testid="open-simulation-panel"
            :disabled="traceAnimationState.visible || simulationAnimationState.visible || showRecommendationPanel || showDeviceRecommendationPanel || showSpecRecommendationPanel"
            :aria-label="isSimulating ? t('app.simulationRunning') : t('app.openSimulationSettings')"
            :aria-pressed="showSimulationPanel || simulationAnimationState.visible"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              (traceAnimationState.visible || simulationAnimationState.visible || showRecommendationPanel || showDeviceRecommendationPanel || showSpecRecommendationPanel)
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
          <div
            v-if="traceAnimationState.visible"
            class="board-tool-pulse bg-green-400"
          ></div>
          <button
            type="button"
            @click="togglePanel('verification')"
            data-testid="open-verification-panel"
            :disabled="traceAnimationState.visible || simulationAnimationState.visible || showRecommendationPanel || showDeviceRecommendationPanel || showSpecRecommendationPanel"
            :aria-label="isVerifying ? t('app.verifying') : t('app.openVerificationSettings')"
            :aria-pressed="showVerificationPanel || traceAnimationState.visible"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              (traceAnimationState.visible || simulationAnimationState.visible || showRecommendationPanel || showDeviceRecommendationPanel || showSpecRecommendationPanel)
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
            @click="toggleHistoryPanel()"
            data-testid="open-history-panel"
            :aria-label="t('app.openRunHistory')"
            :aria-pressed="showHistoryPanel"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              showHistoryPanel ? 'bg-cyan-700' : 'bg-cyan-600 hover:bg-cyan-700'
            ]"
            :title="t('app.openRunHistory')"
          >
            <span class="material-symbols-outlined" aria-hidden="true">history</span>
            <span class="board-tool-label">{{ t('app.runHistory') }}</span>
            <span class="board-tool-tooltip" role="tooltip">{{ t('app.openRunHistory') }}</span>
          </button>
        </div>
      </div>

      <div class="board-tool-separator" aria-hidden="true"></div>

      <div class="board-tool-group" data-testid="ai-tool-group" role="group" :aria-label="t('app.aiTools')">
        <span class="board-tool-group-label">{{ t('app.aiTools') }}</span>

        <div class="board-tool-wrapper group">
          <div
            v-if="isRecommendingRules"
            class="board-tool-pulse bg-amber-400"
          ></div>
          <button
            type="button"
            @click="fetchRuleRecommendations"
            data-testid="open-rule-recommendations"
            :disabled="!isRecommendingRules && (traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || showDeviceRecommendationPanel || showSpecRecommendationPanel)"
            :aria-label="isRecommendingRules ? t('app.stopRuleRecommendations') : t('app.openRuleRecommendations')"
            :aria-pressed="showRecommendationPanel || isRecommendingRules"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              (!isRecommendingRules && (traceAnimationState.visible || simulationAnimationState.visible || isAnimationLocked || showDeviceRecommendationPanel || showSpecRecommendationPanel))
                ? 'bg-amber-300 cursor-not-allowed disabled:hover:scale-100'
                : isRecommendingRules
                  ? 'bg-red-500 hover:bg-red-600'
                  : 'bg-amber-500 hover:bg-amber-600'
            ]"
            :title="isRecommendingRules ? t('app.stopRuleRecommendations') : t('app.openRuleRecommendations')"
          >
            <span v-if="isRecommendingRules" class="material-symbols-outlined" aria-hidden="true">stop</span>
            <span v-else class="material-symbols-outlined" aria-hidden="true">rule_settings</span>
            <span class="board-tool-label">{{ t('app.rulesTool') }}</span>
            <span class="board-tool-tooltip" role="tooltip">
              {{ isRecommendingRules ? t('app.stopRuleRecommendations') : t('app.openRuleRecommendations') }}
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
            @click="fetchDeviceRecommendations"
            data-testid="open-device-recommendations"
            :disabled="!isRecommendingDevices && (traceAnimationState.visible || simulationAnimationState.visible || showRecommendationPanel || isAnimationLocked || showSpecRecommendationPanel)"
            :aria-label="isRecommendingDevices ? t('app.stopDeviceRecommendations') : t('app.openDeviceRecommendations')"
            :aria-pressed="showDeviceRecommendationPanel || isRecommendingDevices"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              (!isRecommendingDevices && (traceAnimationState.visible || simulationAnimationState.visible || showRecommendationPanel || isAnimationLocked || showSpecRecommendationPanel))
                ? 'bg-purple-300 cursor-not-allowed disabled:hover:scale-100'
                : isRecommendingDevices
                  ? 'bg-red-500 hover:bg-red-600'
                  : 'bg-purple-500 hover:bg-purple-600'
            ]"
            :title="isRecommendingDevices ? t('app.stopDeviceRecommendations') : t('app.openDeviceRecommendations')"
          >
            <span v-if="isRecommendingDevices" class="material-symbols-outlined" aria-hidden="true">stop</span>
            <span v-else class="material-symbols-outlined" aria-hidden="true">devices_other</span>
            <span class="board-tool-label">{{ t('app.devicesTool') }}</span>
            <span class="board-tool-tooltip" role="tooltip">
              {{ isRecommendingDevices ? t('app.stopDeviceRecommendations') : t('app.openDeviceRecommendations') }}
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
            @click="fetchSpecRecommendations"
            data-testid="open-spec-recommendations"
            :disabled="!isRecommendingSpecs && (traceAnimationState.visible || simulationAnimationState.visible || showRecommendationPanel || showDeviceRecommendationPanel || isAnimationLocked || showSpecRecommendationPanel)"
            :aria-label="isRecommendingSpecs ? t('app.stopSpecificationRecommendations') : t('app.openSpecificationRecommendations')"
            :aria-pressed="showSpecRecommendationPanel || isRecommendingSpecs"
            :class="[
              'board-tool-button text-white shadow-lg hover:shadow-xl transition-all hover:scale-[1.03] active:scale-95',
              (!isRecommendingSpecs && (traceAnimationState.visible || simulationAnimationState.visible || showRecommendationPanel || showDeviceRecommendationPanel || isAnimationLocked || showSpecRecommendationPanel))
                ? 'bg-red-300 cursor-not-allowed disabled:hover:scale-100'
                : 'bg-red-500 hover:bg-red-600'
            ]"
            :title="isRecommendingSpecs ? t('app.stopSpecificationRecommendations') : t('app.openSpecificationRecommendations')"
          >
            <span v-if="isRecommendingSpecs" class="material-symbols-outlined" aria-hidden="true">stop</span>
            <span v-else class="material-symbols-outlined" aria-hidden="true">playlist_add_check</span>
            <span class="board-tool-label">{{ t('app.specificationsTool') }}</span>
            <span class="board-tool-tooltip" role="tooltip">
              {{ isRecommendingSpecs ? t('app.stopSpecificationRecommendations') : t('app.openSpecificationRecommendations') }}
            </span>
          </button>
        </div>
      </div>
    </div>

    <TraceHistoryPanel
      v-if="showHistoryPanel"
      :active-tab="activeHistoryTab"
      :verification-tasks="verificationTasks"
      :simulation-tasks="simulationTasks"
      :verification-traces="verificationTraces"
      :simulation-traces="simulationTraces"
      :loading-tasks="loadingTaskHistory"
      :loading-verification="loadingVerificationHistory"
      :loading-simulation="loadingSimulationHistory"
      :action-locked="historyActionLocked"
      @update:active-tab="setHistoryTab"
      @close="closeHistoryPanel"
      @refresh-tasks="loadTaskInbox"
      @refresh-verification="loadVerificationTraces"
      @refresh-simulation="loadSimulationTraces"
      @watch-verification-task="watchVerificationTask"
      @watch-simulation-task="watchSimulationTask"
      @view-verification-task="openVerificationTaskResult"
      @view-simulation-task="openSimulationTaskResult"
      @cancel-verification-task="cancelVerificationTaskFromInbox"
      @cancel-simulation-task="cancelSimulationTaskFromInbox"
      @view-verification="selectAndPlayVerificationTrace"
      @fix-verification="openFixForVerificationTrace"
      @delete-verification="deleteVerificationTrace"
      @view-simulation="selectAndPlaySimulationTrace"
      @delete-simulation="deleteSimulationTrace"
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
                {{ task.label }} #{{ task.id }}
              </div>
              <div class="truncate text-[11px] text-slate-500">
                {{ task.status }}
              </div>
            </div>
            <button
              type="button"
              class="inline-flex h-7 w-7 shrink-0 items-center justify-center rounded-md text-slate-500 hover:bg-red-50 hover:text-red-600"
              :title="task.kind === 'verification' ? t('app.cancelVerificationTask') : t('app.cancelSimulationTask')"
              @click="cancelMiniTask(task.kind, task.id)"
            >
              <span class="material-symbols-outlined text-sm">cancel</span>
            </button>
          </div>
          <div class="mt-2 h-1.5 overflow-hidden rounded-full bg-slate-200">
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

    <!-- Verification Panel -->
    <div 
      v-if="showVerificationPanel"
      data-testid="verification-panel"
      class="board-floating-panel board-surface-panel fixed top-20 z-30 w-72 max-w-[calc(100vw-2rem)] rounded-2xl shadow-2xl border overflow-hidden"
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
              <h3 class="text-black font-bold text-base">{{ t('app.verification') }}</h3>
              <p class="text-green-900/80 text-xs">{{ t('app.configureAndRunVerification') }}</p>
            </div>
          </div>
          <button 
            @click="showVerificationPanel = false"
            data-testid="close-verification-panel"
            class="w-8 h-8 flex items-center justify-center rounded-lg text-black/70 hover:text-black hover:bg-black/10 transition-all"
          >
            <span class="material-symbols-outlined">close</span>
          </button>
        </div>
      </div>
      <!-- Verification Options -->
      <div class="p-3 space-y-3 bg-gradient-to-b from-white to-green-50/30">
        <!-- Attack Mode -->
        <div class="flex items-center justify-between p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
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
            :disabled="isVerifying"
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

        <!-- Intensity (visible when attack is enabled) -->
        <div v-if="verificationForm.isAttack" class="p-3 bg-red-50 rounded-xl border border-red-200/60">
          <label class="block text-[10px] font-bold text-red-700 uppercase tracking-wide mb-2">
            {{ t('app.attackIntensity') }}: <span class="text-red-500">{{ verificationForm.intensity }}</span>
          </label>
          <input
            v-model.number="verificationForm.intensity"
            :disabled="isVerifying"
            type="range"
            min="0"
            max="50"
            class="w-full h-2 bg-red-200 rounded-lg appearance-none cursor-pointer accent-red-500 disabled:cursor-not-allowed disabled:opacity-60"
          />
          <div class="flex justify-between text-[10px] text-red-400 mt-1">
            <span>{{ t('app.weak') }}</span>
            <span>{{ t('app.strong') }}</span>
          </div>
        </div>

        <!-- Privacy Analysis -->
        <div class="flex items-center justify-between p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
          <div class="flex items-center gap-3">
            <div class="w-8 h-8 bg-purple-100 rounded-lg flex items-center justify-center">
              <span class="material-symbols-outlined text-purple-500 text-lg">security</span>
            </div>
            <label class="text-xs font-bold text-slate-700 uppercase tracking-wide">
              {{ t('app.privacyAnalysis') }}
            </label>
          </div>
          <button
            type="button"
            :disabled="isVerifying"
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
          :disabled="isVerifying"
          class="w-full py-2.5 bg-green-600 hover:bg-green-700 disabled:bg-green-300 text-white rounded-lg text-xs font-bold uppercase tracking-wider transition-all shadow-md hover:shadow-lg hover:scale-[1.02] active:scale-[0.98] flex items-center justify-center gap-2 disabled:cursor-not-allowed disabled:hover:scale-100"
        >
          <template v-if="isVerifying">
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

    <!-- Rule Recommendation Panel -->
    <div 
      v-if="showRecommendationPanel"
      data-testid="rule-recommendation-panel"
      class="board-floating-panel board-surface-panel fixed top-20 z-30 w-96 max-w-[calc(100vw-2rem)] rounded-2xl shadow-2xl border overflow-hidden"
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
            @click="closeRecommendationPanel"
            data-testid="close-rule-recommendations"
            class="w-8 h-8 flex items-center justify-center rounded-lg text-black/70 hover:text-black hover:bg-black/10 transition-all"
          >
            <span class="material-symbols-outlined">close</span>
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

        <!-- Loading State -->
        <div v-if="isRecommendingRules" class="flex flex-col items-center justify-center py-10">
          <div class="relative">
            <span class="material-symbols-outlined text-amber-500 text-5xl animate-spin">sync</span>
            <div class="absolute inset-0 bg-amber-400 rounded-full animate-ping opacity-20"></div>
          </div>
          <p class="text-slate-600 text-sm mt-4 font-medium">{{ t('app.analyzingDevices') }}</p>
          <p class="text-slate-400 text-xs mt-1">{{ t('app.generatingAutomationRules') }}</p>
        </div>

        <!-- Empty State -->
        <div v-else-if="ruleRecommendations.length === 0" class="flex flex-col items-center justify-center py-10">
          <div class="w-16 h-16 bg-slate-100 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-slate-300 text-3xl">psychology</span>
          </div>
          <p class="text-slate-600 text-sm font-medium mt-2">{{ t('app.noRecommendationsAvailable') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.addMoreDevicesForAutomation') }}</p>
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
              {{ t('app.refresh') }}
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
                    <h4 class="text-sm font-bold text-slate-800">{{ t('app.automationRule') }}</h4>
                    <p class="text-xs text-slate-500 break-words">{{ rec.description || t('app.noDescription') }}</p>
                  </div>
                </div>
                <!-- Confidence Badge -->
                <div v-if="rec.confidence" class="px-2 py-1 bg-amber-100 rounded-full">
                  <span class="text-xs font-medium text-amber-700">{{ Math.round(rec.confidence * 100) }}%</span>
                </div>
              </div>
            </div>

            <!-- Reason -->
            <div class="px-3 pb-2">
              <p class="text-xs text-slate-600 break-words">
                {{ rec.category ? t('app.categoryWithValue', { value: rec.category }) : t('app.aiGeneratedAutomationRule') }}
              </p>
            </div>

            <!-- Action Button -->
            <div class="px-3 pb-3">
              <button 
                @click="applyRecommendation(rec)"
                class="w-full py-2 px-4 bg-amber-500 hover:bg-amber-600 text-white text-sm font-medium rounded-lg transition-colors flex items-center justify-center gap-2"
              >
                <span class="material-symbols-outlined text-sm">add</span>
                {{ t('app.applyThisRule') }}
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
      class="board-floating-panel board-surface-panel fixed top-20 z-30 w-96 max-w-[calc(100vw-2rem)] rounded-2xl shadow-2xl border overflow-hidden"
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
            @click="closeDeviceRecommendationPanel"
            data-testid="close-device-recommendations"
            class="w-8 h-8 flex items-center justify-center rounded-lg text-black/70 hover:text-black hover:bg-black/10 transition-all"
          >
            <span class="material-symbols-outlined">close</span>
          </button>
        </div>
      </div>

      <!-- Recommendation Content -->
      <div class="p-3 space-y-3 bg-gradient-to-b from-white to-purple-50/30 max-h-[500px] overflow-y-auto">
        <!-- Loading State -->
        <div v-if="isRecommendingDevices" class="flex flex-col items-center justify-center py-10">
          <div class="relative">
            <span class="material-symbols-outlined text-purple-500 text-5xl animate-spin">sync</span>
            <div class="absolute inset-0 bg-purple-400 rounded-full animate-ping opacity-20"></div>
          </div>
          <p class="text-slate-600 text-sm mt-4 font-medium">{{ t('app.analyzingBoard') }}</p>
          <p class="text-slate-400 text-xs mt-1">{{ t('app.findingCompatibleDevices') }}</p>
        </div>

        <!-- Empty State -->
        <div v-else-if="deviceRecommendations.length === 0" class="flex flex-col items-center justify-center py-10">
          <div class="w-16 h-16 bg-slate-100 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-slate-300 text-3xl">devices</span>
          </div>
          <p class="text-slate-600 text-sm font-medium mt-2">{{ t('app.noRecommendationsAvailable') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.addMoreDevicesForDevices') }}</p>
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
              {{ t('app.refresh') }}
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
                    <h4 class="text-sm font-bold text-slate-800 truncate" :title="rec.templateName">{{ rec.templateName }}</h4>
                    <p class="text-xs text-slate-500 break-words">{{ rec.description || t('app.noDescription') }}</p>
                  </div>
                </div>
                <!-- Confidence Badge -->
                <div v-if="rec.confidence" class="px-2 py-1 bg-purple-100 rounded-full">
                  <span class="text-xs font-medium text-purple-700">{{ Math.round(rec.confidence * 100) }}%</span>
                </div>
              </div>
            </div>

            <!-- Reason -->
            <div class="px-3 pb-2">
              <p class="text-xs text-slate-600 break-words">{{ rec.reason || t('app.recommendedBasedOnCurrentDevices') }}</p>
            </div>

            <!-- Action Button -->
            <div class="px-3 pb-3">
              <button 
                @click="applyDeviceRecommendation(rec)"
                class="w-full py-2 px-4 bg-purple-500 hover:bg-purple-600 text-white text-sm font-medium rounded-lg transition-colors flex items-center justify-center gap-2"
              >
                <span class="material-symbols-outlined text-sm">add</span>
                {{ t('app.addThisDevice') }}
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
      class="board-floating-panel board-surface-panel fixed top-20 z-30 w-96 max-w-[calc(100vw-2rem)] rounded-2xl shadow-2xl border overflow-hidden"
    >
      <!-- Recommendation Header with gradient -->
      <div class="relative overflow-hidden">
        <div class="absolute inset-0 bg-gradient-to-br from-red-500 to-rose-600"></div>
        <div class="absolute inset-0 bg-[url('data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iNjAiIGhlaWdodD0iNjAiIHZpZXdCb3g9IjAgMCA2MCA2MCIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj48ZyBmaWxsPSJub25lIiBmaWxsLXJ1bGU9ImV2ZW5vZGQiPjxwYXRoIGQ9Ik0zNiAxOGMtOS45NDEgMC0xOCA4LjA1OS0xOCAxOHM4LjA1OSAxOCAxOCAxOCAxOC04LjA1OSAxOC0xOC04LjA1OS0xOC0xOC0xOHptMCAzMmMtNy43MzIgMC0xNC02LjI2OC0xNC0xNHM2LjI2OC0xNCAxNC0xNCAxNCA2LjI2OCAxNCAxNC02LjI2OCAxNC0xNCAxNHoiIGZpbGw9IiNmZmYiIGZpbGwtb3BhY2l0eT0iLjA1Ii8+PC9nPjwvc3ZnPg==')] opacity-30"></div>
        <div class="relative flex items-center justify-between p-4">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-red-500 backdrop-blur-sm rounded-xl flex items-center justify-center shadow-lg">
              <span class="material-symbols-outlined text-white text-xl">verified</span>
            </div>
            <div>
              <h3 class="text-black font-bold text-base">{{ t('app.specificationRecommendations') }}</h3>
              <p class="text-black/70 text-xs">{{ t('app.aiPoweredSpecificationSuggestions') }}</p>
            </div>
          </div>
          <button 
            @click="closeSpecRecommendationPanel"
            data-testid="close-spec-recommendations"
            class="w-8 h-8 flex items-center justify-center rounded-lg text-black/70 hover:text-black hover:bg-black/10 transition-all"
          >
            <span class="material-symbols-outlined">close</span>
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

        <!-- Loading State -->
        <div v-if="isRecommendingSpecs" class="flex flex-col items-center justify-center py-10">
          <div class="relative">
            <span class="material-symbols-outlined text-red-500 text-5xl animate-spin">sync</span>
            <div class="absolute inset-0 bg-red-400 rounded-full animate-ping opacity-20"></div>
          </div>
          <p class="text-slate-600 text-sm mt-4 font-medium">{{ t('app.analyzingSystem') }}</p>
          <p class="text-slate-400 text-xs mt-1">{{ t('app.generatingFormalSpecifications') }}</p>
        </div>

        <!-- Empty State -->
        <div v-else-if="specRecommendations.length === 0" class="flex flex-col items-center justify-center py-10">
          <div class="w-16 h-16 bg-slate-100 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-slate-300 text-3xl">verified</span>
          </div>
          <p class="text-slate-600 text-sm font-medium mt-2">{{ t('app.noRecommendationsAvailable') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.addMoreDevicesForSpecifications') }}</p>
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
              {{ t('app.refresh') }}
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
                    <span class="material-symbols-outlined text-red-600">verified</span>
                  </div>
                  <div class="min-w-0">
                    <h4 class="text-sm font-bold text-slate-800 truncate" :title="rec.templateLabel || t('app.customSpecification')">
                      {{ rec.templateLabel || t('app.customSpecification') }}
                    </h4>
                    <p class="text-xs text-slate-500 break-words">{{ rec.description || t('app.noDescription') }}</p>
                  </div>
                </div>
                <!-- Confidence Badge -->
                <div v-if="rec.confidence" class="px-2 py-1 bg-red-100 rounded-full">
                  <span class="text-xs font-medium text-red-700">{{ Math.round(rec.confidence * 100) }}%</span>
                </div>
              </div>
            </div>

            <!-- Priority -->
            <div class="px-3 pb-2">
              <p class="text-xs text-slate-600">
                {{ t('app.priority') }}: <span :class="{
                  'text-red-600': rec.priority === 'high',
                  'text-amber-600': rec.priority === 'medium',
                  'text-green-600': rec.priority === 'low'
                }">{{ formatRecommendationPriority(rec.priority) }}</span>
              </p>
            </div>

            <!-- Action Button -->
            <div class="px-3 pb-3">
              <button 
                @click="applySpecRecommendation(rec)"
                class="w-full py-2 px-4 bg-red-500 hover:bg-red-600 text-white text-sm font-medium rounded-lg transition-colors flex items-center justify-center gap-2"
              >
                <span class="material-symbols-outlined text-sm">add</span>
                {{ t('app.addThisSpecification') }}
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
      class="board-floating-panel board-surface-panel fixed top-20 z-30 w-72 max-w-[calc(100vw-2rem)] rounded-2xl shadow-2xl border overflow-hidden"
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
            @click="showSimulationPanel = false"
            data-testid="close-simulation-panel"
            class="w-8 h-8 flex items-center justify-center rounded-lg text-black/70 hover:text-black hover:bg-black/10 transition-all"
          >
            <span class="material-symbols-outlined">close</span>
          </button>
        </div>
      </div>
      <!-- Simulation Content -->
      <div class="p-3 space-y-3 bg-gradient-to-b from-white to-indigo-50/30">
        <!-- Steps -->
        <div class="p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
          <label class="block text-[10px] font-bold text-indigo-700 uppercase tracking-wide mb-2">
            {{ t('app.simulationSteps') }}: <span class="text-indigo-600">{{ simulationForm.steps }}</span>
          </label>
          <div class="flex items-center gap-3">
            <span class="material-symbols-outlined text-indigo-300">fast_rewind</span>
            <input
              v-model.number="simulationForm.steps"
              :disabled="isSimulating"
              type="range"
              min="1"
              max="100"
              class="flex-1 h-2 bg-indigo-200 rounded-lg appearance-none cursor-pointer accent-indigo-600 disabled:cursor-not-allowed disabled:opacity-60"
            />
            <span class="material-symbols-outlined text-indigo-300">fast_forward</span>
          </div>
        </div>

        <!-- Attack Mode -->
        <div class="flex items-center justify-between p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
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
            :disabled="isSimulating"
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

        <!-- Intensity (visible when attack is enabled) -->
        <div v-if="simulationForm.isAttack" class="p-3 bg-red-50 rounded-xl border border-red-200/60">
          <label class="block text-[10px] font-bold text-red-700 uppercase tracking-wide mb-2">
            {{ t('app.attackIntensity') }}: <span class="text-red-500">{{ simulationForm.intensity }}</span>
          </label>
          <input
            v-model.number="simulationForm.intensity"
            :disabled="isSimulating"
            type="range"
            min="0"
            max="50"
            class="w-full h-2 bg-red-200 rounded-lg appearance-none cursor-pointer accent-red-500 disabled:cursor-not-allowed disabled:opacity-60"
          />
          <div class="flex justify-between text-[10px] text-red-400 mt-1">
            <span>{{ t('app.weak') }}</span>
            <span>{{ t('app.strong') }}</span>
          </div>
        </div>

        <!-- Privacy Analysis -->
        <div class="flex items-center justify-between p-3 bg-white rounded-xl border border-slate-200/60 shadow-sm">
          <div class="flex items-center gap-3">
            <div class="w-8 h-8 bg-purple-100 rounded-lg flex items-center justify-center">
              <span class="material-symbols-outlined text-purple-500 text-lg">security</span>
            </div>
            <label class="text-xs font-bold text-slate-700 uppercase tracking-wide">
              {{ t('app.privacyAnalysis') }}
            </label>
          </div>
          <button
            type="button"
            :disabled="isSimulating"
            @click="simulationForm.enablePrivacy = !simulationForm.enablePrivacy"
            class="relative inline-flex h-6 w-11 items-center rounded-full transition-colors disabled:cursor-not-allowed disabled:opacity-60"
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
          :disabled="isSimulating || traceAnimationState.visible || simulationAnimationState.visible"
          class="w-full py-2.5 bg-indigo-600 hover:bg-indigo-700 disabled:bg-indigo-300 text-white rounded-lg text-xs font-bold uppercase tracking-wider transition-all shadow-md hover:shadow-lg hover:scale-[1.02] active:scale-[0.98] flex items-center justify-center gap-2 disabled:cursor-not-allowed disabled:hover:scale-100"
        >
          <template v-if="isSimulating">
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
        :visible="dialogVisible"
        :device-name="dialogMeta.deviceName"
        :description="dialogMeta.description"
        :label="dialogMeta.label"
        :node-id="dialogMeta.nodeId"
        :manifest="dialogMeta.manifest"
        :rules="dialogMeta.rules"
        :specs="dialogMeta.specs"
        @update:visible="dialogVisible = $event"
        @delete="handleDialogDelete"
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
        v-model="ruleBuilderVisible"
        :nodes="nodes"
        :device-templates="deviceTemplates"
        @save-rule="handleAddRule"
    />

    <!-- Canvas Map - Fixed at bottom left -->
    <div
      data-testid="canvas-map"
      class="canvas-map fixed w-56 p-3 border rounded-lg shadow-lg z-40"
    >
      <div class="flex items-center justify-between mb-2">
        <span class="text-[10px] uppercase font-bold text-slate-400">{{ t('app.canvasMap') }}</span>
        <div class="flex items-center gap-1">
          <button
            type="button"
            class="canvas-map__tool"
            data-testid="canvas-map-fit"
            :title="t('app.fitToContent')"
            @click="fitToContent"
          >
            <span class="material-symbols-outlined text-sm">fit_screen</span>
          </button>
          <button
            type="button"
            class="canvas-map__tool"
            data-testid="canvas-map-center"
            :title="t('app.centerSelection')"
            @click="centerSelection"
          >
            <span class="material-symbols-outlined text-sm">center_focus_strong</span>
          </button>
          <span class="text-[10px] text-primary font-bold">{{ Math.round(canvasZoom * 100) }}%</span>
        </div>
      </div>

      <div class="canvas-map__viewport w-full h-24 rounded bg-slate-50 border border-slate-200 relative overflow-hidden shadow-inner">
        <!-- SVG for lines (background layer) -->
        <svg class="absolute inset-0 w-full h-full pointer-events-none">
          <!-- Test line to verify SVG works -->

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
        </svg>

        <!-- Dynamic mini map dots representing devices -->
        <div
          v-for="dot in canvasMapDots"
          :key="dot.id"
          class="absolute rounded-full shadow-sm"
          :class="dot.size"
          :style="{ left: dot.x + 'px', top: dot.y + 'px', backgroundColor: dot.color }"
        ></div>

        <!-- Border frame -->
        <div class="absolute inset-0 border-2 border-primary/20 rounded pointer-events-none"></div>

        <!-- Empty state message -->
        <div v-if="canvasMapDots.length === 0" class="absolute inset-0 flex items-center justify-center text-slate-400 text-xs">
          {{ t('app.noDevicesOnCanvas') }}
        </div>
      </div>
    </div>

    <!-- Custom Rename Dialog -->
    <div v-if="renameDialogVisible" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="cancelRename">
      <div class="bg-white rounded-xl p-6 w-96 max-w-[90vw] shadow-2xl" @click.stop>
        <div class="mb-6">
          <h3 class="text-lg font-semibold text-slate-800 mb-4">{{ t('app.renameDevice') }}</h3>
          <div class="space-y-2">
            <input
              v-model="renameDialogData.newName"
              @keyup.enter="confirmRename"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-blue-500 transition-colors"
              :placeholder="t('app.enterDeviceName')"
            />
          </div>
        </div>
        <div class="flex justify-end space-x-3">
          <button
            @click="cancelRename"
            class="px-4 py-2 text-sm font-medium text-slate-700 bg-slate-100 border border-slate-300 rounded-lg hover:bg-slate-200 transition-colors"
          >
            {{ t('app.cancel') }}
          </button>
          <button
            @click="confirmRename"
            :disabled="!renameDialogData.newName.trim() || renameDialogData.newName.trim() === renameDialogData.node?.label"
            class="px-4 py-2 text-sm font-medium text-white bg-blue-600 border border-transparent rounded-lg hover:bg-blue-700 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
          >
            {{ t('app.confirm') }}
          </button>
        </div>
      </div>
    </div>

    <!-- Custom Delete Confirmation Dialog -->
    <div
      v-if="deleteConfirmDialogVisible"
      class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50"
      @click="cancelDelete"
      @keydown="handleDeleteConfirmDialogKeydown"
    >
      <div
        :ref="setDeleteConfirmDialogRef"
        class="bg-white rounded-xl p-6 w-96 max-w-[90vw] shadow-2xl"
        role="dialog"
        aria-modal="true"
        aria-labelledby="delete-device-dialog-title"
        tabindex="-1"
        @click.stop
      >
        <div class="mb-6">
          <div class="flex items-center mb-4">
            <div class="flex-shrink-0 w-10 h-10 bg-red-100 rounded-full flex items-center justify-center">
              <span class="material-symbols-outlined text-red-600" aria-hidden="true">warning</span>
            </div>
            <div class="ml-3">
              <h3 id="delete-device-dialog-title" class="text-lg font-semibold text-slate-800">{{ t('app.deleteDeviceTitle') }}</h3>
              <p class="text-sm text-slate-600">{{ t('app.actionCannotBeUndone') }}</p>
            </div>
          </div>

        

          <div v-if="deleteConfirmDialogData.hasRelations" class="bg-yellow-50 border border-yellow-200 rounded-lg p-4 mb-4">
            <div class="flex items-start">
              <span class="material-symbols-outlined text-yellow-600 mr-2 mt-0.5" aria-hidden="true">info</span>
              <div>
                <p class="text-sm font-medium text-yellow-800 mb-1">{{ t('app.deviceHasRelations') }}</p>
                <div class="text-xs text-yellow-700 space-y-1">
                  <div v-if="deleteConfirmDialogData.relationCount.rules > 0">
                    • {{ t('app.relatedRulesWillBeDeleted', { count: deleteConfirmDialogData.relationCount.rules }) }}
                  </div>
                  <div v-if="deleteConfirmDialogData.relationCount.specs > 0">
                    • {{ t('app.relatedSpecsWillBeDeleted', { count: deleteConfirmDialogData.relationCount.specs }) }}
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
            class="px-4 py-2 text-sm font-medium text-slate-700 bg-slate-100 border border-slate-300 rounded-lg hover:bg-slate-200 transition-colors"
          >
            {{ t('app.cancel') }}
          </button>
          <button
            type="button"
            @click="confirmDelete"
            class="px-4 py-2 text-sm font-medium text-white bg-red-600 border border-transparent rounded-lg hover:bg-red-700 transition-colors"
          >
            {{ t('app.deleteDevice') }}
          </button>
        </div>
      </div>
    </div>
  </div>

  <!-- Simulation Result Dialog -->
  <div v-if="simulationResult || simulationError" class="fixed inset-0 bg-black/60 backdrop-blur-sm flex items-center justify-center z-50" @click="simulationResult = null; simulationError = null">
    <div class="bg-white rounded-2xl w-[750px] max-w-[95vw] shadow-2xl max-h-[90vh] flex flex-col border border-slate-200/60" @click.stop>
      <!-- Header with gradient -->
      <div class="relative overflow-hidden rounded-t-2xl">
        <div class="bg-gradient-to-r from-indigo-500 to-violet-600"></div>
        <div class="absolute inset-0 bg-[url('data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iNjAiIGhlaWdodD0iNjAiIHZpZXdCb3g9IjAgMCA2MCA2MCIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj48ZyBmaWxsPSJub25lIiBmaWxsLXJ1bGU9ImV2ZW5vZGQiPjxwYXRoIGQ9Ik0zNiAxOGMtOS45NDEgMC0xOCA4LjA1OS0xOCAxOHM4LjA1OSAxOCAxOCAxOCAxOC04LjA1OSAxOC0xOC04LjA1OS0xOC0xOC0xOHptMCAzMmMtNy43MzIgMC0xNC02LjI2OC0xNC0xNHM2LjI2OC0xNCAxNC0xNCAxNCA2LjI2OCAxNCAxNC02LjI2OCAxNC0xNCAxNHoiIGZpbGw9IiNmZmYiIGZpbGwtb3BhY2l0eT0iLjA1Ii8+PC9nPjwvc3ZnPg==')] opacity-20"></div>
        <div class="relative flex items-center justify-between p-5">
          <div class="flex items-center gap-4">
            <div class="w-12 h-12 bg-white/20 backdrop-blur-sm rounded-xl flex items-center justify-center shadow-lg">
              <span class="material-symbols-outlined text-white text-2xl">play_circle</span>
            </div>
            <div>
              <h3 class="text-xl font-bold text-white">{{ t('app.simulationResult') }}</h3>
              <p class="text-indigo-200/80 text-sm" v-if="simulationResult">
                {{ t('app.statesFromSteps', { states: simulationResult.steps || 0, steps: simulationResult.requestedSteps || 0 }) }}
              </p>
            </div>
          </div>
          <button @click="simulationResult = null; simulationError = null" class="w-9 h-9 flex items-center justify-center rounded-lg text-white/70 hover:text-white hover:bg-white/20 transition-all">
            <span class="material-symbols-outlined text-xl">close</span>
          </button>
        </div>
      </div>

      <div v-if="simulationError" class="p-6">
        <div class="mb-4 p-4 bg-red-50 border border-red-200 rounded-xl">
          <div class="flex items-center gap-2 text-red-600">
            <span class="material-symbols-outlined">error</span>
            <span class="font-medium">{{ simulationError }}</span>
          </div>
        </div>
      </div>

      <div v-else-if="simulationResult" class="flex-1 overflow-hidden flex flex-col p-6 pt-4">
        <!-- Logs -->
        <div class="mb-4">
          <h4 class="text-sm font-bold text-slate-700 mb-2">{{ t('app.executionLogs') }}</h4>
          <div class="bg-slate-900 rounded-lg p-3 max-h-32 overflow-y-auto">
            <pre class="text-xs text-green-400 font-mono whitespace-pre-wrap">{{ simulationResult.logs?.join('\n') || t('app.noLogsAvailableShort') }}</pre>
          </div>
        </div>

        <!-- States Preview -->
        <div class="flex-1 overflow-hidden flex flex-col">
          <h4 class="text-sm font-bold text-slate-700 mb-2">{{ t('app.simulationStates') }} ({{ simulationResult.states?.length || 0 }})</h4>
          <div class="flex-1 overflow-y-auto border border-slate-200 rounded-lg">
            <table class="w-full text-xs">
              <thead class="bg-slate-50 sticky top-0">
                <tr>
                  <th class="text-left p-2 font-bold text-slate-600 border-b">{{ t('app.stateNumber') }}</th>
                  <th class="text-left p-2 font-bold text-slate-600 border-b">{{ t('app.devicesColumn') }}</th>
                </tr>
              </thead>
              <tbody>
                <tr v-for="(state, idx) in simulationResult.states" :key="idx" class="border-b border-slate-100 hover:bg-indigo-50">
                  <td class="p-2 font-mono text-indigo-600">{{ state.stateIndex }}</td>
                  <td class="p-2">
                    <div class="flex flex-wrap gap-1">
                      <span
                        v-for="(device, dIdx) in state.devices"
                        :key="dIdx"
                        class="inline-flex items-center gap-1 px-2 py-0.5 bg-slate-100 rounded text-slate-700"
                      >
                        <span class="font-medium">{{ device.deviceId }}</span>
                        <span class="text-slate-400">:</span>
                        <span class="text-indigo-600">{{ device.state || 'N/A' }}</span>
                      </span>
                    </div>
                  </td>
                </tr>
              </tbody>
            </table>
          </div>
        </div>

        <!-- NuSMV Output (collapsed by default) -->
        <details class="mt-4">
          <summary class="text-xs font-bold text-slate-500 cursor-pointer hover:text-slate-700">
            {{ t('app.showRawNusmvOutput') }}
          </summary>
          <div class="mt-2 bg-slate-900 rounded-lg p-3 max-h-40 overflow-y-auto">
            <pre class="text-xs text-slate-300 font-mono whitespace-pre-wrap">{{ simulationResult.nusmvOutput || t('app.noOutput') }}</pre>
          </div>
        </details>
      </div>

      <div class="mt-4 pt-4 border-t border-slate-200 flex justify-end gap-3">
        <button
          v-if="simulationResult && simulationResult.states && simulationResult.states.length > 0"
          @click="openSimulationTimeline"
          :disabled="traceAnimationState.visible"
          :class="[
            'px-4 py-2 rounded-lg text-sm font-medium transition-colors flex items-center gap-2',
            traceAnimationState.visible 
              ? 'bg-slate-300 text-slate-500 cursor-not-allowed' 
              : 'bg-gradient-to-r from-indigo-500 to-indigo-600 hover:from-indigo-600 hover:to-indigo-700 text-white'
          ]"
        >
          <span class="material-symbols-outlined text-lg">play_circle</span>
          {{ t('app.viewTimeline') }}
          <span v-if="traceAnimationState.visible" class="text-xs ml-1">({{ t('app.active') }})</span>
        </button>
        <button
          @click="simulationResult = null; simulationError = null"
          class="px-4 py-2 bg-slate-200 hover:bg-slate-300 text-slate-700 rounded-lg text-sm font-medium transition-colors"
        >
          {{ t('app.close') }}
        </button>
      </div>
    </div>
  </div>

  <!-- Verification Result Dialog -->
  <div v-if="showResultDialog" class="fixed inset-0 bg-black/60 backdrop-blur-sm flex items-center justify-center z-50" @click="closeResultDialog">
    <div class="bg-white rounded-2xl w-[650px] max-w-[95vw] shadow-2xl max-h-[85vh] flex flex-col border border-slate-200" @click.stop>
      <!-- Header -->
      <div class="relative overflow-hidden rounded-t-2xl border-b" :class="verificationResult?.safe ? 'bg-green-50 border-green-200' : 'bg-red-50 border-red-200'">
        <div class="relative flex items-center justify-between p-5">
          <div class="flex items-center gap-4">
            <div class="w-12 h-12 rounded-xl flex items-center justify-center shadow-sm" :class="verificationResult?.safe ? 'bg-green-100' : 'bg-red-100'">
              <span class="material-symbols-outlined text-2xl" :class="verificationResult?.safe ? 'text-green-600' : 'text-red-600'">
                {{ verificationResult?.safe ? 'check_circle' : 'error' }}
              </span>
            </div>
            <div>
              <h3 class="text-xl font-bold text-slate-800">{{ t('app.verificationResult') }}</h3>
              <p class="text-sm text-slate-600">{{ verificationResult?.safe ? t('app.allSpecificationsPassed') : verificationUnsafeDetail }}</p>
            </div>
          </div>
          <button @click="closeResultDialog" class="w-9 h-9 flex items-center justify-center rounded-lg text-slate-500 hover:text-slate-700 hover:bg-slate-200 transition-all">
            <span class="material-symbols-outlined text-xl">close</span>
          </button>
        </div>
      </div>

      <div class="p-6 flex-1 overflow-y-auto">
        <div v-if="verificationError" class="mb-4 p-4 bg-red-50 border border-red-200 rounded-xl">
          <div class="flex items-center gap-2 text-red-600">
            <span class="material-symbols-outlined">error</span>
            <span class="font-medium">{{ verificationError }}</span>
          </div>
        </div>

        <div v-else-if="verificationResult" class="space-y-4">
          <!-- Status Card -->
          <div class="p-5 rounded-xl" :class="verificationResult.safe ? 'bg-gradient-to-r from-green-50 to-emerald-50 border border-green-200' : 'bg-gradient-to-r from-red-50 to-orange-50 border border-red-200'">
            <div class="flex items-center gap-3">
              <div class="w-10 h-10 rounded-xl flex items-center justify-center" :class="verificationResult.safe ? 'bg-green-100' : 'bg-red-100'">
                <span class="material-symbols-outlined" :class="verificationResult.safe ? 'text-green-600' : 'text-red-600'">
                  {{ verificationResult.safe ? 'verified' : 'warning' }}
                </span>
              </div>
              <div>
                <span class="text-lg font-bold" :class="verificationResult.safe ? 'text-green-800' : 'text-red-800'">
                  {{ verificationResult.safe ? t('app.systemSafe') : t('app.systemUnsafe') }}
                </span>
                <p class="text-sm" :class="verificationResult.safe ? 'text-green-600' : 'text-red-600'">
                  {{ verificationResult.safe ? t('app.allSpecsPassedVerification') : verificationUnsafeDetail }}
                </p>
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
                    passed: verificationSpecResultSummary.passed,
                    failed: verificationSpecResultSummary.failed
                  }) }}
                </p>
              </div>
              <span
                class="material-symbols-outlined text-lg"
                :class="verificationSpecResultSummary.failed > 0 ? 'text-red-500' : 'text-green-500'"
              >
                {{ verificationSpecResultSummary.failed > 0 ? 'rule' : 'verified' }}
              </span>
            </div>
            <div class="space-y-2 max-h-72 overflow-y-auto pr-1">
              <div
                v-for="(result, index) in verificationSpecResultSummary.results"
                :key="`${result.specId}-${index}`"
                class="rounded-lg border bg-white px-3 py-2"
                :class="result.passed ? 'border-green-200' : 'border-red-200'"
              >
                <div class="flex items-start justify-between gap-3">
                  <div class="min-w-0 flex-1">
                    <div class="flex flex-wrap items-center gap-2">
                      <span class="text-xs font-semibold text-slate-500">#{{ Number(index) + 1 }}</span>
                      <span class="font-mono text-xs font-semibold text-slate-700 break-all">{{ result.specId }}</span>
                    </div>
                    <p v-if="result.expression" class="mt-1 max-w-full font-mono text-xs leading-5 text-slate-600 break-all">
                      {{ result.expression }}
                    </p>
                  </div>
                  <span
                    class="inline-flex shrink-0 items-center gap-1 rounded-full border px-2 py-0.5 text-xs font-semibold"
                    :class="result.passed ? 'bg-green-50 border-green-200 text-green-700' : 'bg-red-50 border-red-200 text-red-700'"
                  >
                    <span class="material-symbols-outlined text-sm">{{ result.passed ? 'check_circle' : 'error' }}</span>
                    {{ result.passed ? t('app.specPassed') : t('app.specViolated') }}
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

        <div v-if="verificationResult && !verificationResult.safe && verificationResult.traces && verificationResult.traces.length > 0">
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
              <div class="text-xs font-bold text-slate-600 mb-1">{{ t('app.specPrefix') }}: {{ trace.violatedSpecId }}</div>
              <div v-if="trace.violatedSpecJson" class="text-xs font-mono text-slate-700 bg-slate-50 p-2 rounded mt-1">
                {{ formatSpec(trace.violatedSpecJson) }}
              </div>
              <div class="text-xs text-slate-500 mt-1">
                {{ t('app.statesCount', { count: trace.states?.length || 0 }) }}
              </div>
            </div>
          </div>
        </div>
      </div>

      
    </div>
  </div>

  <!-- Counterexample Trace Animation Panel -->
  <div 
    v-if="traceAnimationState.visible && savedTraces.length > 0"
    class="fixed left-4 top-1/2 -translate-y-1/2 z-40 flex flex-col gap-2"
    style="max-height: 80vh;"
  >
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
    <div class="board-timeline board-timeline--trace" data-testid="trace-timeline">
      
      <!-- Violation Info - Only show at violation point -->
      <div 
        v-if="traceAnimationState.selectedStateIndex === totalStates - 1"
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
          <div class="text-xs font-mono text-slate-800">{{ formattedSpec }}</div>
        </div>
      </div>

      <!-- Timeline -->
      <div class="mb-3">
        <div class="flex items-center justify-between mb-3">
          <div class="flex items-center gap-2 flex-wrap">
            <span class="text-sm font-bold text-slate-700">{{ t('app.traceVisualization.stateSequence') }}</span>
            <span class="px-2 py-0.5 bg-red-100 text-red-600 text-xs rounded-full" aria-live="polite">
              {{ traceAnimationState.selectedStateIndex + 1 }} / {{ totalStates }}
            </span>
            <!-- Verification Info (from the viewed trace's own context, not the live form) -->
            <span v-if="activeTraceContext.isAttack" class="px-2 py-0.5 bg-red-500 text-white text-xs rounded-full flex items-center gap-1">
              <span class="material-symbols-outlined text-[10px]">warning</span>
              {{ t('app.traceVisualization.attack') }}
            </span>
            <span v-if="activeTraceContext.isAttack" class="px-2 py-0.5 bg-orange-100 text-orange-600 text-xs rounded-full">
              {{ t('app.traceVisualization.intensity') }}: {{ activeTraceContext.intensity }}
            </span>
            <span class="px-2 py-0.5 bg-blue-100 text-blue-600 text-xs rounded-full">
              <span class="material-symbols-outlined text-[10px]">security</span>
              {{ t('app.traceVisualization.security') }}
            </span>
          </div>
          <div class="flex items-center gap-2">
            <button
              type="button"
              @click="toggleTraceAnimation"
              class="px-3 py-1.5 rounded-lg text-xs font-medium transition-colors flex items-center gap-1"
              :aria-label="traceAnimationState.isPlaying ? t('app.traceVisualization.stop') : t('app.traceVisualization.play')"
              :class="traceAnimationState.isPlaying 
                ? 'bg-red-500 text-white' 
                : 'bg-slate-100 text-slate-700 hover:bg-slate-200'"
            >
              <span class="material-symbols-outlined text-sm" aria-hidden="true">{{ traceAnimationState.isPlaying ? 'stop' : 'play_arrow' }}</span>
              {{ traceAnimationState.isPlaying ? t('app.traceVisualization.stop') : t('app.traceVisualization.play') }}
            </button>
            <button
              type="button"
              @click="closeTraceAnimation"
              class="p-1.5 hover:bg-slate-100 rounded-lg transition-colors"
              :title="t('app.close')"
              :aria-label="t('app.close')"
            >
              <span class="material-symbols-outlined text-slate-500" aria-hidden="true">close</span>
            </button>
          </div>
        </div>
        
        <!-- Timeline bar with horizontal scroll support -->
        <div class="overflow-x-auto scrollbar-thin py-2">
          <div 
            class="relative h-14"
            :style="{ width: (currentTrace?.states?.length || 0) > 15 ? 'max-content' : '100%', minWidth: (currentTrace?.states?.length || 0) > 15 ? `${Math.max((currentTrace?.states?.length || 0) * 38, 500)}px` : '100%' }"
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
                :class="Number(index) === traceAnimationState.selectedStateIndex 
                  ? 'bg-red-500 border-red-500 scale-125 shadow-lg' 
                  : Number(index) < traceAnimationState.selectedStateIndex 
                    ? 'bg-green-500 border-green-500' 
                    : 'bg-white border-slate-300 hover:border-red-300'"
              >
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
    :visible="simulationAnimationState.visible"
    :states="savedSimulationStates"
    :style="boardShellStyle"
    @update:visible="handleSimulationTimelineClose"
    @highlight-state="handleHighlightTrace"
  />

  <!-- Logs affordance for a successful simulation: the success path opens the timeline (not the
       result dialog), so this lets the user reach the execution logs / raw NuSMV output on demand. -->
  <div
    v-if="simulationAnimationState.visible && lastSimulationResult"
    class="board-timeline-log-button"
    :style="boardShellStyle"
  >
    <button
      type="button"
      @click="openSimulationLogs"
      :title="t('app.showSimulationLogs')"
      :aria-label="t('app.showSimulationLogs')"
      class="px-3 py-1 bg-slate-700 hover:bg-slate-800 text-white rounded-lg text-xs shadow-lg flex items-center gap-1"
    >
      <span class="material-symbols-outlined text-sm">description</span>
      {{ t('app.showSimulationLogs') }}
    </button>
  </div>

  <!-- Fix Result Dialog 组件 -->
  <FixResultDialog
    :visible="showFixDialog"
    :trace-id="fixTraceId || 0"
    :violated-spec-id="fixViolatedSpecId"
    @update:visible="showFixDialog = $event"
    @applied="handleFixApplied"
  />
</template>

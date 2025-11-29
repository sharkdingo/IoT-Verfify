<script setup lang="ts">
/* =================================================================================
 * 1. Imports & Setup
 * ================================================================================= */
import { ref, reactive, onMounted, onBeforeUnmount, watch } from 'vue'
import { useI18n } from 'vue-i18n'
import { ElMessage, ElMessageBox } from 'element-plus'
// Icons
import { Edit, Platform, Close } from '@element-plus/icons-vue'

// Types
import type { DeviceDialogMeta, DeviceTemplate } from '../types/device'
import type { CanvasPan } from '../types/canvas'
import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { RuleForm } from '../types/rule'
import type { SpecCondition, Specification, SpecTemplate, SpecTemplateId } from '../types/spec'
// [Updated] 引入新的 Panel 类型定义
import type { DockSide, DockState, PanelKey, PanelPosition, BoardLayoutDto } from '@/types/panel'

// Utils
import { getDeviceIconPath, getNodeIcon } from '../utils/device'
import { getUniqueLabel } from '../utils/canvas/nodeCreate'
import {
  getSpecMode,
  validateAndCleanConditions,
  isSameSpecification,
  isSpecRelatedToNode,
  removeSpecsForNode,
  updateSpecsForNodeRename
} from '../utils/spec'
import { getLinkPoints, updateRulesForNodeRename } from '../utils/rule'
import { loadDeviceTemplates, saveDeviceTemplates } from '../utils/boardStorage'

// Config
import { defaultSpecTemplates } from '../assets/config/specTemplates'
import { defaultDeviceTemplates } from '../assets/config/deviceTemplates'

// API
import boardApi from '@/api/board'

// Components
import InputPanel from '../components/InputPanel.vue'
import StatusPanel from '../components/StatusPanel.vue'
import DeviceDialog from '../components/DeviceDialog.vue'
import CanvasBoard from '../components/CanvasBoard.vue'

// Styles
import '../styles/board.css'

const { t } = useI18n()

/* =================================================================================
 * 2. Constants & Configuration
 * ================================================================================= */

const DEFAULT_PANEL_PADDING = 5
const DOCK_SNAP_THRESHOLD = -1 // 拖拽到边缘多少像素内自动吸附
const DOCK_ICON_SIZE = 48

const CARD_WIDTH_MIN = 192 // 12rem
const CARD_WIDTH_MAX = 384 // 24rem
const CARD_WIDTH_RATIO = 0.24

const NODE_MARGIN_RIGHT_OF_PANEL = 60
const NODE_GRID_COLS = 4
const NODE_SPACING_X = 160
const NODE_SPACING_Y = 120
const NODE_START_Y = 140

const MIN_ZOOM = 0.4
const MAX_ZOOM = 2
const ZOOM_STEP = 0.1

const BASE_NODE_WIDTH = 160
const BASE_FONT_SIZE = 16

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

// --- Panel State (Position & Docking) ---
const panelPositions = reactive<Record<PanelKey, PanelPosition>>({
  input: { x: 24, y: 24 },
  status: { x: 1040, y: 80 }
})

const panelDockState = reactive<Record<PanelKey, DockState>>({
  input: { isDocked: false, side: null, lastPos: { x: 24, y: 24 } },
  status: { isDocked: false, side: null, lastPos: { x: 1040, y: 80 } }
})

// [Fix] Dragging State: 用于在拖拽时禁用 CSS transition，解决“粘滞”感
const draggingState = reactive<Record<PanelKey, boolean>>({
  input: false,
  status: false
})

let draggingPanel: PanelKey | null = null
let panelDragStart = { x: 0, y: 0 }
let panelStartPos = { x: 0, y: 0 }

// --- Core Data State ---
const deviceTemplates = ref<DeviceTemplate[]>([])
const nodes = ref<DeviceNode[]>([])
const edges = ref<DeviceEdge[]>([])
const specifications = ref<Specification[]>([])
const specTemplates = ref<SpecTemplate[]>(defaultSpecTemplates)

const inputActive = ref<string[]>([])
const statusActive = ref<string[]>([])

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

/* =================================================================================
 * 4. Helper Functions (Styles & Calculation)
 * ================================================================================= */

const getCardWidth = () => {
  const w = window.innerWidth * CARD_WIDTH_RATIO
  return Math.min(CARD_WIDTH_MAX, Math.max(CARD_WIDTH_MIN, w))
}

const getTemplateInitIcon = (tpl: DeviceTemplate) => {
  const folder = tpl.name
  const initState = tpl.manifest?.InitState || 'Working'
  return getDeviceIconPath(folder, initState)
}

const getNodeLabelStyle = (node: DeviceNode) => {
  const ratio = node.width / BASE_NODE_WIDTH
  const scale = Math.min(Math.max(ratio, 0.75), 1.5)
  const fontSize = BASE_FONT_SIZE * scale
  return {
    fontSize: fontSize + 'px',
    maxWidth: node.width - 16 + 'px'
  }
}

// [Fix] CSS 类绑定：添加 is-dragging 用于禁用过渡
const getCardClasses = (key: PanelKey) => {
  const state = panelDockState[key]
  return {
    'floating-card': true,
    [`${key}-card`]: true,
    'is-docked': state.isDocked,
    [`dock-${state.side}`]: state.isDocked,
    'is-dragging': draggingState[key]
  }
}

const isInteractiveTarget = (el: HTMLElement | null): boolean => {
  if (!el) return false
  const interactiveSelectors =
      'input, textarea, select, button, a, [role="button"],' +
      '.el-input, .el-select, .el-button, .el-checkbox, .el-radio,' +
      '.el-switch, .el-slider, .el-table, .el-scrollbar, .dock-close-btn'
  return !!el.closest(interactiveSelectors)
}

// [Fix] 安全检查：防止面板在初始化或窗口缩放时跑出屏幕外
const clampPanelsToScreen = () => {
  const winW = window.innerWidth
  const winH = window.innerHeight
  const margin = 40;

  (['input', 'status'] as PanelKey[]).forEach(key => {
    const pos = panelPositions[key]
    const dock = panelDockState[key]

    // [Crucial Fix] 如果是停靠状态，必须根据当前窗口尺寸重置位置
    // 否则如果之前保存的坐标在当前屏幕外（例如底部停靠时 y 很大），面板就会消失
    if (dock.isDocked && dock.side) {
      switch (dock.side) {
        case 'left':
          pos.x = 0
          pos.y = Math.min(Math.max(0, pos.y), winH - DOCK_ICON_SIZE)
          break
        case 'right':
          pos.x = winW - DOCK_ICON_SIZE
          pos.y = Math.min(Math.max(0, pos.y), winH - DOCK_ICON_SIZE)
          break
        case 'top':
          pos.y = 0
          pos.x = Math.min(Math.max(0, pos.x), winW - DOCK_ICON_SIZE)
          break
        case 'bottom':
          pos.y = winH - DOCK_ICON_SIZE
          pos.x = Math.min(Math.max(0, pos.x), winW - DOCK_ICON_SIZE)
          break
      }
    } else {
      // 未停靠状态，进行常规边界检查
      pos.x = Math.min(Math.max(0, pos.x), winW - margin)
      pos.y = Math.min(Math.max(0, pos.y), winH - margin)
    }
  })
}

/* =================================================================================
 * 5. Canvas Interaction (Zoom & Pan)
 * ================================================================================= */

// [Fix] 拦截浏览器默认缩放，只改变 canvasZoom
const onBoardWheel = (e: WheelEvent) => {
  if (e.ctrlKey) {
    // 阻止浏览器默认缩放行为 (template 中已加 .prevent，这里是逻辑处理)
    if (e.deltaY > 0) {
      canvasZoom.value = Math.max(MIN_ZOOM, canvasZoom.value - ZOOM_STEP)
    } else {
      canvasZoom.value = Math.min(MAX_ZOOM, canvasZoom.value + ZOOM_STEP)
    }
  }
}

const onCanvasEnter = () => (isCanvasHovered.value = true)
const onCanvasLeave = () => (isCanvasHovered.value = false)

// [Fix] 全局按键拦截：拦截 Ctrl + +/-/0 防止浏览器缩放快捷键
const onGlobalKeydown = (e: KeyboardEvent) => {
  if (e.ctrlKey) {
    if (['=', '+', '-', '0'].includes(e.key)) {
      e.preventDefault() // 关键！阻止浏览器菜单缩放

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

  // 捕获指针，拖动体验更好
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

  await saveLayoutToServer()
  window.removeEventListener('pointermove', onCanvasPointerMove)
  window.removeEventListener('pointerup', onCanvasPointerUp)
}

/* =================================================================================
 * 6. Panel Interaction (Move, Dock, Restore)
 * ================================================================================= */

// --- 6.1 Event Handlers ---

const onPanelPointerDownWrapper = (e: PointerEvent, key: PanelKey) => {
  const target = e.target as HTMLElement | null
  if (isInteractiveTarget(target)) return
  onPanelPointerDown(e, key)
}

const onPanelPointerDown = (e: PointerEvent, key: PanelKey) => {
  // 如果已停靠，点击即恢复
  if (panelDockState[key].isDocked) {
    restorePanel(key)
    return
  }

  // 1. 设置拖拽状态 -> 激活 CSS 的 no-transition (关键：解决拖拽延迟)
  draggingPanel = key
  draggingState[key] = true

  // 2. 捕获指针，防止快速拖动时鼠标移出元素导致失焦
  const target = e.currentTarget as HTMLElement
  if (target && target.setPointerCapture) {
    target.setPointerCapture(e.pointerId)
  }

  panelDragStart = { x: e.clientX, y: e.clientY }
  panelStartPos = { ...panelPositions[key] }

  window.addEventListener('pointermove', onPanelPointerMove)
  window.addEventListener('pointerup', onPanelPointerUp)
}

const onPanelPointerMove = (e: PointerEvent) => {
  if (!draggingPanel) return
  // 纯粹的位置更新，因为有 is-dragging 类，这里会非常流畅
  const dx = e.clientX - panelDragStart.x
  const dy = e.clientY - panelDragStart.y
  const pos = panelPositions[draggingPanel]
  pos.x = panelStartPos.x + dx
  pos.y = panelStartPos.y + dy
}

const onPanelPointerUp = async (e: PointerEvent) => {
  if (!draggingPanel) return

  const key = draggingPanel

  // 释放指针捕获
  const target = e.target as HTMLElement
  if (target && target.releasePointerCapture) {
    try { target.releasePointerCapture(e.pointerId) } catch(err){}
  }

  // 3. 检查是否需要自动吸附
  checkAutoDock(key)

  // 4. 清除拖拽状态
  // 使用 requestAnimationFrame 延迟一帧，确保吸附动画(transition)能平滑接管
  requestAnimationFrame(() => {
    draggingState[key] = false
    draggingPanel = null
  })

  window.removeEventListener('pointermove', onPanelPointerMove)
  window.removeEventListener('pointerup', onPanelPointerUp)

  await saveLayoutToServer()
}

// --- 6.2 Docking Logic ---
const getNearestEdge = (x: number, y: number, width: number, height: number): { side: DockSide, dist: number } => {
  const winW = window.innerWidth
  const winH = window.innerHeight

  const distLeft = x
  const distRight = winW - (x + width)
  const distTop = y
  const distBottom = winH - (y + height)

  const min = Math.min(distLeft, distRight, distTop, distBottom)

  if (min === distLeft) return { side: 'left', dist: min }
  if (min === distRight) return { side: 'right', dist: min }
  if (min === distTop) return { side: 'top', dist: min }
  return { side: 'bottom', dist: min }
}

const checkAutoDock = (key: PanelKey) => {
  const el = document.querySelector(`.${key}-card`) as HTMLElement
  if (!el) return

  const rect = el.getBoundingClientRect()
  const { side, dist } = getNearestEdge(rect.x, rect.y, rect.width, rect.height)

  if (dist < DOCK_SNAP_THRESHOLD) {
    dockPanel(key, side)
  }
}

const handleManualDock = (key: PanelKey) => {
  const el = document.querySelector(`.${key}-card`) as HTMLElement
  if (!el) return
  const rect = el.getBoundingClientRect()
  // 手动点击 X 时，寻找绝对最近的边缘直接停靠
  const { side } = getNearestEdge(rect.x, rect.y, rect.width, rect.height)
  dockPanel(key, side)
}

const dockPanel = (key: PanelKey, side: DockSide) => {
  if (!side) return

  panelDockState[key].lastPos = { ...panelPositions[key] }
  panelDockState[key].isDocked = true
  panelDockState[key].side = side

  const winW = window.innerWidth
  const winH = window.innerHeight

  // 设置吸附位置（配合 CSS transition 实现飞入效果）
  if (side === 'left') {
    panelPositions[key].x = 0
  } else if (side === 'right') {
    panelPositions[key].x = winW - DOCK_ICON_SIZE
  } else if (side === 'top') {
    panelPositions[key].y = 0
  } else if (side === 'bottom') {
    panelPositions[key].y = winH - DOCK_ICON_SIZE
  }

  void saveLayoutToServer()
}

// [Fix] 智能恢复逻辑：紧贴边缘完全展示
const restorePanel = (key: PanelKey) => {
  const side = panelDockState[key].side
  const padding = DEFAULT_PANEL_PADDING
  const headerHeight = 60

  // 获取当前卡片展开后的理论宽度
  const currentCardWidth = getCardWidth()

  const winW = window.innerWidth
  const winH = window.innerHeight

  let newX = panelPositions[key].x
  let newY = panelPositions[key].y

  // 根据停靠方向计算“完美展示位置”
  if (side === 'left') {
    // 停靠在左 -> 恢复到左侧 padding 处
    newX = padding
    newY = Math.min(Math.max(padding, panelPositions[key].y), winH - headerHeight)
  } else if (side === 'right') {
    // 停靠在右 -> 恢复到右侧边缘内侧
    newX = winW - currentCardWidth - padding
    newY = Math.min(Math.max(padding, panelPositions[key].y), winH - headerHeight)
  } else if (side === 'top') {
    // 停靠在上 -> 恢复到顶部
    newY = padding
    newX = Math.min(Math.max(padding, panelPositions[key].x), winW - currentCardWidth - padding)
  } else if (side === 'bottom') {
    // 停靠在下 -> 恢复到大概位置
    if (panelPositions[key].y > winH - 200) {
      newY = winH - 500 // 假设一个合理高度
    } else {
      newY = Math.max(padding, panelPositions[key].y)
    }
    newX = Math.min(Math.max(padding, panelPositions[key].x), winW - currentCardWidth - padding)
  } else {
    // 异常回退
    newX = panelDockState[key].lastPos.x
    newY = panelDockState[key].lastPos.y
  }

  // 安全边界钳位，防止出界
  newX = Math.min(Math.max(0, newX), winW - 100)
  newY = Math.min(Math.max(0, newY), winH - headerHeight)

  panelPositions[key].x = newX
  panelPositions[key].y = newY

  panelDockState[key].isDocked = false
  panelDockState[key].side = null

  void saveLayoutToServer()
}

/* =================================================================================
 * 7. Node / Edge / Spec Management
 * ================================================================================= */

// --- Node Positioning ---
const getNextNodePosition = (): { x: number; y: number } => {
  const count = nodes.value.length
  const col = count % NODE_GRID_COLS
  const row = Math.floor(count / NODE_GRID_COLS)

  const screenX =
      panelPositions.input.x +
      getCardWidth() +
      NODE_MARGIN_RIGHT_OF_PANEL +
      col * NODE_SPACING_X

  const screenY = NODE_START_Y + row * NODE_SPACING_Y

  const x = (screenX - canvasPan.value.x) / canvasZoom.value
  const y = (screenY - canvasPan.value.y) / canvasZoom.value

  return { x, y }
}

// --- Creation ---
const createDeviceInstanceAt = async (tpl: DeviceTemplate, pos: { x: number; y: number }) => {
  const uniqueLabel = getUniqueLabel(tpl.name, nodes.value)
  const node: DeviceNode = {
    id: uniqueLabel,
    templateName: tpl.name,
    label: uniqueLabel,
    position: pos,
    state: tpl.manifest.InitState || 'Off',
    width: 110,
    height: 90
  }
  nodes.value.push(node)
  await saveNodesToServer()
}

const handleCreateDevice = async (tpl: DeviceTemplate) => {
  const pos = getNextNodePosition()
  await createDeviceInstanceAt(tpl, pos)
}

// --- Drag & Drop Devices ---
const onDeviceDragStart = (tpl: DeviceTemplate) => {
  draggingTplName.value = tpl.name
}

const onDeviceDragEnd = () => {
  draggingTplName.value = null
}

const onCanvasDragOver = (e: DragEvent) => {
  if (e.dataTransfer) e.dataTransfer.dropEffect = 'copy'
}

const onCanvasDrop = async (e: DragEvent) => {
  if (!draggingTplName.value) return
  const tpl = deviceTemplates.value.find(d => d.name === draggingTplName.value)
  if (!tpl) return

  const rect = (e.currentTarget as HTMLElement).getBoundingClientRect()
  const Sx = e.clientX - rect.left
  const Sy = e.clientY - rect.top

  const x = (Sx - canvasPan.value.x) / canvasZoom.value
  const y = (Sy - canvasPan.value.y) / canvasZoom.value

  await createDeviceInstanceAt(tpl, { x, y })
  draggingTplName.value = null
}

// --- Canvas Board Events ---
const handleNodeMovedOrResized = async () => {
  await saveNodesToServer()
  await saveEdgesToServer()
}

// --- Rules (InputPanel) ---
const handleAddRule = async (payload: RuleForm) => {
  const { fromId, fromApi, toId, toApi } = payload
  if (!fromId || !fromApi || !toId || !toApi) {
    ElMessage.warning(t('app.fillAllRuleFields') || '请完整选择源/目标设备及 API')
    return
  }

  const fromNode = nodes.value.find(n => n.id === fromId)
  const toNode = nodes.value.find(n => n.id === toId)
  if (!fromNode || !toNode) return

  const { fromPoint, toPoint } = getLinkPoints(fromNode, toNode)

  edges.value.push({
    id: 'edge_' + Date.now(),
    from: fromNode.id,
    to: toNode.id,
    fromLabel: fromNode.label,
    toLabel: toNode.label,
    fromApi,
    toApi,
    fromPos: fromPoint,
    toPos: toPoint
  })
  await saveEdgesToServer()
}

// --- Specs (InputPanel) ---
const handleAddSpec = async (payload: {
  templateId: SpecTemplateId | ''
  mode: 'single' | 'ifThen'
  aConditions: SpecCondition[]
  ifConditions: SpecCondition[]
  thenConditions: SpecCondition[]
}) => {
  if (!payload.templateId) {
    ElMessage.warning(t('app.selectTemplate') || '请选择规约模板')
    return
  }

  const tplId = payload.templateId as SpecTemplateId
  const aCheck = validateAndCleanConditions(payload.aConditions)
  const ifCheck = validateAndCleanConditions(payload.ifConditions)
  const thenCheck = validateAndCleanConditions(payload.thenConditions)

  if (aCheck.hasIncomplete || ifCheck.hasIncomplete || thenCheck.hasIncomplete) {
    ElMessage.warning(t('app.specRowIncomplete') || '存在未填完整的条件')
    return
  }

  const aConds = aCheck.cleaned
  const ifConds = ifCheck.cleaned
  const thenConds = thenCheck.cleaned

  const mode = getSpecMode(tplId)
  const tplLabel = specTemplates.value.find(t => t.id === tplId)?.label || tplId

  if (mode === 'single') {
    if (!aConds.length) {
      ElMessage.warning(t('app.specNeedA') || '请至少配置一个事件 A 条件')
      return
    }
    const item: Specification = {
      id: 'spec_' + Date.now(),
      templateId: tplId,
      templateLabel: tplLabel,
      aConditions: aConds,
      ifConditions: [],
      thenConditions: []
    }
    if (specifications.value.some(spec => isSameSpecification(spec, item))) {
      ElMessage.warning(t('app.specDuplicate') || '已经存在一条内容完全相同的规约')
      return
    }
    specifications.value.push(item)
    await saveSpecsToServer()
    return
  }

  if (mode === 'ifThen') {
    if (!ifConds.length || !thenConds.length) {
      ElMessage.warning(t('app.specNeedIf') || '请完善 IF/THEN 条件')
      return
    }
    const item: Specification = {
      id: 'spec_' + Date.now(),
      templateId: tplId,
      templateLabel: tplLabel,
      aConditions: [],
      ifConditions: ifConds,
      thenConditions: thenConds
    }
    if (specifications.value.some(spec => isSameSpecification(spec, item))) {
      ElMessage.warning(t('app.specDuplicate') || '已经存在一条内容完全相同的规约')
      return
    }
    specifications.value.push(item)
    await saveSpecsToServer()
    return
  }
}

const deleteSpecification = async (id: string) => {
  specifications.value = specifications.value.filter(s => s.id !== id)
  await saveSpecsToServer()
}

/* =================================================================================
 * 8. Context Menu & Deletion
 * ================================================================================= */

const onNodeContext = (node: DeviceNode) => {
  const tpl = deviceTemplates.value.find(t => t.name === node.templateName)
  dialogMeta.nodeId = node.id
  dialogMeta.label = node.label
  dialogMeta.deviceName = tpl ? tpl.manifest.Name : node.templateName
  dialogMeta.description = tpl ? tpl.manifest.Description : ''
  dialogMeta.manifest = tpl ? tpl.manifest : null
  dialogMeta.rules = edges.value.filter(e => e.from === node.id || e.to === node.id)
  dialogMeta.specs = specifications.value.filter(spec => isSpecRelatedToNode(spec, node.id))
  dialogVisible.value = true
}

const handleDialogSave = async (newLabel: string) => {
  const exists = nodes.value.some(n => n.label === newLabel && n.id !== dialogMeta.nodeId)
  if (exists) {
    ElMessage.error(t('app.nameExists') || '该名称已存在，请换一个')
    return
  }
  const node = nodes.value.find(n => n.id === dialogMeta.nodeId)
  if (!node) {
    dialogVisible.value = false
    return
  }

  node.label = newLabel
  await saveNodesToServer()

  const rulesChanged = updateRulesForNodeRename(edges.value, node.id, newLabel)
  if (rulesChanged) await saveEdgesToServer()

  const specChanged = updateSpecsForNodeRename(specifications.value, node.id, newLabel)
  if (specChanged) await saveSpecsToServer()

  dialogMeta.label = newLabel
  dialogMeta.specs = specifications.value.filter(spec => isSpecRelatedToNode(spec, node.id))
  dialogVisible.value = false
}

const forceDeleteNode = async (nodeId: string) => {
  nodes.value = nodes.value.filter(n => n.id !== nodeId)
  edges.value = edges.value.filter(e => e.from !== nodeId && e.to !== nodeId)

  const { nextSpecs, removed } = removeSpecsForNode(specifications.value, nodeId)
  specifications.value = nextSpecs

  await saveNodesToServer()
  await saveEdgesToServer()
  await saveSpecsToServer()

  if (removed.length > 0) {
    ElMessage.info(t('app.specsDeletedWithNode') || '已同时删除与该设备相关的规约')
  }
}

const deleteCurrentNodeWithConfirm = (nodeId: string) => {
  const hasEdges = edges.value.some(e => e.from === nodeId || e.to === nodeId)
  const hasSpecs = specifications.value.some(spec => isSpecRelatedToNode(spec, nodeId))

  const doDelete = async () => {
    await forceDeleteNode(nodeId)
    dialogVisible.value = false
  }

  if (!hasEdges && !hasSpecs) {
    void doDelete()
    return
  }

  ElMessageBox.confirm(
      t('app.deleteNodeWithRelationsConfirm') || '该设备有关联规则或规约，确认删除？',
      t('app.warning') || '警告',
      { type: 'warning', confirmButtonText: t('app.delete'), cancelButtonText: t('app.cancel') }
  ).then(() => doDelete()).catch(() => {})
}

const handleDialogDelete = () => {
  if (!dialogMeta.nodeId) return
  deleteCurrentNodeWithConfirm(dialogMeta.nodeId)
}

const deleteNodeFromStatus = (nodeId: string) => deleteCurrentNodeWithConfirm(nodeId)

const deleteEdgeFromStatus = async (edgeId: string) => {
  edges.value = edges.value.filter(e => e.id !== edgeId)
  await saveEdgesToServer()
}

/* =================================================================================
 * 9. API Interactions (Save)
 * ================================================================================= */

const saveLayoutToServer = async () => {
  const payload: BoardLayoutDto = {
    input: panelPositions.input,
    status: panelPositions.status,
    dockState: {
      input: { ...panelDockState.input },
      status: { ...panelDockState.status }
    },
    canvasPan: canvasPan.value,
    canvasZoom: canvasZoom.value
  }
  try {
    await boardApi.saveLayout(payload)
  } catch (e) {
    console.error('saveLayout error', e)
    ElMessage.error(t('app.saveLayoutFailed') || '保存画布布局失败')
  }
}

const saveNodesToServer = async () => {
  try { await boardApi.saveNodes(nodes.value) }
  catch (e) { ElMessage.error(t('app.saveNodesFailed') || '保存设备节点失败') }
}

const saveEdgesToServer = async () => {
  try { await boardApi.saveEdges(edges.value) }
  catch (e) { ElMessage.error(t('app.saveEdgesFailed') || '保存规则连线失败') }
}

const saveSpecsToServer = async () => {
  try { await boardApi.saveSpecs(specifications.value) }
  catch (e) { ElMessage.error(t('app.saveSpecsFailed') || '保存规约失败') }
}

/* =================================================================================
 * 10. Lifecycle & Watchers
 * ================================================================================= */

const initDefaultDevices = () => {
  const cached = loadDeviceTemplates()
  if (cached.length) {
    deviceTemplates.value = cached
    return
  }
  deviceTemplates.value = defaultDeviceTemplates
  saveDeviceTemplates(defaultDeviceTemplates)
}

onMounted(async () => {
  initDefaultDevices()

  // Load Data
  try { nodes.value = (await boardApi.getNodes()).data } catch { nodes.value = [] }
  try { edges.value = (await boardApi.getEdges()).data } catch { edges.value = [] }
  try { specifications.value = (await boardApi.getSpecs()).data } catch { specifications.value = [] }

  // Load Layout
  try {
    const res = await boardApi.getLayout()
    const layout = res.data

    // Panel Position
    if (layout?.input && layout?.status) {
      panelPositions.input = layout.input
      panelPositions.status = layout.status
    } else {
      panelPositions.input = { x: DEFAULT_PANEL_PADDING, y: DEFAULT_PANEL_PADDING }
      panelPositions.status = {
        x: window.innerWidth - getCardWidth() - DEFAULT_PANEL_PADDING,
        y: DEFAULT_PANEL_PADDING
      }
    }

    // Dock State
    if (layout?.dockState) {
      if (layout.dockState.input) Object.assign(panelDockState.input, layout.dockState.input)
      if (layout.dockState.status) Object.assign(panelDockState.status, layout.dockState.status)
    }

    // [Fix] Ensure panels are on screen
    clampPanelsToScreen()

    // Canvas
    if (layout?.canvasPan) canvasPan.value = layout.canvasPan
    if (typeof layout?.canvasZoom === 'number') {
      canvasZoom.value = Math.min(MAX_ZOOM, Math.max(MIN_ZOOM, layout.canvasZoom))
    }
  } catch {
    // Fallback
    panelPositions.input = { x: DEFAULT_PANEL_PADDING, y: DEFAULT_PANEL_PADDING }
    panelPositions.status = {
      x: window.innerWidth - getCardWidth() - DEFAULT_PANEL_PADDING,
      y: DEFAULT_PANEL_PADDING
    }
  }

  // Load Active Folders
  try {
    const res = await boardApi.getActive()
    if (Array.isArray(res.data?.input)) inputActive.value = res.data.input
    if (Array.isArray(res.data?.status)) statusActive.value = res.data.status
  } catch {}

  window.addEventListener('keydown', onGlobalKeydown)
  window.addEventListener('resize', clampPanelsToScreen)
})

watch(
    () => ({ input: inputActive.value, status: statusActive.value }),
    async val => {
      try { await boardApi.saveActive(val) }
      catch { ElMessage.error(t('app.saveActiveFailed') || '保存折叠面板状态失败') }
    },
    { deep: true }
)

watch(canvasZoom, () => void saveLayoutToServer())

onBeforeUnmount(() => {
  window.removeEventListener('keydown', onGlobalKeydown)
  window.removeEventListener('resize', clampPanelsToScreen)
  window.removeEventListener('pointermove', onCanvasPointerMove)
  window.removeEventListener('pointerup', onCanvasPointerUp)
})
</script>

<template>
  <!-- [Fix] @wheel.ctrl.prevent 阻止浏览器原生缩放 -->
  <div class="iot-board" @wheel.ctrl.prevent="onBoardWheel">
    <CanvasBoard
        :nodes="nodes"
        :edges="edges"
        :pan="canvasPan"
        :zoom="canvasZoom"
        :get-node-icon="getNodeIcon"
        :get-node-label-style="getNodeLabelStyle"
        @canvas-pointerdown="onCanvasPointerDown"
        @canvas-dragover="onCanvasDragOver"
        @canvas-drop="onCanvasDrop"
        @canvas-enter="onCanvasEnter"
        @canvas-leave="onCanvasLeave"
        @node-context="onNodeContext"
        @node-moved-or-resized="handleNodeMovedOrResized"
    />

    <div
        :class="getCardClasses('input')"
        :style="{ left: panelPositions.input.x + 'px', top: panelPositions.input.y + 'px' }"
        @pointerdown="onPanelPointerDownWrapper($event, 'input')"
    >
      <el-tooltip
          :disabled="!panelDockState.input.isDocked"
          :content="t('app.restoreInput') || '点击恢复输入面板'"
          placement="right"
      >
        <div class="docked-icon-container">
          <el-icon :size="24"><Edit /></el-icon>
        </div>
      </el-tooltip>

      <div class="card-header">
        <span class="card-title">
           <el-icon style="margin-right: 6px; vertical-align: middle"><Edit /></el-icon>
           {{ t('app.input') }}
        </span>
        <div class="dock-close-btn" @click.stop="handleManualDock('input')" title="收起面板">
          <el-icon><Close /></el-icon>
        </div>
      </div>

      <div class="card-body">
        <InputPanel
            v-model:active="inputActive"
            :device-templates="deviceTemplates"
            :nodes="nodes"
            :spec-templates="specTemplates"
            @create-device="handleCreateDevice"
            @add-rule="handleAddRule"
            @add-spec="handleAddSpec"
            @device-drag-start="onDeviceDragStart"
            @device-drag-end="onDeviceDragEnd"
            :get-template-init-icon="getTemplateInitIcon"
        />
      </div>
    </div>

    <div
        :class="getCardClasses('status')"
        :style="{ left: panelPositions.status.x + 'px', top: panelPositions.status.y + 'px' }"
        @pointerdown="onPanelPointerDownWrapper($event, 'status')"
    >
      <el-tooltip
          :disabled="!panelDockState.status.isDocked"
          :content="t('app.restoreStatus') || '点击恢复状态面板'"
          placement="left"
      >
        <div class="docked-icon-container">
          <el-icon :size="24"><Platform /></el-icon>
        </div>
      </el-tooltip>

      <div class="card-header">
        <span class="card-title">
           <el-icon style="margin-right: 6px; vertical-align: middle"><Platform /></el-icon>
           {{ t('app.status') }}
        </span>
        <div class="dock-close-btn" @click.stop="handleManualDock('status')" title="收起面板">
          <el-icon><Close /></el-icon>
        </div>
      </div>

      <div class="card-body">
        <StatusPanel
            v-model:active="statusActive"
            :nodes="nodes"
            :edges="edges"
            :specifications="specifications"
            @delete-node="deleteNodeFromStatus"
            @delete-edge="deleteEdgeFromStatus"
            @delete-spec="deleteSpecification"
        />
      </div>
    </div>

    <DeviceDialog
        :visible="dialogVisible"
        :device-name="dialogMeta.deviceName"
        :description="dialogMeta.description"
        :label="dialogMeta.label"
        :manifest="dialogMeta.manifest"
        :rules="dialogMeta.rules"
        :specs="dialogMeta.specs"
        @update:visible="dialogVisible = $event"
        @save="handleDialogSave"
        @delete="handleDialogDelete"
    />
  </div>
</template>
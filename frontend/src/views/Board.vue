<script setup lang="ts">
import { ref, reactive, onMounted, onBeforeUnmount, watch } from 'vue'
import { ElMessage, ElMessageBox } from 'element-plus'
import { useI18n } from 'vue-i18n'

import type {DeviceManifest, DeviceTemplate} from '../types/device'
import type {
  CanvasPan,
  DeviceNode,
  DeviceEdge,
  RuleForm,
  SpecTemplate,
  Specification,
  SpecCondition,
  SpecTemplateId,
  PanelPositions
} from '../types/board'

import { getDeviceIconPath, getNodeIcon } from '../utils/device'
import { getLinkPoints, getSelfLoopPath } from '../utils/geometry'
import {
  getUniqueLabel,
  updateEdgesForNode as updateEdgesByGeometry
} from '../utils/boardLayout'
import {
  loadDeviceTemplates,
  loadNodes,
  loadEdges,
  loadSpecs,
  loadPanels,
  loadPanelActive,
  saveDeviceTemplates,
  saveNodes,
  saveEdges,
  saveSpecs,
  savePanels,
  savePanelActive,
} from '../utils/boardStorage'
import { defaultSpecTemplates } from '../assets/config/specTemplates'
import { defaultDeviceTemplates } from '../assets/config/deviceTemplates'

import InputPanel from '../components/InputPanel.vue'
import StatusPanel from '../components/StatusPanel.vue'
import DeviceDialog from '../components/DeviceDialog.vue'

import '../styles/board.css'

const { t } = useI18n()

/* ========= 常量区域 ========= */

/** 浮动卡片距离视口边缘的默认间距（初始化时使用） */
const DEFAULT_PANEL_PADDING = 8

const CARD_WIDTH_MIN = 12 * 16 // 12rem * 16
const CARD_WIDTH_MAX = 24 * 16 // 24rem * 16
const CARD_WIDTH_RATIO = 0.24// 22vw

/** 设备与左侧 InputPanel 之间的水平间距 */
const NODE_MARGIN_RIGHT_OF_PANEL = 60

/** 节点网格布局：列数 & 间距（用于连续创建设备时的排布） */
const NODE_GRID_COLS = 4
const NODE_SPACING_X = 160
const NODE_SPACING_Y = 120
const NODE_START_Y = 140

/** 画布缩放配置 */
const MIN_ZOOM = 0.4
const MAX_ZOOM = 2
const ZOOM_STEP = 0.1

/** 节点标签缩放参考值（用于根据节点宽度调整字体大小） */
const BASE_NODE_WIDTH = 160
const BASE_FONT_SIZE = 16

// 单事件规约：只用 A（1,2,3,7）
const SINGLE_SPEC_IDS: SpecTemplateId[] = ['1', '2', '3', '7']
// A-B 规约：需要 IF(A) 和 THEN(B)（4,5,6）
const AB_SPEC_IDS: SpecTemplateId[] = ['4', '5', '6']

/* ========= 画布缩放 / 平移 ========= */

const canvasZoom = ref(1)
const isCanvasHovered = ref(false)
const canvasPan = ref<CanvasPan>({ x: 0, y: 0 })

let isPanning = false
let panStart = { x: 0, y: 0 }
let panOrigin = { x: 0, y: 0 }

const onCanvasEnter = () => (isCanvasHovered.value = true)
const onCanvasLeave = () => (isCanvasHovered.value = false)

/**
 * Ctrl + 滚轮 缩放画布
 */
const onCanvasWheel = (e: WheelEvent) => {
  if (!isCanvasHovered.value) return
  if (!e.ctrlKey) return
  e.preventDefault()

  if (e.deltaY > 0) {
    canvasZoom.value = Math.max(MIN_ZOOM, canvasZoom.value - ZOOM_STEP)
  } else {
    canvasZoom.value = Math.min(MAX_ZOOM, canvasZoom.value + ZOOM_STEP)
  }
}

/**
 * Ctrl + (= / + / - / 0) 键盘缩放
 */
const onGlobalKeydown = (e: KeyboardEvent) => {
  if (!isCanvasHovered.value) return
  if (!e.ctrlKey) return
  if (['=', '+', '-', '0'].includes(e.key)) e.preventDefault()

  if (e.key === '=' || e.key === '+') {
    canvasZoom.value = Math.min(MAX_ZOOM, canvasZoom.value + ZOOM_STEP)
  } else if (e.key === '-') {
    canvasZoom.value = Math.max(MIN_ZOOM, canvasZoom.value - ZOOM_STEP)
  } else if (e.key === '0') {
    canvasZoom.value = 1
  }
}

/**
 * 按住鼠标左键在空白画布上拖拽，实现平移
 */
const onCanvasPointerDown = (e: PointerEvent) => {
  isPanning = true
  panStart = { x: e.clientX, y: e.clientY }
  panOrigin = { x: canvasPan.value.x, y: canvasPan.value.y }
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

const onCanvasPointerUp = () => {
  isPanning = false
  window.removeEventListener('pointermove', onCanvasPointerMove)
  window.removeEventListener('pointerup', onCanvasPointerUp)
}

/**
 * 根据当前视口宽度按 clamp 规则计算浮动卡片宽度
 * 与 CSS 的 width: clamp(20rem, 32vw, 32rem) 保持一致
 */
const getCardWidth = () => {
  const w = window.innerWidth * CARD_WIDTH_RATIO
  return Math.min(CARD_WIDTH_MAX, Math.max(CARD_WIDTH_MIN, w))
}

/* ========= 浮动卡片位置（可拖拽 + 持久化） ========= */

type PanelKey = 'left' | 'status'

/** 当前两张浮动卡片的位置（像素） */
const panelPositions = reactive<Record<PanelKey, { x: number; y: number }>>({
  left: { x: 24, y: 24 },
  status: { x: 1040, y: 80 }
})

let draggingPanel: PanelKey | null = null
let panelDragStart = { x: 0, y: 0 }
let panelStartPos = { x: 0, y: 0 }

/**
 * 按住卡片头部开始拖拽
 */
const onPanelPointerDown = (e: PointerEvent, key: PanelKey) => {
  draggingPanel = key
  panelDragStart = { x: e.clientX, y: e.clientY }
  panelStartPos = { ...panelPositions[key] }
  window.addEventListener('pointermove', onPanelPointerMove)
  window.addEventListener('pointerup', onPanelPointerUp)
}

/**
 * 拖拽过程持续更新卡片位置
 */
const onPanelPointerMove = (e: PointerEvent) => {
  if (!draggingPanel) return
  const dx = e.clientX - panelDragStart.x
  const dy = e.clientY - panelDragStart.y
  const pos = panelPositions[draggingPanel]
  pos.x = panelStartPos.x + dx
  pos.y = panelStartPos.y + dy
}

/**
 * 拖拽结束：移除监听并将最新位置写入 sessionStorage
 */
const onPanelPointerUp = () => {
  const panelsToSave: PanelPositions = {
    left: { ...panelPositions.left },
    status: { ...panelPositions.status }
  }
  savePanels(panelsToSave)

  draggingPanel = null
  window.removeEventListener('pointermove', onPanelPointerMove)
  window.removeEventListener('pointerup', onPanelPointerUp)
}

// 判断点击目标是否在可交互控件上（按钮、输入框等）
const isInteractiveTarget = (el: HTMLElement | null): boolean => {
  if (!el) return false
  const interactiveSelectors =
      'input, textarea, select, button, a, [role="button"],' +
      '.el-input, .el-select, .el-button, .el-checkbox, .el-radio,' +
      '.el-switch, .el-slider, .el-table, .el-scrollbar'
  return !!el.closest(interactiveSelectors)
}

// 卡片整体的 pointerdown 包装：过滤交互控件后再真正开始拖拽
const onPanelPointerDownWrapper = (e: PointerEvent, key: PanelKey) => {
  const target = e.target as HTMLElement | null
  if (isInteractiveTarget(target)) {
    // 点在表单/按钮上时，不拖拽
    return
  }
  onPanelPointerDown(e, key)
}

/* ========= 核心数据 ========= */

const deviceTemplates = ref<DeviceTemplate[]>([])
const nodes = ref<DeviceNode[]>([])
const edges = ref<DeviceEdge[]>([])
const specifications = ref<Specification[]>([])
const specTemplates = ref<SpecTemplate[]>(defaultSpecTemplates)

/** InputPanel 折叠面板默认展开项 */
const inputActive = ref<string[]>(['devices', 'rules', 'specs'])
/** StatusPanel 折叠面板默认展开项 */
const statusActive = ref<string[]>(['devices', 'edges', 'specs'])

/* ========= 节点图标 / 标签样式 ========= */

/** 根据模板初始状态获取侧栏图标路径 */
const getTemplateInitIcon = (tpl: DeviceTemplate) => {
  const folder = tpl.name
  const initState = tpl.manifest?.InitState || 'Working'
  return getDeviceIconPath(folder, initState)
}

/**
 * 根据节点宽度缩放文字大小，防止缩放过大/过小导致标签溢出或过小
 */
const getNodeLabelStyle = (node: DeviceNode) => {
  const ratio = node.width / BASE_NODE_WIDTH
  const scale = Math.min(Math.max(ratio, 0.75), 1.5)
  const fontSize = BASE_FONT_SIZE * scale

  return {
    fontSize: fontSize + 'px',
    maxWidth: node.width - 16 + 'px' // 给左右留一点内边距
  }
}

/* ========= 节点布局：避免重叠 & 远离左面板 ========= */

/**
 * 创建新设备节点时的默认位置：
 * - X 方向：从左侧面板右侧开始，向右偏移 NODE_MARGIN_RIGHT_OF_PANEL，再按列增量
 * - Y 方向：从 NODE_START_Y 开始按行增量
 * 这样既不会盖住 InputPanel，又能避免多个节点重叠。
 */
const getNextNodePosition = (): { x: number; y: number } => {
  const count = nodes.value.length
  const col = count % NODE_GRID_COLS
  const row = Math.floor(count / NODE_GRID_COLS)

  const baseX =
      panelPositions.left.x +
      getCardWidth() +
      NODE_MARGIN_RIGHT_OF_PANEL +
      col * NODE_SPACING_X

  const baseY = NODE_START_Y + row * NODE_SPACING_Y
  return { x: baseX, y: baseY }
}

/* ========= 节点拖拽 / 缩放 ========= */

let dragNode: DeviceNode | null = null
let dragStart = { x: 0, y: 0 }
let nodeStart = { x: 0, y: 0 }

/** 调用通用的 geometry 工具，更新与某个节点有关的所有边的端点坐标 */
const updateEdgesForNode = (nodeId: string) => {
  updateEdgesByGeometry(nodeId, nodes.value, edges.value)
}

/**
 * 节点拖拽开始
 */
const onNodePointerDown = (e: PointerEvent, node: DeviceNode) => {
  e.preventDefault()
  dragNode = node
  dragStart = { x: e.clientX, y: e.clientY }
  nodeStart = { x: node.position.x, y: node.position.y }
  window.addEventListener('pointermove', onNodePointerMove)
  window.addEventListener('pointerup', onNodePointerUp)
}

/**
 * 节点拖拽过程：更新 position 并刷新连线
 */
const onNodePointerMove = (e: PointerEvent) => {
  if (!dragNode) return
  const dx = e.clientX - dragStart.x
  const dy = e.clientY - dragStart.y
  dragNode.position.x = nodeStart.x + dx
  dragNode.position.y = nodeStart.y + dy
  updateEdgesForNode(dragNode.id)
}

/**
 * 节点拖拽结束：保存节点 & 边数据
 */
const onNodePointerUp = () => {
  if (dragNode) {
    saveNodes(nodes.value)
    saveEdges(edges.value)
  }
  dragNode = null
  window.removeEventListener('pointermove', onNodePointerMove)
  window.removeEventListener('pointerup', onNodePointerUp)
}

// ========= 边 / 自环几何 =========

const getSelfLoopD = (edge: DeviceEdge) => {
  const node = nodes.value.find(n => n.id === edge.from)
  if (!node) return ''
  return getSelfLoopPath(node)
}


/* ----- 节点缩放（四角手柄） ----- */

let resizingNode: DeviceNode | null = null
let resizeStart = { x: 0, y: 0 }
let startSize = { w: 0, h: 0 }
let startPos = { x: 0, y: 0 }
let resizeDir: 'tl' | 'tr' | 'bl' | 'br' = 'br'

const onPointerDownResize = (
    e: PointerEvent,
    node: DeviceNode,
    dir: 'tl' | 'tr' | 'bl' | 'br' = 'br'
) => {
  e.stopPropagation()
  e.preventDefault()
  resizingNode = node
  resizeDir = dir
  resizeStart = { x: e.clientX, y: e.clientY }
  startSize = { w: node.width, h: node.height }
  startPos = { x: node.position.x, y: node.position.y }
  window.addEventListener('pointermove', onPointerMoveResize)
  window.addEventListener('pointerup', onPointerUpResize)
}

const onPointerMoveResize = (e: PointerEvent) => {
  if (!resizingNode) return
  const dx = e.clientX - resizeStart.x
  const dy = e.clientY - resizeStart.y
  const minW = 80
  const minH = 60

  let newW = startSize.w
  let newH = startSize.h
  let newX = startPos.x
  let newY = startPos.y

  if (resizeDir === 'br') {
    newW = Math.max(minW, startSize.w + dx)
    newH = Math.max(minH, startSize.h + dy)
  } else if (resizeDir === 'bl') {
    newW = Math.max(minW, startSize.w - dx)
    newH = Math.max(minH, startSize.h + dy)
    newX = startPos.x + (startSize.w - newW)
  } else if (resizeDir === 'tr') {
    newW = Math.max(minW, startSize.w + dx)
    newH = Math.max(minH, startSize.h - dy)
    newY = startPos.y + (startSize.h - newH)
  } else if (resizeDir === 'tl') {
    newW = Math.max(minW, startSize.w - dx)
    newH = Math.max(minH, startSize.h - dy)
    newX = startPos.x + (startSize.w - newW)
    newY = startPos.y + (startSize.h - newH)
  }

  resizingNode.width = newW
  resizingNode.height = newH
  resizingNode.position.x = newX
  resizingNode.position.y = newY

  updateEdgesForNode(resizingNode.id)
}

const onPointerUpResize = () => {
  if (resizingNode) {
    saveNodes(nodes.value)
    saveEdges(edges.value)
  }
  resizingNode = null
  window.removeEventListener('pointermove', onPointerMoveResize)
  window.removeEventListener('pointerup', onPointerUpResize)
}

/* ========= 设备创建 / 拖拽 ========= */

/**
 * 在指定位置基于模板创建设备节点
 */
const createDeviceInstanceAt = (
    tpl: DeviceTemplate,
    pos: { x: number; y: number }
) => {
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
  saveNodes(nodes.value)
}

/**
 * 左键点击 InputPanel 中的设备模板时，在画布上创建一个新节点
 */
const handleCreateDevice = (tpl: DeviceTemplate) => {
  const pos = getNextNodePosition()
  createDeviceInstanceAt(tpl, pos)
}

/* ----- 侧栏拖拽创建设备 ----- */

const draggingTplName = ref<string | null>(null)

const onDeviceDragStart = (tpl: DeviceTemplate) => {
  draggingTplName.value = tpl.name
}

const onDeviceDragEnd = () => {
  draggingTplName.value = null
}

const onCanvasDragOver = (e: DragEvent) => {
  if (e.dataTransfer) e.dataTransfer.dropEffect = 'copy'
}

/**
 * 支持从左侧列表拖拽到画布任意位置放置设备
 */
const onCanvasDrop = (e: DragEvent) => {
  if (!draggingTplName.value) return
  const tpl = deviceTemplates.value.find(d => d.name === draggingTplName.value)
  if (!tpl) return

  const rect = (e.currentTarget as HTMLElement).getBoundingClientRect()
  const x = e.clientX - rect.left
  const y = e.clientY - rect.top
  createDeviceInstanceAt(tpl, { x, y })

  draggingTplName.value = null
}

/* ========= IFTTT 规则（来自 InputPanel） ========= */

/**
 * 由 InputPanel 触发，添加一条 IFTTT 规则 + 画布上的连线
 */
const handleAddRule = (payload: RuleForm) => {
  const { fromId, fromApi, toId, toApi } = payload
  if (!fromId || !fromApi || !toId || !toApi) {
    ElMessage.warning(
        t('app.fillAllRuleFields') || '请完整选择源/目标设备及 API'
    )
    return
  }

  const fromNode = nodes.value.find(n => n.id === fromId)
  const toNode = nodes.value.find(n => n.id === toId)
  if (!fromNode || !toNode) return

  const { fromPoint, toPoint } = getLinkPoints(fromNode, toNode)

  // 现在：不再根据 API 自动更新目标节点状态，只记录一条规则边
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
  saveEdges(edges.value)
}

/* ========= 规约（来自 InputPanel） ========= */
/** 一行条件是否“完全空”的判断 */
const isEmptyCondition = (c: SpecCondition) => {
  return (
      !c.deviceId &&
      !c.targetType &&
      !c.key &&
      !c.relation &&
      !c.value
  )
}

/** 一行条件是否“完整” —— 严格按照表单渲染逻辑来 */
const isCompleteCondition = (c: SpecCondition) => {
  if (isEmptyCondition(c)) return false

  // 没选设备 / 类型 / 目标键，一定不完整
  if (!c.deviceId || !c.targetType || !c.key) return false

  // ① API：设备 + 类型(api) + key 就够了
  if (c.targetType === 'api') {
    return true
  }

  // ② state / variable：还必须要有 relation + value
  if (c.targetType === 'state' || c.targetType === 'variable') {
    return !!c.relation && !!c.value
  }

  // 其他未知类型，一律当不完整处理（防御性）
  return false
}

/**
 * 对某一侧（A / IF / THEN）的条件做校验并去掉“完全空”的行
 * - 完全空行：丢弃
 * - 非空但不完整：标记 hasIncomplete = true
 * - 完整：进入 cleaned
 */
const validateAndCleanConditions = (conds: SpecCondition[]) => {
  const cleaned: SpecCondition[] = []
  let hasIncomplete = false

  for (const c of conds) {
    if (isEmptyCondition(c)) {
      // 完全空行 → 直接忽略
      continue
    }

    if (!isCompleteCondition(c)) {
      // 有内容，但没填完 → 整体标记为不完整
      hasIncomplete = true
      break
    }

    cleaned.push(c)
  }

  return { cleaned, hasIncomplete }
}

/**
 * 将 InputPanel 中配置好的规约实例化为一条 Specification 并存储
 */
const handleAddSpec = (payload: {
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

  // 先对三侧分别做“去空行 + 检查是否有半残行”
  const aCheck = validateAndCleanConditions(payload.aConditions)
  const ifCheck = validateAndCleanConditions(payload.ifConditions)
  const thenCheck = validateAndCleanConditions(payload.thenConditions)

  if (aCheck.hasIncomplete || ifCheck.hasIncomplete || thenCheck.hasIncomplete) {
    ElMessage.warning(
        t('app.specRowIncomplete') ||
        '存在未填完整的条件，请删除该行或补全所有字段'
    )
    return
  }

  const aConds = aCheck.cleaned
  const ifConds = ifCheck.cleaned
  const thenConds = thenCheck.cleaned

  // ① 单事件规约：1 / 2 / 3 / 7
  if (SINGLE_SPEC_IDS.includes(tplId)) {
    if (!aConds.length) {
      ElMessage.warning(
          t('app.specNeedA') || '请至少配置一个事件 A 条件'
      )
      return
    }

    const tplLabel =
        specTemplates.value.find(t => t.id === tplId)?.label || tplId

    const item: Specification = {
      id: 'spec_' + Date.now(),
      templateId: tplId,
      templateLabel: tplLabel,
      aConditions: aConds,
      ifConditions: [],
      thenConditions: []
    }

    specifications.value.push(item)
    saveSpecs(specifications.value)
    return
  }

  // ② A-B 规约：4 / 5 / 6
  if (AB_SPEC_IDS.includes(tplId)) {
    if (!ifConds.length) {
      ElMessage.warning(
          t('app.specNeedIf') || '请先完成 IF 部分（事件 A 的条件）'
      )
      return
    }
    if (!thenConds.length) {
      ElMessage.warning(
          t('app.specNeedThen') || '请先完成 THEN 部分（事件 B 的条件）'
      )
      return
    }

    const tplLabel =
        specTemplates.value.find(t => t.id === tplId)?.label || tplId

    const item: Specification = {
      id: 'spec_' + Date.now(),
      templateId: tplId,
      templateLabel: tplLabel,
      aConditions: [],
      ifConditions: ifConds,
      thenConditions: thenConds
    }

    specifications.value.push(item)
    saveSpecs(specifications.value)
    return
  }

  // 理论不会走到这里，防御性代码
  ElMessage.error('Unknown specification template id: ' + tplId)
}

/** 从 StatusPanel 删除某条规约 */
const deleteSpecification = (id: string) => {
  specifications.value = specifications.value.filter(s => s.id !== id)
  saveSpecs(specifications.value)
}

/* ========= 右键设备弹窗 ========= */

const dialogVisible = ref(false)
const dialogMeta = reactive<{
  nodeId: string
  deviceName: string
  description: string
  label: string
  manifest: DeviceManifest | null
  rules: DeviceEdge[]
  specs: Specification[]
}>({
  nodeId: '',
  deviceName: '',
  description: '',
  label: '',
  manifest: null,
  rules: [],
  specs: []
})

/**
 * 右键点击设备节点，打开设备信息弹窗
 */
const onNodeContext = (node: DeviceNode) => {
  const tpl = deviceTemplates.value.find(t => t.name === node.templateName)

  dialogMeta.nodeId = node.id
  dialogMeta.label = node.label
  dialogMeta.deviceName = tpl ? tpl.manifest.Name : node.templateName
  dialogMeta.description = tpl ? tpl.manifest.Description : ''
  dialogMeta.manifest = tpl ? tpl.manifest : null

  // 与该节点相关的 IFTTT 规则（连线）
  dialogMeta.rules = edges.value.filter(
      e => e.from === node.id || e.to === node.id
  )

  // 与该节点相关的规约：
  // 这里先用简单策略：自然语言里包含设备实例名即可视为“相关”
  // dialogMeta.specs = specifications.value.filter(spec =>
  //     (spec.naturalLanguage ?? '').includes(node.label)
  // )

  dialogVisible.value = true
}
/**
 * 当设备重命名时，更新所有相关边的 fromLabel / toLabel
 */
const refreshEdgeLabelsForNode = (nodeId: string, newLabel: string) => {
  let changed = false
  edges.value.forEach(e => {
    if (e.from === nodeId && e.fromLabel !== newLabel) {
      e.fromLabel = newLabel
      changed = true
    }
    if (e.to === nodeId && e.toLabel !== newLabel) {
      e.toLabel = newLabel
      changed = true
    }
  })
  if (changed) saveEdges(edges.value)
}

/**
 * 弹窗保存：校验重名 -> 写回节点列表 -> 同步连线标签
 */
const handleDialogSave = (newLabel: string) => {
  const exists = nodes.value.some(
      n => n.label === newLabel && n.id !== dialogMeta.nodeId
  )
  if (exists) {
    ElMessage.error(t('app.nameExists') || '该名称已存在，请换一个')
    return
  }
  const node = nodes.value.find(n => n.id === dialogMeta.nodeId)
  if (node) {
    node.label = newLabel
    saveNodes(nodes.value)
    refreshEdgeLabelsForNode(node.id, node.label)
  }
  dialogMeta.label = newLabel
  dialogVisible.value = false
}

/** 真正删除节点 + 相关连线（不弹窗） */
const forceDeleteNode = (nodeId: string) => {
  nodes.value = nodes.value.filter(n => n.id !== nodeId)
  edges.value = edges.value.filter(e => e.from !== nodeId && e.to !== nodeId)
  saveNodes(nodes.value)
  saveEdges(edges.value)
}

/**
 * 删除节点前检查是否有关联连线，必要时弹出确认框
 */
const deleteCurrentNodeWithConfirm = (nodeId: string) => {
  const hasEdges = edges.value.some(e => e.from === nodeId || e.to === nodeId)
  const doDelete = () => {
    forceDeleteNode(nodeId)
    dialogVisible.value = false
  }

  if (!hasEdges) {
    doDelete()
    return
  }

  ElMessageBox.confirm(
      t('app.deleteNodeWithEdgesConfirm') ||
      '该设备存在与其他设备的规则（连线），删除设备将同时删除这些规则，是否继续？',
      t('app.warning') || '警告',
      {
        type: 'warning',
        confirmButtonText: t('app.delete') || '删除',
        cancelButtonText: t('app.cancel') || '取消'
      }
  )
      .then(() => doDelete())
      .catch(() => {})
}

/** 弹窗中的“删除设备”按钮 */
const handleDialogDelete = () => {
  if (!dialogMeta.nodeId) return
  deleteCurrentNodeWithConfirm(dialogMeta.nodeId)
}

/* ========= StatusPanel 删除回调 ========= */

const deleteNodeFromStatus = (nodeId: string) => {
  deleteCurrentNodeWithConfirm(nodeId)
}

const deleteEdgeFromStatus = (edgeId: string) => {
  edges.value = edges.value.filter(e => e.id !== edgeId)
  saveEdges(edges.value)
}

/* ========= 初始化 ========= */

/**
 * 设备模板初始化：
 * - 若 sessionStorage 中已有缓存，直接使用；
 * - 否则使用 assets/config 中的默认模板并写入缓存。
 */
const initDefaultDevices = () => {
  const cached = loadDeviceTemplates()
  if (cached.length) {
    deviceTemplates.value = cached
    return
  }
  deviceTemplates.value = defaultDeviceTemplates
  saveDeviceTemplates(defaultDeviceTemplates)
}

onMounted(() => {
  initDefaultDevices()
  nodes.value = loadNodes()
  edges.value = loadEdges()
  specifications.value = loadSpecs()

  // 恢复浮动卡片位置；如果没有存储，则使用“左上角 / 右上角”默认布局
  const savedPanels = loadPanels()
  if (savedPanels) {
    panelPositions.left.x = savedPanels.left.x
    panelPositions.left.y = savedPanels.left.y
    panelPositions.status.x = savedPanels.status.x
    panelPositions.status.y = savedPanels.status.y
  } else {
    // 左边：左上角留一个 DEFAULT_PANEL_PADDING 的内边距
    panelPositions.left.x = DEFAULT_PANEL_PADDING
    panelPositions.left.y = DEFAULT_PANEL_PADDING

    // 右边：根据真实卡片宽度贴到右侧
    const cardWidth = getCardWidth()
    panelPositions.status.x =
        window.innerWidth - cardWidth - DEFAULT_PANEL_PADDING
    panelPositions.status.y = DEFAULT_PANEL_PADDING
  }

  const savedActive = loadPanelActive()
  if (savedActive) {
    if (Array.isArray(savedActive.input)) {
      inputActive.value = savedActive.input
    }
    if (Array.isArray(savedActive.status)) {
      statusActive.value = savedActive.status
    }
  }

  window.addEventListener('keydown', onGlobalKeydown)
})

watch(
    () => ({
      input: inputActive.value,
      status: statusActive.value
    }),
    val => {
      savePanelActive(val)
    },
    { deep: true }
)

onBeforeUnmount(() => {
  window.removeEventListener('keydown', onGlobalKeydown)
})
</script>

<template>
  <div class="iot-board">
    <!-- ===== 背景画布（节点 + 连线） ===== -->
    <div
        class="canvas"
        @pointerdown="onCanvasPointerDown"
        @dragover.prevent="onCanvasDragOver"
        @drop.prevent="onCanvasDrop"
        @mouseenter="onCanvasEnter"
        @mouseleave="onCanvasLeave"
        @wheel="onCanvasWheel"
    >
      <div
          class="canvas-inner"
          :style="{
          transform: `translate(${canvasPan.x}px, ${canvasPan.y}px) scale(${canvasZoom})`,
          transformOrigin: '0 0'
        }"
      >
        <!-- 连线层 -->
        <svg class="edge-layer">
          <defs>
            <marker
                id="arrow"
                markerWidth="10"
                markerHeight="10"
                refX="10"
                refY="3"
                orient="auto"
            >
              <!-- 箭头颜色也改成跟变量一致 -->
              <path d="M0,0 L0,6 L9,3 z" :fill="`var(--iot-color-edge)`"></path>
            </marker>
          </defs>

          <g v-for="edge in edges" :key="edge.id">
            <!-- 自环：from === to，用 path -->
            <path
                v-if="edge.from === edge.to"
                class="edge-line"
                :d="getSelfLoopD(edge)"
                marker-end="url(#arrow)"
            />
            <!-- 普通边：仍然用 line -->
            <line
                v-else
                class="edge-line"
                :x1="edge.fromPos.x"
                :y1="edge.fromPos.y"
                :x2="edge.toPos.x"
                :y2="edge.toPos.y"
                marker-end="url(#arrow)"
            />
          </g>
        </svg>

        <!-- 设备节点 -->
        <div
            v-for="node in nodes"
            :key="node.id"
            class="device-node"
            :style="{
            left: node.position.x + 'px',
            top: node.position.y + 'px',
            width: node.width + 'px',
            height: node.height + 'px'
          }"
            @pointerdown.stop="onNodePointerDown($event, node)"
            @contextmenu.prevent="onNodeContext(node)"
        >
          <img
              class="device-img"
              :src="getNodeIcon(node)"
              :alt="node.label"
              draggable="false"
              :style="{
              width: node.width * 0.55 + 'px',
              height: node.height * 0.35 + 'px'
            }"
          />
          <div class="device-label" :style="getNodeLabelStyle(node)">
            {{ node.label }}
          </div>

          <!-- 四角缩放手柄 -->
          <div
              class="resize-handle tl"
              @pointerdown.stop="onPointerDownResize($event, node, 'tl')"
          ></div>
          <div
              class="resize-handle tr"
              @pointerdown.stop="onPointerDownResize($event, node, 'tr')"
          ></div>
          <div
              class="resize-handle bl"
              @pointerdown.stop="onPointerDownResize($event, node, 'bl')"
          ></div>
          <div
              class="resize-handle br"
              @pointerdown.stop="onPointerDownResize($event, node, 'br')"
          ></div>
        </div>
      </div>
    </div>

    <!-- ===== 左侧浮动卡片：输入（设备 / 规则 / 规约） ===== -->
    <div
        class="floating-card input-card"
        :style="{ left: panelPositions.left.x + 'px', top: panelPositions.left.y + 'px' }"
        @pointerdown="onPanelPointerDownWrapper($event, 'left')"
    >
      <div class="card-header">
        <span class="card-title">{{ t('app.input') }}</span>
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

    <!-- ===== 右侧浮动卡片：状态（当前设备 / 规则 / 规约） ===== -->
    <div
        class="floating-card status-card"
        :style="{ left: panelPositions.status.x + 'px', top: panelPositions.status.y + 'px' }"
        @pointerdown="onPanelPointerDownWrapper($event, 'status')"
    >
      <div class="card-header">
        <span class="card-title">{{ t('app.status') }}</span>
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

    <!-- ===== 右键设备信息弹窗 ===== -->
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

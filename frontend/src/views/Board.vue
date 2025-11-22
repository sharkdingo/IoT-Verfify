<script setup lang="ts">
import { ref, reactive, onMounted, onBeforeUnmount, watch } from 'vue'
import { ElMessage, ElMessageBox } from 'element-plus'
import { useI18n } from 'vue-i18n'

import type { DeviceDialogMeta, DeviceTemplate } from '../types/device'
import type { CanvasPan } from '../types/canvas'
import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { RuleForm } from '../types/rule'
import type { PanelPositions } from '../types/panel'

import { getDeviceIconPath, getNodeIcon } from '../utils/device'
import { getUniqueLabel } from '../utils/canvas/nodeCreate'

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
  savePanelActive
} from '../utils/boardStorage'

import {
  getSpecMode,
  validateAndCleanConditions,
  isSameSpecification,
  isSpecRelatedToNode,
  removeSpecsForNode,
  updateSpecsForNodeRename
} from '../utils/spec'

import { defaultSpecTemplates } from '../assets/config/specTemplates'
import { defaultDeviceTemplates } from '../assets/config/deviceTemplates'

import InputPanel from '../components/InputPanel.vue'
import StatusPanel from '../components/StatusPanel.vue'
import DeviceDialog from '../components/DeviceDialog.vue'
import CanvasBoard from '../components/CanvasBoard.vue'

import '../styles/board.css'
import {
  SpecCondition,
  Specification,
  SpecTemplate,
  SpecTemplateId
} from '../types/spec'
import {
  updateRulesForNodeRename,
  getLinkPoints,
} from '../utils/rule'

const { t } = useI18n()

/* ========= 常量区域 ========= */

/** 浮动卡片距离视口边缘的默认间距（初始化时使用） */
const DEFAULT_PANEL_PADDING = 8

const CARD_WIDTH_MIN = 12 * 16 // 12rem * 16
const CARD_WIDTH_MAX = 24 * 16 // 24rem * 16
const CARD_WIDTH_RATIO = 0.24 // 24vw

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
 * （由 CanvasBoard 通过 @canvas-pointerdown 调用）
 */
const onCanvasPointerDown = (e: PointerEvent) => {
  // 只处理左键
  if (e.button !== 0) return
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

type PanelKey = 'input' | 'status'

/** 当前两张浮动卡片的位置（像素） */
const panelPositions = reactive<Record<PanelKey, { x: number; y: number }>>({
  input: { x: 24, y: 24 },
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
    input: { ...panelPositions.input },
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
      panelPositions.input.x +
      getCardWidth() +
      NODE_MARGIN_RIGHT_OF_PANEL +
      col * NODE_SPACING_X

  const baseY = NODE_START_Y + row * NODE_SPACING_Y
  return { x: baseX, y: baseY }
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

/**
 * CanvasBoard 通过 @canvas-dragover -> 交给此函数
 */
const onCanvasDragOver = (e: DragEvent) => {
  if (e.dataTransfer) e.dataTransfer.dropEffect = 'copy'
}

/**
 * CanvasBoard 通过 @canvas-drop -> 交给此函数
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

  // 不再根据 API 自动更新目标节点状态，只记录一条规则边
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

  // 三侧分别做“去空行 + 检查是否有半残行”
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

  // 根据模板 id 判定是单事件规约还是 IF/THEN 规约
  const mode = getSpecMode(tplId)
  const tplLabel =
      specTemplates.value.find(t => t.id === tplId)?.label || tplId

  // ① 单事件规约：1 / 2 / 3 / 7
  if (mode === 'single') {
    if (!aConds.length) {
      ElMessage.warning(
          t('app.specNeedA') || '请至少配置一个事件 A 条件'
      )
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
    const exists = specifications.value.some(spec =>
        isSameSpecification(spec, item)
    )
    if (exists) {
      ElMessage.warning(
          t('app.specDuplicate') || '已经存在一条内容完全相同的规约'
      )
      return
    }
    specifications.value.push(item)
    saveSpecs(specifications.value)
    return
  }
  // ② A-B 规约：4 / 5 / 6
  if (mode === 'ifThen') {
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
    const item: Specification = {
      id: 'spec_' + Date.now(),
      templateId: tplId,
      templateLabel: tplLabel,
      aConditions: [],
      ifConditions: ifConds,
      thenConditions: thenConds
    }
    const exists = specifications.value.some(spec =>
        isSameSpecification(spec, item)
    )
    if (exists) {
      ElMessage.warning(
          t('app.specDuplicate') || '已经存在一条内容完全相同的规约'
      )
      return
    }
    specifications.value.push(item)
    saveSpecs(specifications.value)
    return
  }
  // 理论上不会走到这里，防御性兜底
  ElMessage.error('Unknown specification template id: ' + tplId)
}

/** 从 StatusPanel 删除某条规约 */
const deleteSpecification = (id: string) => {
  specifications.value = specifications.value.filter(s => s.id !== id)
  saveSpecs(specifications.value)
}

/* ========= 右键设备弹窗 ========= */

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

/**
 * 右键点击设备节点，打开设备信息弹窗
 * （由 CanvasBoard 通过 @node-context 调用）
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
  // 与该节点相关的规约
  dialogMeta.specs = specifications.value.filter(spec =>
      isSpecRelatedToNode(spec, node.id)
  )
  dialogVisible.value = true
}

/**
 * 弹窗保存：校验重名 -> 写回节点列表 -> 同步连线标签 & 规约里的 deviceLabel
 */
const handleDialogSave = (newLabel: string) => {
  // 1) 重名校验
  const exists = nodes.value.some(
      n => n.label === newLabel && n.id !== dialogMeta.nodeId
  )
  if (exists) {
    ElMessage.error(t('app.nameExists') || '该名称已存在，请换一个')
    return
  }
  const node = nodes.value.find(n => n.id === dialogMeta.nodeId)
  if (!node) {
    dialogVisible.value = false
    return
  }
  // 2) 更新节点本身名字
  node.label = newLabel
  saveNodes(nodes.value)
  // 3) 同步规则（边）上的标签
  const rulesChanged = updateRulesForNodeRename(edges.value, node.id, newLabel)
  if (rulesChanged) {
    saveEdges(edges.value)
  }
  // 4) 同步规约里的 deviceLabel（通过 deviceId == node.id 判断）
  const specChanged = updateSpecsForNodeRename(
      specifications.value,
      node.id,
      newLabel
  )
  if (specChanged) {
    saveSpecs(specifications.value)
  }
  // 5) 更新弹窗里的显示数据
  dialogMeta.label = newLabel
  dialogMeta.specs = specifications.value.filter(spec =>
      isSpecRelatedToNode(spec, node.id)
  )
  dialogVisible.value = false
}

/** 真正删除节点 + 相关连线 + 相关规约（不再弹窗确认） */
const forceDeleteNode = (nodeId: string) => {
  // 1) 删节点
  nodes.value = nodes.value.filter(n => n.id !== nodeId)
  // 2) 删连线
  edges.value = edges.value.filter(e => e.from !== nodeId && e.to !== nodeId)
  // 3) 删规约（所有涉及该节点的规约）
  const { nextSpecs, removed } = removeSpecsForNode(
      specifications.value,
      nodeId
  )
  specifications.value = nextSpecs
  // 4) 持久化
  saveNodes(nodes.value)
  saveEdges(edges.value)
  saveSpecs(specifications.value)
  // 5) 如有规约被删，给出提示
  if (removed.length > 0) {
    ElMessage.info(
        t('app.specsDeletedWithNode') || '已同时删除与该设备相关的规约'
    )
  }
}

/**
 * 删除节点前检查是否有关联连线 / 规约，必要时弹出确认框
 */
const deleteCurrentNodeWithConfirm = (nodeId: string) => {
  const hasEdges = edges.value.some(e => e.from === nodeId || e.to === nodeId)
  const hasSpecs = specifications.value.some(spec =>
      isSpecRelatedToNode(spec, nodeId)
  )
  const doDelete = () => {
    forceDeleteNode(nodeId)
    dialogVisible.value = false
  }
  // 既没有边也没有规约，直接删
  if (!hasEdges && !hasSpecs) {
    doDelete()
    return
  }
  ElMessageBox.confirm(
      t('app.deleteNodeWithRelationsConfirm') ||
      '该设备存在与其他设备的规则（连线）或已参与规约，删除设备将同时删除这些规则和相关规约，是否继续？',
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

/* ========= CanvasBoard 回调：节点移动 / 缩放完成 ========= */

const handleNodeMovedOrResized = () => {
  // 这里目前只需要持久化；如后面要做“自动排版”等逻辑也可以在这里加
  saveNodes(nodes.value)
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
    panelPositions.input.x = savedPanels.input.x
    panelPositions.input.y = savedPanels.input.y
    panelPositions.status.x = savedPanels.status.x
    panelPositions.status.y = savedPanels.status.y
  } else {
    // 左边：左上角留一个 DEFAULT_PANEL_PADDING 的内边距
    panelPositions.input.x = DEFAULT_PANEL_PADDING
    panelPositions.input.y = DEFAULT_PANEL_PADDING

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
  window.removeEventListener('pointermove', onCanvasPointerMove)
  window.removeEventListener('pointerup', onCanvasPointerUp)
})
</script>

<template>
  <div class="iot-board">
    <!-- ===== 背景画布（节点 + 连线）抽离为 CanvasBoard ===== -->
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
        @canvas-wheel="onCanvasWheel"
        @node-context="onNodeContext"
        @node-moved-or-resized="handleNodeMovedOrResized"
    />

    <!-- ===== 浮动卡片：输入（设备 / 规则 / 规约） ===== -->
    <div
        class="floating-card input-card"
        :style="{ left: panelPositions.input.x + 'px', top: panelPositions.input.y + 'px' }"
        @pointerdown="onPanelPointerDownWrapper($event, 'input')"
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

    <!-- ===== 浮动卡片：状态（当前设备 / 规则 / 规约） ===== -->
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

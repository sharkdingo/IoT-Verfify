<script setup lang="ts">
import { ref, reactive, onMounted, onBeforeUnmount, watch } from 'vue'
import { ElMessage, ElMessageBox } from 'element-plus'
import { useI18n } from 'vue-i18n'

import type { DeviceDialogMeta, DeviceTemplate } from '../types/device'
import type { CanvasPan } from '../types/canvas'
import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { RuleForm } from '../types/rule'
import type { SpecCondition, Specification, SpecTemplate, SpecTemplateId } from '../types/spec'

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

import { defaultSpecTemplates } from '../assets/config/specTemplates'
import { defaultDeviceTemplates } from '../assets/config/deviceTemplates'

// 设备模板仍然用 sessionStorage
import { loadDeviceTemplates, saveDeviceTemplates } from '../utils/boardStorage'

// === 与后端交互的 API（请确保有 src/api/board.ts 并默认导出这些方法） ===
import boardApi from '@/api/board'

import InputPanel from '../components/InputPanel.vue'
import StatusPanel from '../components/StatusPanel.vue'
import DeviceDialog from '../components/DeviceDialog.vue'
import CanvasBoard from '../components/CanvasBoard.vue'

import '../styles/board.css'

const { t } = useI18n()

/* ========= 常量区域 ========= */

const DEFAULT_PANEL_PADDING = 8

const CARD_WIDTH_MIN = 12 * 16 // 12rem
const CARD_WIDTH_MAX = 24 * 16 // 24rem
const CARD_WIDTH_RATIO = 0.24    // 24vw

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

/* ========= 画布缩放 / 平移 ========= */

const canvasZoom = ref(1)
const isCanvasHovered = ref(false)
const canvasPan = ref<CanvasPan>({ x: 0, y: 0 })

let isPanning = false
let panStart = { x: 0, y: 0 }
let panOrigin = { x: 0, y: 0 }

const onCanvasEnter = () => (isCanvasHovered.value = true)
const onCanvasLeave = () => (isCanvasHovered.value = false)

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

const onCanvasPointerDown = (e: PointerEvent) => {
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

const onCanvasPointerUp = async () => {
  isPanning = false
  await saveLayoutToServer()
  window.removeEventListener('pointermove', onCanvasPointerMove)
  window.removeEventListener('pointerup', onCanvasPointerUp)
}

/* ========= 浮动卡片位置（可拖拽 + 持久化） ========= */

type PanelKey = 'input' | 'status'

const panelPositions = reactive<Record<PanelKey, { x: number; y: number }>>({
  input: { x: 24, y: 24 },
  status: { x: 1040, y: 80 }
})

let draggingPanel: PanelKey | null = null
let panelDragStart = { x: 0, y: 0 }
let panelStartPos = { x: 0, y: 0 }

const onPanelPointerDown = (e: PointerEvent, key: PanelKey) => {
  draggingPanel = key
  panelDragStart = { x: e.clientX, y: e.clientY }
  panelStartPos = { ...panelPositions[key] }
  window.addEventListener('pointermove', onPanelPointerMove)
  window.addEventListener('pointerup', onPanelPointerUp)
}

const onPanelPointerMove = (e: PointerEvent) => {
  if (!draggingPanel) return
  const dx = e.clientX - panelDragStart.x
  const dy = e.clientY - panelDragStart.y
  const pos = panelPositions[draggingPanel]
  pos.x = panelStartPos.x + dx
  pos.y = panelStartPos.y + dy
}

const onPanelPointerUp = async () => {
  draggingPanel = null
  window.removeEventListener('pointermove', onPanelPointerMove)
  window.removeEventListener('pointerup', onPanelPointerUp)
  await saveLayoutToServer()
}

const isInteractiveTarget = (el: HTMLElement | null): boolean => {
  if (!el) return false
  const interactiveSelectors =
      'input, textarea, select, button, a, [role="button"],' +
      '.el-input, .el-select, .el-button, .el-checkbox, .el-radio,' +
      '.el-switch, .el-slider, .el-table, .el-scrollbar'
  return !!el.closest(interactiveSelectors)
}

const onPanelPointerDownWrapper = (e: PointerEvent, key: PanelKey) => {
  const target = e.target as HTMLElement | null
  if (isInteractiveTarget(target)) return
  onPanelPointerDown(e, key)
}

/* ========= 计算卡片宽度 ========= */

const getCardWidth = () => {
  const w = window.innerWidth * CARD_WIDTH_RATIO
  return Math.min(CARD_WIDTH_MAX, Math.max(CARD_WIDTH_MIN, w))
}

/* ========= 核心数据 ========= */

const deviceTemplates = ref<DeviceTemplate[]>([])
const nodes = ref<DeviceNode[]>([])
const edges = ref<DeviceEdge[]>([])
const specifications = ref<Specification[]>([])
const specTemplates = ref<SpecTemplate[]>(defaultSpecTemplates)

const inputActive = ref<string[]>([])
const statusActive = ref<string[]>([])

/* ========= 节点图标 / 标签样式 ========= */

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

/* ========= 节点布局：避免重叠 & 远离左面板 ========= */

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

  // 转换到画布内部坐标（极其关键）
  const x = (screenX - canvasPan.value.x) / canvasZoom.value
  const y = (screenY - canvasPan.value.y) / canvasZoom.value

  return { x, y }
}

/* ========= 与后端交互的一些小封装 ========= */

const saveLayoutToServer = async () => {
  const payload = {
    input: { x: panelPositions.input.x, y: panelPositions.input.y },
    status: { x: panelPositions.status.x, y: panelPositions.status.y },
    canvasPan: { x: canvasPan.value.x, y: canvasPan.value.y },
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
  try {
    await boardApi.saveNodes(nodes.value)
  } catch (e) {
    console.error(e)
    ElMessage.error(t('app.saveNodesFailed') || '保存设备节点失败')
  }
}

const saveEdgesToServer = async () => {
  try {
    await boardApi.saveEdges(edges.value)
  } catch (e) {
    console.error(e)
    ElMessage.error(t('app.saveEdgesFailed') || '保存规则连线失败')
  }
}

const saveSpecsToServer = async () => {
  try {
    await boardApi.saveSpecs(specifications.value)
  } catch (e) {
    console.error(e)
    ElMessage.error(t('app.saveSpecsFailed') || '保存规约失败')
  }
}

/* ========= 设备创建 / 拖拽 ========= */

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

const onCanvasDrop = async (e: DragEvent) => {
  if (!draggingTplName.value) return
  const tpl = deviceTemplates.value.find(d => d.name === draggingTplName.value)
  if (!tpl) return

  const rect = (e.currentTarget as HTMLElement).getBoundingClientRect()
  const Sx = e.clientX - rect.left
  const Sy = e.clientY - rect.top

  // 正确公式：I = (S - P) / Z
  const x = (Sx - canvasPan.value.x) / canvasZoom.value
  const y = (Sy - canvasPan.value.y) / canvasZoom.value

  await createDeviceInstanceAt(tpl, { x, y })
  draggingTplName.value = null
}


/* ========= IFTTT 规则（来自 InputPanel） ========= */

import { getLinkPoints, updateRulesForNodeRename } from '../utils/rule'

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

/* ========= 规约（来自 InputPanel） ========= */

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
    ElMessage.warning(
        t('app.specRowIncomplete') || '存在未填完整的条件，请删除该行或补全所有字段'
    )
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
    const exists = specifications.value.some(spec => isSameSpecification(spec, item))
    if (exists) {
      ElMessage.warning(t('app.specDuplicate') || '已经存在一条内容完全相同的规约')
      return
    }
    specifications.value.push(item)
    await saveSpecsToServer()
    return
  }

  if (mode === 'ifThen') {
    if (!ifConds.length) {
      ElMessage.warning(t('app.specNeedIf') || '请先完成 IF 部分（事件 A 的条件）')
      return
    }
    if (!thenConds.length) {
      ElMessage.warning(t('app.specNeedThen') || '请先完成 THEN 部分（事件 B 的条件）')
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
    const exists = specifications.value.some(spec => isSameSpecification(spec, item))
    if (exists) {
      ElMessage.warning(t('app.specDuplicate') || '已经存在一条内容完全相同的规约')
      return
    }
    specifications.value.push(item)
    await saveSpecsToServer()
    return
  }

  ElMessage.error('Unknown specification template id: ' + tplId)
}

const deleteSpecification = async (id: string) => {
  specifications.value = specifications.value.filter(s => s.id !== id)
  await saveSpecsToServer()
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

  node.label = newLabel
  await saveNodesToServer()

  const rulesChanged = updateRulesForNodeRename(edges.value, node.id, newLabel)
  if (rulesChanged) {
    await saveEdgesToServer()
  }

  const specChanged = updateSpecsForNodeRename(
      specifications.value,
      node.id,
      newLabel
  )
  if (specChanged) {
    await saveSpecsToServer()
  }

  dialogMeta.label = newLabel
  dialogMeta.specs = specifications.value.filter(spec => isSpecRelatedToNode(spec, node.id))
  dialogVisible.value = false
}

/* ========= 删除节点 ========= */

const forceDeleteNode = async (nodeId: string) => {
  nodes.value = nodes.value.filter(n => n.id !== nodeId)
  edges.value = edges.value.filter(e => e.from !== nodeId && e.to !== nodeId)

  const { nextSpecs, removed } = removeSpecsForNode(specifications.value, nodeId)
  specifications.value = nextSpecs

  await saveNodesToServer()
  await saveEdgesToServer()
  await saveSpecsToServer()

  if (removed.length > 0) {
    ElMessage.info(
        t('app.specsDeletedWithNode') || '已同时删除与该设备相关的规约'
    )
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

const handleDialogDelete = () => {
  if (!dialogMeta.nodeId) return
  deleteCurrentNodeWithConfirm(dialogMeta.nodeId)
}

/* ========= StatusPanel 删除回调 ========= */

const deleteNodeFromStatus = (nodeId: string) => {
  deleteCurrentNodeWithConfirm(nodeId)
}

const deleteEdgeFromStatus = async (edgeId: string) => {
  edges.value = edges.value.filter(e => e.id !== edgeId)
  await saveEdgesToServer()
}

/* ========= CanvasBoard 回调：节点移动 / 缩放完成 ========= */

const handleNodeMovedOrResized = async () => {
  await saveNodesToServer()
  await saveEdgesToServer()
}

/* ========= 初始化 ========= */

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

  try {
    const res = await boardApi.getNodes()
    nodes.value = res.data
  } catch {
    nodes.value = []
  }

  try {
    const res = await boardApi.getEdges()
    edges.value = res.data
  } catch {
    edges.value = []
  }

  try {
    const res = await boardApi.getSpecs()
    specifications.value = res.data
  } catch {
    specifications.value = []
  }

  try {
    const res = await boardApi.getLayout()
    const layout = res.data
    if (layout?.input && layout?.status) {
      panelPositions.input.x = layout.input.x
      panelPositions.input.y = layout.input.y
      panelPositions.status.x = layout.status.x
      panelPositions.status.y = layout.status.y
    } else {
      // 没有数据时使用默认布局
      panelPositions.input.x = DEFAULT_PANEL_PADDING
      panelPositions.input.y = DEFAULT_PANEL_PADDING

      const cardWidth = getCardWidth()
      panelPositions.status.x =
          window.innerWidth - cardWidth - DEFAULT_PANEL_PADDING
      panelPositions.status.y = DEFAULT_PANEL_PADDING
    }
    if (layout?.canvasPan) {
      canvasPan.value = layout.canvasPan
    }
    if (typeof layout?.canvasZoom === 'number') {
      canvasZoom.value = Math.min(MAX_ZOOM, Math.max(MIN_ZOOM, layout.canvasZoom))
    }
  } catch {
    // 布局加载失败：使用默认值
    panelPositions.input.x = DEFAULT_PANEL_PADDING
    panelPositions.input.y = DEFAULT_PANEL_PADDING
    const cardWidth = getCardWidth()
    panelPositions.status.x =
        window.innerWidth - cardWidth - DEFAULT_PANEL_PADDING
    panelPositions.status.y = DEFAULT_PANEL_PADDING
  }

  try {
    const res = await boardApi.getActive()
    if (Array.isArray(res.data?.input)) {
      inputActive.value = res.data.input
    }
    if (Array.isArray(res.data?.status)) {
      statusActive.value = res.data.status
    }
  } catch {
    // 折叠状态失败就用默认
  }

  window.addEventListener('keydown', onGlobalKeydown)
})

watch(
    () => ({ input: inputActive.value, status: statusActive.value }),
    async val => {
      try {
        await boardApi.saveActive(val)
      } catch (e) {
        console.error(e)
        ElMessage.error(t('app.saveActiveFailed') || '保存折叠面板状态失败')
      }
    },
    { deep: true }
)

watch(canvasZoom, () => {
  void saveLayoutToServer()
})

onBeforeUnmount(() => {
  window.removeEventListener('keydown', onGlobalKeydown)
  window.removeEventListener('pointermove', onCanvasPointerMove)
  window.removeEventListener('pointerup', onCanvasPointerUp)
})
</script>

<template>
  <div class="iot-board">
    <!-- 画布：节点 + 连线 -->
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

    <!-- 左侧输入卡片 -->
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

    <!-- 右侧状态卡片 -->
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

    <!-- 右键弹出的设备详情对话框 -->
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

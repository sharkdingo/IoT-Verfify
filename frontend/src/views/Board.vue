<script setup lang="ts">
/* =================================================================================
 * 1. Imports & Setup
 * ================================================================================= */
import {ref, reactive, computed, onMounted, onBeforeUnmount, watch} from 'vue'
import { useI18n } from 'vue-i18n'
import { ElMessage, ElMessageBox } from 'element-plus'
// Icons
import { Edit, Platform, Close } from '@element-plus/icons-vue'

// Types
import type {DeviceDialogMeta, DeviceTemplate} from '../types/device'
import type { CanvasPan } from '../types/canvas'
import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { RuleForm } from '../types/rule'
import type { SpecCondition, Specification, SpecTemplate, SpecTemplateId } from '../types/spec'
// Panel types removed

// Utils
import {getDeviceIconPath, getNodeIcon} from '../utils/device'
import { getUniqueLabel } from '../utils/canvas/nodeCreate'
import {
  getSpecMode,
  validateAndCleanConditions,
  isSameSpecification,
  isSpecRelatedToNode,
  removeSpecsForNode,
  updateSpecsForNodeRename
} from '../utils/spec'
import { getLinkPoints } from '../utils/rule'

// Config
import { defaultSpecTemplates } from '../assets/config/specTemplates'

// API
import boardApi from '@/api/board'

// Components
import DeviceDialog from '../components/DeviceDialog.vue'
import CanvasBoard from '../components/CanvasBoard.vue'
import ControlCenter from '../components/ControlCenter.vue'
import SystemInspector from '../components/SystemInspector.vue'
import RuleBuilderDialog from '../components/RuleBuilderDialog.vue'

// Styles
import '../styles/board.css'

const { t } = useI18n()

/* =================================================================================
 * 2. Constants & Configuration
 * ================================================================================= */

// Panel constants removed

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

// Panel system removed

// Panel system removed

// --- Core Data State ---
const deviceTemplates = ref<DeviceTemplate[]>([])
const nodes = ref<DeviceNode[]>([])
const edges = ref<DeviceEdge[]>([])
const rules = ref<RuleForm[]>([])  // 独立存储规则列表
const specifications = ref<Specification[]>([])
const specTemplates = ref<SpecTemplate[]>(defaultSpecTemplates)


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

// getCardWidth removed


const getNodeLabelStyle = (node: DeviceNode) => {
  const ratio = node.width / BASE_NODE_WIDTH
  const scale = Math.min(Math.max(ratio, 0.75), 1.5)
  const fontSize = BASE_FONT_SIZE * scale
  return {
    fontSize: fontSize + 'px',
    maxWidth: node.width - 16 + 'px'
  }
}

// Panel system removed

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
  await saveNodesToServer()
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

  await createDeviceInstanceAt(tpl, { x, y })
  draggingTplName.value = null
}

const handleNodeMovedOrResized = async () => {
  await saveNodesToServer()
  await saveEdgesToServer()
}

const handleAddRule = async (payload: RuleForm) => {
  const { sources, toId, toApi } = payload
  if (!sources || !sources.length || !toId || !toApi) {
    ElMessage.warning(t('app.fillAllRuleFields') || '请完整选择源/目标设备及 API')
    return
  }

  const toNode = nodes.value.find(n => n.id === toId)
  if (!toNode) return

  // 为新规则生成 ID
  const ruleId = 'rule_' + Date.now()
  const newRule: RuleForm = {
    ...payload,
    id: ruleId
  }

  // 计算新规则对应的 Edge
  const newEdges: DeviceEdge[] = []
  for (const s of sources) {
    const fid = s.fromId
    const fromApi = s.fromApi
    if (!fid || !fromApi) continue
    const fromNode = nodes.value.find(n => n.id === fid)
    if (!fromNode) continue
    const { fromPoint, toPoint } = getLinkPoints(fromNode, toNode)
    newEdges.push({
      id: 'edge_' + Date.now() + '_' + fid,
      from: fromNode.id,
      to: toNode.id,
      fromLabel: fromNode.label,
      toLabel: toNode.label,
      fromApi,
      toApi,
      fromPos: fromPoint,
      toPos: toPoint
    })
  }

  if (newEdges.length) {
    try {
      // 更新前端状态
      rules.value = [...rules.value, newRule]
      edges.value = [...edges.value, ...newEdges]

      // 并行保存规则和边
      await Promise.all([
        boardApi.saveRules(rules.value),
        boardApi.saveEdges(edges.value)
      ])

      ElMessage.success(t('app.addRuleSuccess') || '添加规则成功')
    } catch (e) {
      console.error('saveRules/saveEdges error', e)
      // 保存失败，回滚状态
      rules.value = rules.value.filter(r => r.id !== ruleId)
      edges.value = edges.value.filter(e => !newEdges.some(ne => ne.id === e.id))
      ElMessage.error(t('app.saveRulesFailed') || '保存规则失败')
    }
  }
}


/* =================================================================================
 * 8. Context Menu & Deletion
 * ================================================================================= */

const onDeviceListClick = (deviceId: string) => {
  const node = nodes.value.find(n => n.id === deviceId)
  if (!node) return

  const tpl = deviceTemplates.value.find(t => t.manifest.Name === node.templateName)
  dialogMeta.nodeId = node.id
  dialogMeta.label = node.label
  dialogMeta.deviceName = tpl ? tpl.manifest.Name : node.templateName
  dialogMeta.description = tpl ? tpl.manifest.Description : ''
  dialogMeta.manifest = tpl ? tpl.manifest : null
  dialogMeta.rules = edges.value.filter(e => e.from === node.id || e.to === node.id)
  dialogMeta.specs = specifications.value.filter(spec => isSpecRelatedToNode(spec, node.id))
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
  contextMenu.value = {
    visible: true,
    x: event.clientX,
    y: event.clientY,
    node: node
  }
}

const closeContextMenu = () => {
  contextMenu.value.visible = false
}

// 右键菜单操作
const renameDevice = () => {
  if (!contextMenu.value.node) return
  // 打开重命名对话框或直接编辑
  const node = contextMenu.value.node
  const newLabel = prompt('请输入新的设备名称:', node.label)
  if (newLabel && newLabel !== node.label) {
    handleRenameDevice(node.id, newLabel)
  }
  closeContextMenu()
}

const deleteDevice = () => {
  if (!contextMenu.value.node) return
  deleteCurrentNodeWithConfirm(contextMenu.value.node.id)
  closeContextMenu()
}

const handleRenameDevice = async (nodeId: string, newLabel: string) => {
  const exists = nodes.value.some(n => n.label === newLabel && n.id !== nodeId)
  if (exists) {
    ElMessage.error(t('app.nameExists') || '该名称已存在，请换一个')
    return
  }

  const node = nodes.value.find(n => n.id === nodeId)
  if (node) {
    node.label = newLabel
    await saveNodesToServer()
    ElMessage.success(t('app.renameSuccess') || '重命名成功')
  }
}

const viewDeviceDetails = () => {
  if (!contextMenu.value.node) return
  // 显示设备详情 - 复用左侧列表点击的逻辑
  onDeviceListClick(contextMenu.value.node.id)
  closeContextMenu()
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

/**
 * 删除规则及其相关的边
 */
const deleteRule = async (ruleId: string) => {
  const ruleToDelete = rules.value.find(r => r.id === ruleId)
  if (!ruleToDelete) return

  // 删除规则
  rules.value = rules.value.filter(r => r.id !== ruleId)

  // 删除相关的边（所有 toId 和 toApi 匹配的边）
  edges.value = edges.value.filter(e => {
    // 如果边的 toId 和 toApi 与被删除的规则匹配，则删除
    if (e.to === ruleToDelete.toId && e.toApi === ruleToDelete.toApi) {
      // 检查 source 是否在这个规则中
      return !ruleToDelete.sources.some(s => s.fromId === e.from && s.fromApi === e.fromApi)
    }
    return true
  })

  // 并行保存
  try {
    await Promise.all([
      boardApi.saveRules(rules.value),
      boardApi.saveEdges(edges.value)
    ])
    ElMessage.success(t('app.deleteRuleSuccess') || '删除规则成功')
  } catch (e) {
    console.error('删除规则失败', e)
    // 保存失败，回滚（重新获取）
    await refreshRules()
    ElMessage.error(t('app.deleteRuleFailed') || '删除规则失败')
  }
}

const deleteSpecification = async (specId: string) => {
  const specToDelete = specifications.value.find(s => s.id === specId)
  if (!specToDelete) return

  // 删除规约
  specifications.value = specifications.value.filter(s => s.id !== specId)

  try {
    await saveSpecsToServer()
    ElMessage.success('删除规约成功')
  } catch (e) {
    console.error('删除规约失败', e)
    // 保存失败，回滚（重新获取）
    await refreshSpecifications()
    ElMessage.error('删除规约失败')
  }
}

/* =================================================================================
 * 9. API Interactions (Save)
 * ================================================================================= */

// Panel layout saving removed

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

const ruleBuilderVisible = ref(false)

// Default device templates for demonstration
const defaultDeviceTemplates = ref<DeviceTemplate[]>([
  {
    id: 'sensor-1',
    name: 'Sensor',
    manifest: {
      Name: 'Sensor',
      Description: 'Basic sensor device',
      Modes: ['Working', 'Off'],
      InternalVariables: [],
      ImpactedVariables: ['temperature', 'humidity', 'motion'],
      InitState: 'Working',
      WorkingStates: [
        {
          Name: 'Working',
          Dynamics: [],
          Description: 'Sensor is actively monitoring environmental conditions',
          Trust: 'trusted',
          Privacy: 'private',
          Invariant: 'temperature >= -50 && temperature <= 100'
        }
      ],
      APIs: []
    }
  },
  {
    id: 'switch-1',
    name: 'Switch',
    manifest: {
      Name: 'Switch',
      Description: 'Basic switch device',
      Modes: ['On', 'Off'],
      InternalVariables: [],
      ImpactedVariables: ['power'],
      InitState: 'Off',
      WorkingStates: [
        {
          Name: 'On',
          Dynamics: [],
          Description: 'Switch is turned on and power is flowing',
          Trust: 'trusted',
          Privacy: 'public',
          Invariant: 'power == true'
        },
        {
          Name: 'Off',
          Dynamics: [],
          Description: 'Switch is turned off and no power is flowing',
          Trust: 'trusted',
          Privacy: 'public',
          Invariant: 'power == false'
        }
      ],
      APIs: []
    }
  },
  {
    id: 'light-1',
    name: 'Light',
    manifest: {
      Name: 'Light',
      Description: 'Basic light device',
      Modes: ['On', 'Off'],
      InternalVariables: [],
      ImpactedVariables: ['brightness', 'color'],
      InitState: 'Off',
      WorkingStates: [
        {
          Name: 'On',
          Dynamics: [],
          Description: 'Light is turned on and emitting light',
          Trust: 'trusted',
          Privacy: 'public',
          Invariant: 'brightness > 0'
        },
        {
          Name: 'Off',
          Dynamics: [],
          Description: 'Light is turned off and not emitting light',
          Trust: 'trusted',
          Privacy: 'public',
          Invariant: 'brightness == 0'
        }
      ],
      APIs: []
    }
  }
])
const refreshDeviceTemplates = async () => {
  try {
    const res = await boardApi.getDeviceTemplates()
    deviceTemplates.value = res || []
    // If no templates from backend, use defaults
    if (deviceTemplates.value.length === 0) {
      deviceTemplates.value = defaultDeviceTemplates.value
      console.log('Using default device templates:', deviceTemplates.value)
    }
  } catch (e) {
    console.error(e)
    // Fallback to default templates on error
    deviceTemplates.value = defaultDeviceTemplates.value
    console.log('Using default device templates due to API error:', deviceTemplates.value)
    // ElMessage.error(t('app.loadTemplatesFailed') || '加载设备模板失败')
  }
}



/* =================================================================================
 * 10. Lifecycle & Watchers
 * ================================================================================= */

// 1. 定义刷新设备的函数
const refreshDevices = async () => {
  console.log('🔄 Board组件收到指令，正在刷新设备列表...')
  try { nodes.value = await boardApi.getNodes() } catch(e) {
    console.error('加载设备失败', e)
    nodes.value = [] }
}

// 2.定义刷新规则的函数
const refreshRules = async () => {
  try {
    // 并行获取规则列表和边列表
    const [rulesData, edgesData] = await Promise.all([
      boardApi.getRules(),
      boardApi.getEdges()
    ])
    rules.value = rulesData
    edges.value = edgesData
  } catch (e) {
    console.error('加载规则失败', e)
    rules.value = []
    edges.value = []
  }
}

// 3.定义刷新规约的函数
const refreshSpecifications = async () => {
  console.log('🔄 Board组件收到指令，正在刷新规约列表...')
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

  // Load Layout (only canvas)
  try {
    const layout = await boardApi.getLayout()

    // Canvas
    if (layout?.canvasPan) canvasPan.value = layout.canvasPan
    if (typeof layout?.canvasZoom === 'number') {
      canvasZoom.value = Math.min(MAX_ZOOM, Math.max(MIN_ZOOM, layout.canvasZoom))
    }
  } catch {
    // Layout loading failed
  }

  // Panel system removed

  window.addEventListener('keydown', onGlobalKeydown)
})

// Panel watch removed

// Canvas zoom saving removed

// Color utilities (matching CanvasBoard colors)
const getCanvasMapColorIndex = (nodeId: string): number => {
  // Same hash function as CanvasBoard.vue for consistency - using djb2 algorithm
  let hash = 5381
  for (let i = 0; i < nodeId.length; i++) {
    const char = nodeId.charCodeAt(i)
    hash = ((hash << 5) + hash) + char // hash * 33 + char
  }

  // Convert to positive number and get modulo 4
  const colorIndex = Math.abs(hash) % 4

  return colorIndex
}

const getCanvasMapColor = (nodeId: string): string => {
  // Return actual color values instead of Tailwind classes
  const colorIndex = getCanvasMapColorIndex(nodeId)
  const colorValues = ['#6366f1', '#059669', '#C026D3', '#dc2626'] // primary, online, secondary(purple), offline
  return colorValues[colorIndex] || colorValues[0]
}

// Convert Tailwind bg- class to actual color value for SVG
const getCanvasMapColorValue = (nodeId: string): string => {
  const colorIndex = getCanvasMapColorIndex(nodeId)
  // Map to actual color values that match the Tailwind colors
  const colorValues = ['#2563EB', '#059669', '#C026D3', '#dc2626']
  return colorValues[colorIndex] || colorValues[0]
}

const getCanvasMapSize = (nodeId: string): string => {
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

  // Map dimensions (the mini map container)
  const mapWidth = 256 // width of the mini map container (w-full in h-32 div)
  const mapHeight = 128 // height of the mini map container (h-32)

  // Convert node positions to mini map coordinates
  const dots = nodes.value.map((node) => {
    const nodeX = canvasWidth > 0 ? ((node.position.x - minX) / canvasWidth) * mapWidth : mapWidth / 2
    const nodeY = canvasHeight > 0 ? ((node.position.y - minY) / canvasHeight) * mapHeight : mapHeight / 2

    return {
      id: node.id,
      x: Math.max(0, Math.min(mapWidth - 8, nodeX)), // Keep within bounds
      y: Math.max(0, Math.min(mapHeight - 8, nodeY)),
      size: getCanvasMapSize(node.id),
      color: getCanvasMapColor(node.id)
    }
  })

  // Create node lookup map for easy access
  const nodeMap = new Map(dots.map(dot => [dot.id, dot]))

  // Generate lines for edges
  const lines = edges.value.map((edge) => {
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
      color: getCanvasMapColor(edge.from), // Use source device color
      isBidirectional
    }
  }).filter(Boolean)

  return { dots, lines }
})

const canvasMapDots = computed(() => canvasMapData.value.dots)
const canvasMapLines = computed(() => canvasMapData.value.lines.filter(line => line !== null && line !== undefined))

const handleCreateDevice = async (data: { template: DeviceTemplate, customName: string }) => {
  const { template, customName } = data

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
  await saveNodesToServer()
}

const openRuleBuilder = () => {
  ruleBuilderVisible.value = true
}

const handleAddSpec = async (data: { templateId: string, devices: Array<{deviceId: string, deviceLabel: string, selectedApis: string[]}>, formula: string }) => {
  const { templateId, devices, formula } = data

  // Create specification with LTL formula
  const specId = 'spec_' + Date.now()
  const templateLabel = templateId === 'safety' ? 'Safety Property' :
                       templateId === 'liveness' ? 'Liveness Property' :
                       'Fairness Property'

  const newSpec: Specification = {
    id: specId,
    templateId: '1' as any, // Use first template as fallback since we don't have LTL templates
    templateLabel,
    aConditions: [],
    ifConditions: [],
    thenConditions: [],
    formula: formula,
    devices: devices
  }

  specifications.value.push(newSpec)
  await saveSpecsToServer()
}

const getNextNodePosition = (): { x: number; y: number } => {
  const count = nodes.value.length
  const col = count % NODE_GRID_COLS
  const row = Math.floor(count / NODE_GRID_COLS)

  // 使用固定起始位置
  const screenX = 200 + col * NODE_SPACING_X
  const screenY = NODE_START_Y + row * NODE_SPACING_Y

  const x = (screenX - canvasPan.value.x) / canvasZoom.value
  const y = (screenY - canvasPan.value.y) / canvasZoom.value

  return { x, y }
}

onBeforeUnmount(() => {
  window.removeEventListener('keydown', onGlobalKeydown)
  window.removeEventListener('pointermove', onCanvasPointerMove)
  window.removeEventListener('pointerup', onCanvasPointerUp)
})

defineExpose({
  refreshDevices,
  refreshRules,
  refreshSpecifications,
})
</script>

<template>
  <!-- [Fix] @wheel.ctrl.prevent 阻止浏览器原生缩放 -->
  <div class="iot-board" @wheel.ctrl.prevent="onBoardWheel">
    <!-- Left Sidebar - Control Center -->
    <ControlCenter
      :device-templates="deviceTemplates"
      :nodes="nodes"
      :edges="edges"
      :canvas-pan="canvasPan"
      :canvas-zoom="canvasZoom"
      @create-device="handleCreateDevice"
      @open-rule-builder="openRuleBuilder"
      @add-spec="handleAddSpec"
    />

    <!-- Right Sidebar - System Inspector -->
    <SystemInspector
      :devices="nodes"
      :rules="rules"
      :specifications="specifications"
      @delete-device="deleteNodeFromStatus"
      @delete-rule="deleteRule"
      @delete-spec="deleteSpecification"
      @device-click="onDeviceListClick"
    />

    <!-- Canvas Area -->
    <div class="canvas-container">
      <!-- Background elements -->
      <div class="absolute inset-0 grid-bg opacity-100 pointer-events-none z-0"></div>
      <div class="absolute inset-0 bg-gradient-to-b from-white/40 via-transparent to-blue-50/20 pointer-events-none z-0"></div>


      <!-- Canvas Board -->
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
      class="fixed z-50 bg-white border border-slate-200 rounded-lg shadow-lg py-2 min-w-48"
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
        重命名
      </button>
      <button
        @click="viewDeviceDetails"
        class="w-full px-3 py-2 text-left text-sm text-slate-700 hover:bg-slate-50 flex items-center gap-2"
      >
        <span class="material-icons-round text-base">visibility</span>
        查看详细
      </button>
      <div class="border-t border-slate-100 my-1"></div>
      <button
        @click="deleteDevice"
        class="w-full px-3 py-2 text-left text-sm text-red-600 hover:bg-red-50 flex items-center gap-2"
      >
        <span class="material-icons-round text-base">delete</span>
        删除设备
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
        @save-rule="handleAddRule"
    />

    <!-- Canvas Map - Fixed at bottom left -->
    <div class="fixed bottom-4 left-4 w-64 p-4 bg-white border border-slate-200 rounded-lg shadow-lg z-50">
      <div class="flex items-center justify-between mb-2">
        <span class="text-[10px] uppercase font-bold text-slate-400">Canvas Map</span>
        <span class="text-[10px] text-primary font-bold">{{ Math.round(canvasZoom * 100) }}%</span>
      </div>

      <div class="w-full h-32 rounded bg-slate-50 border border-slate-200 relative overflow-hidden shadow-inner">
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
            :stroke="getCanvasMapColorValue(line.fromId)"
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
          No devices on canvas
        </div>
      </div>
    </div>
  </div>
</template>
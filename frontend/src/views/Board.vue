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
import { cacheManifestForNode, getCachedManifestForNode, hydrateManifestCacheForNodes } from '@/utils/templateCache'

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
    id: ruleId,
    name: payload.name || `Rule ${ruleId}`
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
      fromPos: fromPoint,
      toPos: toPoint
    })
  }

  if (newEdges.length) {
    try {
      // 先保存新创建的规则（只保存新规则，不是所有规则）
      await boardApi.saveRules([newRule])
      
      // 保存新创建的边
      await boardApi.saveEdges(newEdges)

      // 更新前端状态
      rules.value = [...rules.value, newRule]
      edges.value = [...edges.value, ...newEdges]

      ElMessage.success(t('app.addRuleSuccess') || '添加规则成功')
    } catch (e: any) {
      console.error('saveRules/saveEdges error', e)
      // 如果后端返回了错误信息，显示它
      const errorMsg = e?.response?.data?.message || e?.message || '保存规则失败'
      ElMessage.error(errorMsg)
    }
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
  // 先更新本地状态，确保UI立即响应
  nodes.value = nodes.value.filter(n => n.id !== nodeId)
  edges.value = edges.value.filter(e => e.from !== nodeId && e.to !== nodeId)

  // 删除与该设备相关的规则
  const rulesToDelete = rules.value.filter(rule =>
    rule.toId === nodeId || rule.sources.some(source => source.fromId === nodeId)
  )
  const ruleIdsToDelete = rulesToDelete.map(rule => rule.id)
  rules.value = rules.value.filter(rule => !ruleIdsToDelete.includes(rule.id))

  const { nextSpecs, removed } = removeSpecsForNode(specifications.value, nodeId)
  specifications.value = nextSpecs

  // 尝试保存到服务器，但不让保存失败影响UI更新
  try {
    await Promise.all([
      saveNodesToServer(),
      saveEdgesToServer(),
      boardApi.saveRules(rules.value),
      saveSpecsToServer()
    ])

    if (ruleIdsToDelete.length > 0) {
      ElMessage.info(`已同时删除 ${ruleIdsToDelete.length} 个与该设备相关的规则`)
    }

    if (removed.length > 0) {
      ElMessage.info('已同时删除与该设备相关的规约')
    }
  } catch (error) {
    console.error('保存删除操作失败:', error)
    // 即使保存失败，UI状态已经更新，用户可以看到设备已被删除
    ElMessage.warning('设备已从界面删除，但保存到服务器时出现问题')
  }
}

const deleteCurrentNodeWithConfirm = (nodeId: string) => {
  const node = nodes.value.find(n => n.id === nodeId)
  if (!node) return

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

  // 显示自定义确认对话框
  deleteConfirmDialogData.node = node
  deleteConfirmDialogData.hasRelations = true
  deleteConfirmDialogData.relationCount = {
    rules: edges.value.filter(e => e.from === nodeId || e.to === nodeId).length,
    specs: specifications.value.filter(spec => isSpecRelatedToNode(spec, nodeId)).length
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
    ElMessage.error('删除设备失败，请重试')
  }
}

const cancelDelete = () => {
  deleteConfirmDialogVisible.value = false
  deleteConfirmDialogData.node = null
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

  // 删除相关的边（所有 to 匹配的边）
  edges.value = edges.value.filter(e => {
    // 如果边的 to 与被删除的规则的 toId 匹配，则需要进一步检查
    if (e.to === ruleToDelete.toId) {
      // 检查 source 是否在这个规则中（通过 from 字段匹配）
      return !ruleToDelete.sources.some(s => s.fromId === e.from)
    }
    return true
  })

  // 并行保存
  try {
    await Promise.all([
      boardApi.saveRules(rules.value),
      boardApi.saveEdges(edges.value)
    ])
    ElMessage.success( '删除规则成功')
  } catch (e) {
    console.error('删除规则失败', e)
    // 保存失败，回滚（重新获取）
    await refreshRules()
    ElMessage.error('删除规则失败')
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

// Default device templates - now loaded from backend
const defaultDeviceTemplates = ref<DeviceTemplate[]>([])

const refreshDeviceTemplates = async () => {
  try {
    // 先重新加载模板（从后端资源文件）
    await boardApi.reloadDeviceTemplates()
    // 然后获取模板列表
    const res = await boardApi.getDeviceTemplates()
    deviceTemplates.value = res || []
    console.log('Loaded device templates from backend:', deviceTemplates.value)
  } catch (e) {
    console.error('加载设备模板失败:', e)
    deviceTemplates.value = []
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
    console.log('🔍 [Board] 刷新规则 - 原始数据:', JSON.parse(JSON.stringify(rulesData)))
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
  hydrateManifestCacheForNodes(nodes.value, deviceTemplates.value as any, resolveTemplateForHydration as any)

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
    '#6366f1', '#059669', '#C026D3', '#dc2626',
    '#ef4444', '#14b8a6', '#ec4899', '#eab308'
  ] // primary, online, secondary(purple), offline, red, teal, pink, yellow
  return colorValues[colorIndex] || colorValues[0]
}

// Convert Tailwind bg- class to actual color value for SVG
const getCanvasMapColorValue = (nodeId: string): string => {
  const colorIndex = getCanvasMapColorIndex(nodeId)
  // Map to actual color values that match the Tailwind colors
  const colorValues = [
    '#2563EB', '#059669', '#C026D3', '#dc2626',
    '#ef4444', '#14b8a6', '#ec4899', '#eab308'
  ]
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

const handleAddSpec = async (data: { 
  templateId: string, 
  templateType: string,
  devices: Array<{deviceId: string, deviceLabel: string, selectedApis: string[]}>, 
  formula: string,
  aConditions: SpecCondition[],
  ifConditions: SpecCondition[],
  thenConditions: SpecCondition[]
}) => {
  const { templateId, templateType, devices, formula, aConditions, ifConditions, thenConditions } = data

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

  console.log('[Board] Creating new spec:', newSpec)
  specifications.value.push(newSpec)
  await saveSpecsToServer()
}

const handleDeleteTemplate = async (templateId: string) => {
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
  window.removeEventListener('keydown', onGlobalKeydown)
  window.removeEventListener('pointermove', onCanvasPointerMove)
  window.removeEventListener('pointerup', onCanvasPointerUp)
})

defineExpose({
  refreshDevices,
  refreshRules,
  refreshSpecifications,
})

// ==== Verification Logic ====
const isVerifying = ref(false)
const verificationResult = ref<any>(null)
const verificationError = ref<string | null>(null)

const handleVerify = async () => {
  if (nodes.value.length === 0) {
    ElMessage.warning('No devices to verify')
    return
  }

  isVerifying.value = true
  verificationError.value = null
  verificationResult.value = null

  try {
    // Prepare devices: Add default variables/privacies if missing
    const devices = nodes.value.map(node => {
      // Get template
      const tpl = deviceTemplates.value.find(t => t.manifest?.Name === node.templateName)
      const manifest = tpl?.manifest

      // Determine variables
      let variables = (node as any).variables || []
      if ((!variables || variables.length === 0) && manifest?.InternalVariables) {
        variables = manifest.InternalVariables.map((v: any) => ({
          name: v.Name,
          value: v.Default || '0', // Or some default
          trust: 'trusted'
        }))
      }

      // Determine privacies
      let privacies = (node as any).privacies || []
      if ((!privacies || privacies.length === 0) && manifest?.InternalVariables) {
        privacies = manifest.InternalVariables.map((v: any) => ({
          name: v.Name,
          privacy: v.Privacy || 'public'
        }))
      }

      // Map to backend DTO format - varName is required
      return {
        varName: node.label,  // Backend expects varName
        templateName: node.templateName,
        state: node.state,
        currentStateTrust: (node as any).currentStateTrust || 'trusted',
        variables,
        privacies
      }
    })

    // Prepare rules - transform to backend DTO format
    const rulesData = rules.value.map(r => ({
      // Backend expects: conditions (not sources)
      conditions: (r.sources || []).map(s => ({
        deviceName: s.fromId,
        attribute: s.fromApi || s.property || '',
        relation: s.relation || '=',
        value: s.value || 'true'
      })),
      // Backend expects: command with deviceName and action
      command: {
        deviceName: r.toId || '',
        action: r.toApi || '',
        contentDevice: null,
        content: null
      },
      ruleString: r.name || ''
    }))

    // Prepare specs
    const specs = specifications.value

    const req = {
      devices,
      rules: rulesData,
      specs,
      isAttack: false,
      intensity: 3
    }

    console.log('Starting verification with payload:', req)

    const result = await boardApi.verify(req)
    verificationResult.value = result

    if (result.safe) {
      ElMessage.success('Verification passed: System is safe!')
    } else {
      ElMessage.warning(`Verification failed: Found ${result.traces?.length || 0} violations`)
    }

  } catch (error: any) {
    console.error('Verification failed:', error)
    verificationError.value = error.message || 'Verification failed'
    ElMessage.error(verificationError.value)
  } finally {
    isVerifying.value = false
  }
}

// ==== Results Dialog ====
const showResultDialog = computed(() => !!verificationResult.value || !!verificationError.value)

const closeResultDialog = () => {
  verificationResult.value = null
  verificationError.value = null
}
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
      @refresh-templates="refreshDeviceTemplates"
      @delete-template="handleDeleteTemplate"
      @verify="handleVerify"
    />

    <!-- Right Sidebar - System Inspector -->
    <SystemInspector
      :devices="nodes"
      :rules="rules"
      :edges="edges"
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
        :device-templates="deviceTemplates"
        @save-rule="handleAddRule"
    />

    <!-- Canvas Map - Fixed at top right -->
    <div class="fixed bottom-4 right-4 w-64 p-4 bg-white border border-slate-200 rounded-lg shadow-lg z-40">
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

    <!-- Custom Rename Dialog -->
    <div v-if="renameDialogVisible" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="cancelRename">
      <div class="bg-white rounded-xl p-6 w-96 max-w-[90vw] shadow-2xl" @click.stop>
        <div class="mb-6">
          <h3 class="text-lg font-semibold text-slate-800 mb-4">重命名设备</h3>
          <div class="space-y-2">
            <input
              v-model="renameDialogData.newName"
              @keyup.enter="confirmRename"
              class="w-full px-3 py-2 border border-slate-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-blue-500 transition-colors"
              placeholder="输入设备名称"
            />
          </div>
        </div>
        <div class="flex justify-end space-x-3">
          <button
            @click="cancelRename"
            class="px-4 py-2 text-sm font-medium text-slate-700 bg-slate-100 border border-slate-300 rounded-lg hover:bg-slate-200 transition-colors"
          >
            取消
          </button>
          <button
            @click="confirmRename"
            :disabled="!renameDialogData.newName.trim() || renameDialogData.newName.trim() === renameDialogData.node?.label"
            class="px-4 py-2 text-sm font-medium text-white bg-blue-600 border border-transparent rounded-lg hover:bg-blue-700 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
          >
            确定
          </button>
        </div>
      </div>
    </div>

    <!-- Custom Delete Confirmation Dialog -->
    <div v-if="deleteConfirmDialogVisible" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="cancelDelete">
      <div class="bg-white rounded-xl p-6 w-96 max-w-[90vw] shadow-2xl" @click.stop>
        <div class="mb-6">
          <div class="flex items-center mb-4">
            <div class="flex-shrink-0 w-10 h-10 bg-red-100 rounded-full flex items-center justify-center">
              <span class="material-symbols-outlined text-red-600">warning</span>
            </div>
            <div class="ml-3">
              <h3 class="text-lg font-semibold text-slate-800">确认删除设备</h3>
              <p class="text-sm text-slate-600">此操作无法撤销</p>
            </div>
          </div>

        

          <div v-if="deleteConfirmDialogData.hasRelations" class="bg-yellow-50 border border-yellow-200 rounded-lg p-4 mb-4">
            <div class="flex items-start">
              <span class="material-symbols-outlined text-yellow-600 mr-2 mt-0.5">info</span>
              <div>
                <p class="text-sm font-medium text-yellow-800 mb-1">此设备有关联的规则和规约</p>
                <div class="text-xs text-yellow-700 space-y-1">
                  <div v-if="deleteConfirmDialogData.relationCount.rules > 0">
                    • {{ deleteConfirmDialogData.relationCount.rules }} 个关联规则将被删除
                  </div>
                  <div v-if="deleteConfirmDialogData.relationCount.specs > 0">
                    • {{ deleteConfirmDialogData.relationCount.specs }} 个关联规约将被删除
                  </div>
                </div>
              </div>
            </div>
          </div>

  
        </div>

        <div class="flex justify-end space-x-3">
          <button
            @click="cancelDelete"
            class="px-4 py-2 text-sm font-medium text-slate-700 bg-slate-100 border border-slate-300 rounded-lg hover:bg-slate-200 transition-colors"
          >
            取消
          </button>
          <button
            @click="confirmDelete"
            class="px-4 py-2 text-sm font-medium text-white bg-red-600 border border-transparent rounded-lg hover:bg-red-700 transition-colors"
          >
            删除设备
          </button>
        </div>
      </div>
    </div>
  </div>

  <!-- Verification Result Dialog -->
  <div v-if="showResultDialog" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="closeResultDialog">
    <div class="bg-white rounded-xl p-6 w-[600px] max-w-[90vw] shadow-2xl max-h-[80vh] flex flex-col" @click.stop>
      <div class="flex items-center justify-between mb-4">
        <h3 class="text-lg font-semibold text-slate-800">Verification Result</h3>
        <button @click="closeResultDialog" class="text-slate-400 hover:text-slate-600">
          <span class="material-symbols-outlined">close</span>
        </button>
      </div>

      <div v-if="verificationError" class="text-red-600 mb-4">
        {{ verificationError }}
      </div>

      <div v-else-if="verificationResult" class="flex-1 overflow-y-auto">
        <div class="mb-4 p-4 rounded-lg" :class="verificationResult.safe ? 'bg-green-50 border border-green-200' : 'bg-red-50 border border-red-200'">
          <div class="flex items-center gap-2">
            <span class="material-symbols-outlined" :class="verificationResult.safe ? 'text-green-600' : 'text-red-600'">
              {{ verificationResult.safe ? 'check_circle' : 'error' }}
            </span>
            <span class="font-bold" :class="verificationResult.safe ? 'text-green-800' : 'text-red-800'">
              {{ verificationResult.safe ? 'System is Safe' : 'System is Unsafe' }}
            </span>
          </div>
        </div>

        <div v-if="verificationResult.checkLogs && verificationResult.checkLogs.length > 0" class="mb-4">
          <h4 class="text-sm font-bold text-slate-700 mb-2">Logs</h4>
          <div class="bg-slate-100 p-2 rounded text-xs font-mono h-32 overflow-y-auto">
            <div v-for="(log, i) in verificationResult.checkLogs" :key="i">{{ log }}</div>
          </div>
        </div>

        <div v-if="!verificationResult.safe && verificationResult.traces && verificationResult.traces.length > 0">
          <h4 class="text-sm font-bold text-slate-700 mb-2">Violations ({{ verificationResult.traces.length }})</h4>
          <div class="space-y-2">
            <div v-for="(trace, i) in verificationResult.traces" :key="i" class="border border-slate-200 rounded p-2">
              <div class="text-xs font-bold text-slate-600 mb-1">Spec: {{ trace.violatedSpecId }}</div>
              <div class="text-xs text-slate-500">
                States: {{ trace.states?.length || 0 }}
              </div>
              <!-- Detailed trace display could go here -->
            </div>
          </div>
        </div>
      </div>

      <div class="mt-4 flex justify-end">
        <button
          @click="closeResultDialog"
          class="px-4 py-2 text-sm font-medium text-white bg-slate-600 rounded hover:bg-slate-700"
        >
          Close
        </button>
      </div>
    </div>
  </div>
</template>
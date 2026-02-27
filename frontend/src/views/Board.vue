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
import simulationApi from '@/api/simulation'

// Components
import DeviceDialog from '../components/DeviceDialog.vue'
import CanvasBoard from '../components/CanvasBoard.vue'
import ControlCenter from '../components/ControlCenter.vue'
import SystemInspector from '../components/SystemInspector.vue'
import RuleBuilderDialog from '../components/RuleBuilderDialog.vue'
import SimulationTimeline from '../components/SimulationTimeline.vue'

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
const internalVariableEdges = ref<DeviceEdge[]>([])  // 内部变量连线
const rules = ref<RuleForm[]>([])  // 独立存储规则列表

// 合并所有连线（规则连线 + 内部变量连线）
const allEdges = computed(() => {
  return [...edges.value, ...internalVariableEdges.value]
})
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

  await saveNodesToServer()
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
    // 从变量节点ID中提取主设备ID（格式：deviceId_variableName）
    const parts = varNode.id.split('_')
    if (parts.length < 2) return

    const deviceId = parts[0]
    const variableName = parts.slice(1).join('_')  // 处理变量名中可能包含下划线的情况

    // 找到对应的设备节点
    const deviceNode = nodes.value.find(n => n.id === deviceId)
    if (!deviceNode) return

    // 查找设备模板以确认这是内部变量
    const template = deviceTemplates.value.find(t => t.manifest.Name === deviceNode.templateName)
    const internalVar = template?.manifest.InternalVariables?.find(v => v.Name === variableName)
    if (!internalVar) return

    // 创建连线
    const edgeId = `edge_${deviceId}_to_${varNode.id}`
    const edge: DeviceEdge = {
      id: edgeId,
      from: deviceId,
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

  await createDeviceInstanceAt(tpl, { x, y })
  draggingTplName.value = null
}

const handleNodeMovedOrResized = async () => {
  // 更新内部变量连线的位置
  updateInternalVariableEdgePositions()

  await saveNodesToServer()
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

      ElMessage.success(t('app.addRuleSuccess') || '添加规则成功')
    } catch (e: any) {
      console.error('saveRules error', e)
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
  // 先找出要删除的内部变量节点ID（在删除主节点之前）
  const variableNodeIds = nodes.value
    .filter(n => n.id.startsWith(`${nodeId}_`) && n.templateName?.startsWith('variable_'))
    .map(n => n.id)
  
  // 删除设备及其内部变量节点
  nodes.value = nodes.value.filter(n => n.id !== nodeId && !n.id.startsWith(`${nodeId}_`))

  // 删除与该设备相关的规则
  const rulesToDelete = rules.value.filter(rule =>
    rule.toId === nodeId || rule.sources.some(source => source.fromId === nodeId)
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
  specifications.value = nextSpecs

  // 尝试保存到服务器，但不让保存失败影响UI更新
  try {
    // 将 Proxy 对象转换为普通对象后再发送
    const rulesToSave = JSON.parse(JSON.stringify(rules.value))
    await Promise.all([
      saveNodesToServer(),
      boardApi.saveRules(rulesToSave),
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
    ElMessage.success('删除规则成功')
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

// 从 rules 动态生成 edges（不单独存储到服务器）
const generateEdgesFromRules = (): DeviceEdge[] => {
  const result: DeviceEdge[] = []
  
  for (const rule of rules.value) {
    if (!rule.sources || !rule.toId) continue
    
    const toNode = nodes.value.find(n => n.id === rule.toId)
    if (!toNode) continue
    
    for (const source of rule.sources) {
      const fromId = source.fromId
      if (!fromId) continue
      
      const fromNode = nodes.value.find(n => n.id === fromId)
      if (!fromNode) continue
      
      const { fromPoint, toPoint } = getLinkPoints(fromNode, toNode)
      
      result.push({
        id: `edge_${rule.id}_${fromId}`,
        from: fromId,
        to: rule.toId,
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
    console.log('[Board] Saving specs to server:', specsToSave)
    await boardApi.saveSpecs(specsToSave)
  }
  catch (e) {
    console.error('[Board] Save specs failed:', e)
    // 打印更详细的错误信息
    if (e.response) {
      console.error('[Board] Server error response:', e.response.data)
      console.error('[Board] Server error status:', e.response.status)
    }
    ElMessage.error(t('app.saveSpecsFailed') || '保存规约失败')
  }
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
    const humidifierTpl = deviceTemplates.value.find(t => t.manifest?.Name === 'Humidifier')
    console.log('Humidifier template:', humidifierTpl)
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

  // 重新生成内部变量连线（根据已加载的节点和设备模板）
  regenerateInternalVariableEdges()
}

// 2.定义刷新规则的函数（edges 由 rules 动态生成）
const refreshRules = async () => {
  try {
    // 只获取规则列表
    const rulesData = await boardApi.getRules()
    console.log('🔍 [Board] 刷新规则 - 原始数据:', JSON.parse(JSON.stringify(rulesData)))
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
    '#6366f1', '#059669', '#C026D3', '#dc2626',
    '#ef4444', '#14b8a6', '#ec4899', '#eab308'
  ] // primary, online, secondary(purple), offline, red, teal, pink, yellow
  return colorValues[colorIndex] || colorValues[0]
}

// 辅助函数：判断是否是内部变量连线
const isInternalVariableEdgeById = (edgeId: string): boolean => {
  const edge = allEdges.value.find(e => e.id === edgeId)
  return edge?.itemType === 'variable' && edge?.relation === 'contains'
}

// Convert Tailwind bg- class to actual color value for SVG
const getCanvasMapColorValue = (nodeId: string): string => {
  // 内部变量连线使用灰色
  if (nodeId.startsWith('edge_') || isInternalVariableEdgeById(nodeId)) {
    return '#94a3b8' // 灰色
  }
  
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

// ==== Simulation Logic ====
const isSimulating = ref(false)
const simulationResult = ref<any>(null)
const simulationError = ref<string | null>(null)

// Simulation form state (moved from ControlCenter)
const simulationForm = reactive({
  steps: 10,
  isAttack: false,
  intensity: 3,
  enablePrivacy: false
})

// Floating panel visibility state
const showSimulationPanel = ref(false)

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

let playInterval: ReturnType<typeof setInterval> | null = null

// 当前选中的 trace
const currentTrace = computed(() => {
  // 优先使用 savedTraces
  if (savedTraces.value.length > 0) {
    return savedTraces.value[traceAnimationState.value.selectedTraceIndex] || null
  }
  return verificationResult.value?.traces?.[traceAnimationState.value.selectedTraceIndex] || null
})

// 当前状态
const currentState = computed(() => {
  if (!currentTrace.value?.states) return null
  return currentTrace.value.states[traceAnimationState.value.selectedStateIndex] || null
})

// 所有状态数量
const totalStates = computed(() => {
  return currentTrace.value?.states?.length || 0
})

// 打开反例路径动画
const openTraceAnimation = () => {
  if (verificationResult.value?.traces?.length > 0) {
    // 保存 traces 数据到独立变量
    savedTraces.value = [...verificationResult.value.traces]
    
    // 关闭验证结果对话框
    closeResultDialog()
    
    // 打开反例路径动画
    traceAnimationState.value = {
      visible: true,
      selectedTraceIndex: 0,
      selectedStateIndex: 0,
      isPlaying: false
    }
    // 高亮第一个状态 - 添加防御性检查确保 currentTrace 不为 null
    const trace = currentTrace.value
    if (trace) {
      highlightedTrace.value = {
        ...trace,
        selectedStateIndex: traceAnimationState.value.selectedStateIndex
      }
    }
  }
}

// 选择并播放指定索引的反例路径动画
const selectAndPlayTrace = (traceIndex: number) => {
  if (verificationResult.value?.traces?.length > 0 && traceIndex < verificationResult.value.traces.length) {
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
}

// 选择违规规约
const selectTrace = (index: number) => {
  traceAnimationState.value.selectedTraceIndex = index
  traceAnimationState.value.selectedStateIndex = 0
  const trace = currentTrace.value
  if (trace) {
    highlightedTrace.value = {
      ...trace,
      selectedStateIndex: traceAnimationState.value.selectedStateIndex
    }
  }
}

// 跳转到指定状态
const goToState = (index: number) => {
  traceAnimationState.value.selectedStateIndex = index
  const trace = currentTrace.value
  if (trace) {
    highlightedTrace.value = {
      ...trace,
      selectedStateIndex: traceAnimationState.value.selectedStateIndex
    }
  }
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

// 获取设备状态颜色
const getStateColor = (state: string): string => {
  const stateColors: Record<string, string> = {
    'heat': 'bg-red-500',
    'cool': 'bg-blue-500',
    'off': 'bg-gray-400',
    'on': 'bg-green-500',
    'auto': 'bg-purple-500',
    'dry': 'bg-yellow-500',
    'fanOnly': 'bg-cyan-500',
    'heatClean': 'bg-orange-500',
    'dryClean': 'bg-amber-500',
    'coolClean': 'bg-sky-500'
  }
  return stateColors[state?.toLowerCase()] || 'bg-slate-500'
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
const clearHighlight = () => {
  highlightedTrace.value = null
}

// ==== Simulation Timeline Animation Logic ====

// 打开模拟时间轴动画
const openSimulationTimeline = () => {
  if (simulationResult.value?.states?.length > 0) {
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
}

// 跳转到指定状态
const goToSimulationState = (index: number) => {
  simulationAnimationState.value.selectedStateIndex = index
  highlightedTrace.value = {
    states: savedSimulationStates.value,
    selectedStateIndex: index
  }
}

// 播放/停止模拟动画
const toggleSimulationAnimation = () => {
  if (simulationAnimationState.value.isPlaying) {
    stopSimulationAnimation()
  } else {
    startSimulationAnimation()
  }
}

let simulationPlayInterval: ReturnType<typeof setInterval> | null = null

const startSimulationAnimation = () => {
  if (simulationAnimationState.value.isPlaying) return
  
  simulationAnimationState.value.isPlaying = true
  simulationPlayInterval = setInterval(() => {
    const states = savedSimulationStates.value
    if (!states || states.length === 0) {
      stopSimulationAnimation()
      return
    }
    if (simulationAnimationState.value.selectedStateIndex < states.length - 1) {
      simulationAnimationState.value.selectedStateIndex++
      highlightedTrace.value = {
        states: savedSimulationStates.value,
        selectedStateIndex: simulationAnimationState.value.selectedStateIndex
      }
    } else {
      // 到达最后一个状态时停止播放，不循环
      stopSimulationAnimation()
    }
  }, 1500)
}

const stopSimulationAnimation = () => {
  simulationAnimationState.value.isPlaying = false
  if (simulationPlayInterval) {
    clearInterval(simulationPlayInterval)
    simulationPlayInterval = null
  }
}

// 高亮模拟状态
const handleHighlightSimulationState = (state: any) => {
  if (state) {
    highlightedTrace.value = {
      states: savedSimulationStates.value,
      selectedStateIndex: simulationAnimationState.value.selectedStateIndex
    }
  }
}

const handleVerify = async () => {
  if (nodes.value.length === 0) {
    ElMessage.warning({ message: 'No devices to verify', type: 'warning' })
    return
  }

  isVerifying.value = true
  verificationError.value = null
  verificationResult.value = null

  try {
    // ==== Helper function to normalize device names for NuSMV ====
    // NuSMV identifiers cannot start with a number, so we add a prefix
    const normalizeDeviceName = (name: string): string => {
      if (!name) return name
      // If starts with a digit, add prefix
      if (/^\d/.test(name)) {
        return 'd_' + name
      }
      return name
    }

    // Helper to convert value: remove quotes for numeric values
    const normalizeValue = (val: string): string => {
      if (!val) return val
      // If value is a quoted number, remove quotes
      if (/^"\d+"$/.test(val) || /^'\d+'$/.test(val)) {
        return val.replace(/^["']|["']$/g, '')
      }
      return val
    }

    // Create a mapping from original label to normalized name
    const deviceNameMap = new Map<string, string>()
    
    // 过滤掉变量节点（templateName 以 variable_ 开头）
    const deviceNodes = nodes.value.filter(node => !node.templateName.startsWith('variable_'))
    
    deviceNodes.forEach(node => {
      deviceNameMap.set(node.label, normalizeDeviceName(node.label))
    })

    // Prepare devices: Add default variables/privacies if missing
    const devices = deviceNodes.map(node => {
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
      // Use normalized name to ensure NuSMV compatibility
      const normalizedVarName = normalizeDeviceName(node.label)
      return {
        varName: normalizedVarName,  // Backend expects varName
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
        attribute: s.fromApi || '',
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

    // Prepare specs - normalize device names and values
    const specs = specifications.value.map(spec => ({
      ...spec,
      aConditions: (spec.aConditions || []).map((cond: any) => ({
        ...cond,
        deviceId: cond.deviceId ? normalizeDeviceName(cond.deviceId) : cond.deviceId,
        deviceLabel: cond.deviceLabel ? normalizeDeviceName(cond.deviceLabel) : cond.deviceLabel,
        value: normalizeValue(cond.value || '')
      })),
      ifConditions: (spec.ifConditions || []).map((cond: any) => ({
        ...cond,
        deviceId: cond.deviceId ? normalizeDeviceName(cond.deviceId) : cond.deviceId,
        deviceLabel: cond.deviceLabel ? normalizeDeviceName(cond.deviceLabel) : cond.deviceLabel,
        value: normalizeValue(cond.value || '')
      })),
      thenConditions: (spec.thenConditions || []).map((cond: any) => ({
        ...cond,
        deviceId: cond.deviceId ? normalizeDeviceName(cond.deviceId) : cond.deviceId,
        deviceLabel: cond.deviceLabel ? normalizeDeviceName(cond.deviceLabel) : cond.deviceLabel,
        value: normalizeValue(cond.value || '')
      }))
    }))

    // Also normalize device names in rules
    const normalizedRulesData = rulesData.map((r: any) => ({
      ...r,
      conditions: (r.conditions || []).map((c: any) => ({
        ...c,
        deviceName: c.deviceName ? normalizeDeviceName(c.deviceName) : c.deviceName,
        value: normalizeValue(c.value || '')
      })),
      command: {
        ...r.command,
        deviceName: r.command.deviceName ? normalizeDeviceName(r.command.deviceName) : r.command.deviceName
      }
    }))

    const req = {
      devices,
      rules: normalizedRulesData,
      specs,
      isAttack: false,
      intensity: 3
    }

    console.log('Verification Request JSON:', JSON.stringify(req, null, 2))

    const result = await boardApi.verify(req)
    verificationResult.value = result

    if (result.safe) {
      ElMessage.success({ message: 'Verification passed: System is safe!', type: 'success' })
    } else {
      ElMessage.warning({ message: `Verification failed: Found ${result.traces?.length || 0} violations`, type: 'warning' })
    }

  } catch (error: any) {
    console.error('Verification failed:', error)
    verificationError.value = error.message || 'Verification failed'
    ElMessage.error({ message: verificationError.value || 'Verification failed', type: 'error' })
  } finally {
    isVerifying.value = false
  }
}

const handleSimulate = async (simConfig: {
  steps: number
  isAttack: boolean
  intensity: number
  enablePrivacy: boolean
}) => {
  if (nodes.value.length === 0) {
    ElMessage.warning({ message: 'No devices to simulate', type: 'warning' })
    return
  }

  isSimulating.value = true
  simulationError.value = null
  simulationResult.value = null

  try {
    // 使用与验证相同的设备数据转换逻辑
    const normalizeDeviceName = (name: string): string => {
      if (!name) return name
      if (/^\d/.test(name)) {
        return 'd_' + name
      }
      return name
    }

    const normalizeValue = (val: string): string => {
      if (!val) return val
      if (/^"\d+"$/.test(val) || /^'\d+'$/.test(val)) {
        return val.replace(/^["']|["']$/g, '')
      }
      return val
    }

    const deviceNameMap = new Map<string, string>()

    // 过滤掉变量节点
    const deviceNodes = nodes.value.filter(node => !node.templateName.startsWith('variable_'))

    deviceNodes.forEach(node => {
      deviceNameMap.set(node.label, normalizeDeviceName(node.label))
    })

    // Prepare devices
    const devices = deviceNodes.map(node => {
      const tpl = deviceTemplates.value.find(t => t.manifest?.Name === node.templateName)
      const manifest = tpl?.manifest

      let variables = (node as any).variables || []
      if ((!variables || variables.length === 0) && manifest?.InternalVariables) {
        variables = manifest.InternalVariables.map((v: any) => ({
          name: v.Name,
          value: v.Default || '0',
          trust: 'trusted'
        }))
      }

      let privacies = (node as any).privacies || []
      if ((!privacies || privacies.length === 0) && manifest?.InternalVariables) {
        privacies = manifest.InternalVariables.map((v: any) => ({
          name: v.Name,
          privacy: v.Privacy || 'public'
        }))
      }

      const normalizedVarName = normalizeDeviceName(node.label)
      return {
        varName: normalizedVarName,
        templateName: node.templateName,
        state: node.state,
        currentStateTrust: (node as any).currentStateTrust || 'trusted',
        variables,
        privacies
      }
    })

    // Prepare rules
    const rulesData = rules.value.map(r => ({
      conditions: (r.sources || []).map(s => ({
        deviceName: s.fromId,
        attribute: s.fromApi || '',
        relation: s.relation || '=',
        value: s.value || 'true'
      })),
      command: {
        deviceName: r.toId || '',
        action: r.toApi || '',
        contentDevice: null,
        content: null
      },
      ruleString: r.name || ''
    }))

    // Normalize device names in rules
    const normalizedRulesData = rulesData.map((r: any) => ({
      ...r,
      conditions: (r.conditions || []).map((c: any) => ({
        ...c,
        deviceName: c.deviceName ? normalizeDeviceName(c.deviceName) : c.deviceName,
        value: normalizeValue(c.value || '')
      })),
      command: {
        ...r.command,
        deviceName: r.command.deviceName ? normalizeDeviceName(r.command.deviceName) : r.command.deviceName
      }
    }))

    const req = {
      devices,
      rules: normalizedRulesData,
      steps: simConfig.steps,
      isAttack: simConfig.isAttack,
      intensity: simConfig.intensity,
      enablePrivacy: simConfig.enablePrivacy
    }

    console.log('Simulation Request JSON:', JSON.stringify(req, null, 2))

    const result = await simulationApi.simulate(req)
    
    // 直接打开时间轴动画，不显示结果对话框
    if (result.states && result.states.length > 0) {
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
        message: `Simulation completed: ${result.states.length} states generated`,
        type: 'success'
      })
    } else {
      ElMessage.warning({
        message: 'Simulation completed but no states were generated',
        type: 'warning'
      })
    }

  } catch (error: any) {
    console.error('Simulation failed:', error)
    simulationError.value = error.message || 'Simulation failed'
    ElMessage.error({ message: simulationError.value || 'Simulation failed', type: 'error' })
  } finally {
    isSimulating.value = false
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
          @node-moved-or-resized="handleNodeMovedOrResized"
      />

    </div>

    <!-- Floating Action Buttons - Left of System Inspector -->
    <div class="fixed top-20 right-[285px] z-40 flex flex-col gap-3">
      <!-- Simulation Button (Circle) -->
      <button
        @click="showSimulationPanel = !showSimulationPanel"
        class="w-12 h-12 rounded-full bg-indigo-500 hover:bg-indigo-600 text-white shadow-lg hover:shadow-xl transition-all hover:scale-110 active:scale-95 flex items-center justify-center group"
        title="Simulation"
      >
        <span class="material-symbols-outlined text-xl">play_circle</span>
        <!-- Tooltip -->
        <span class="absolute right-full mr-3 px-2 py-1 bg-slate-800 text-white text-xs rounded opacity-0 group-hover:opacity-100 whitespace-nowrap transition-opacity pointer-events-none">
          Simulation
        </span>
      </button>

      <!-- Verify Button (Circle) -->
      <button
        @click="handleVerify"
        :disabled="isVerifying"
        class="w-12 h-12 rounded-full bg-green-500 hover:bg-green-600 disabled:bg-green-400 text-white shadow-lg hover:shadow-xl transition-all hover:scale-110 active:scale-95 flex items-center justify-center group disabled:cursor-not-allowed disabled:hover:scale-100"
        title="Start Verification"
      >
        <template v-if="isVerifying">
          <span class="material-symbols-outlined text-xl animate-spin">sync</span>
        </template>
        <template v-else>
          <span class="material-symbols-outlined text-xl">verified_user</span>
        </template>
        <!-- Tooltip -->
        <span class="absolute right-full mr-3 px-2 py-1 bg-slate-800 text-white text-xs rounded opacity-0 group-hover:opacity-100 whitespace-nowrap transition-opacity pointer-events-none">
          Start Verification
        </span>
      </button>
    </div>

    <!-- Simulation Panel (Appears when clicking simulation button) -->
    <div 
      v-if="showSimulationPanel"
      class="fixed top-20 right-[370px] z-30 w-72 bg-white rounded-xl shadow-xl border border-slate-200 overflow-hidden"
    >
      <!-- Simulation Header -->
      <div class="flex items-center justify-between p-3 bg-indigo-500">
        <div class="flex items-center gap-2">
          <div class="w-8 h-8 bg-white/20 rounded-lg flex items-center justify-center">
            <span class="material-symbols-outlined text-white text-lg">play_circle</span>
          </div>
          <div>
            <span class="text-sm font-bold text-white">Simulation</span>
            <p class="text-xs text-indigo-200">Config</p>
          </div>
        </div>
        <button 
          @click="showSimulationPanel = false"
          class="text-white/80 hover:text-white"
        >
          <span class="material-symbols-outlined">close</span>
        </button>
      </div>

      <!-- Simulation Content -->
      <div class="p-3 space-y-3 bg-indigo-50">
        <!-- Steps -->
        <div>
          <label class="block text-[10px] font-bold text-indigo-700 uppercase tracking-wide mb-1">
            Simulation Steps
          </label>
          <div class="flex items-center gap-2">
            <input
              v-model.number="simulationForm.steps"
              type="range"
              min="1"
              max="100"
              class="flex-1 h-2 bg-indigo-200 rounded-lg appearance-none cursor-pointer accent-indigo-600"
            />
            <span class="w-10 text-xs font-bold text-indigo-800 text-center bg-white rounded px-2 py-1 border border-indigo-200">
              {{ simulationForm.steps }}
            </span>
          </div>
        </div>

        <!-- Attack Mode -->
        <div class="flex items-center justify-between">
          <label class="text-xs font-bold text-indigo-700 uppercase tracking-wide">
            Attack
          </label>
          <button
            @click="simulationForm.isAttack = !simulationForm.isAttack"
            :class="[
              'relative inline-flex h-6 w-11 items-center rounded-full transition-colors',
              simulationForm.isAttack ? 'bg-red-500' : 'bg-indigo-300'
            ]"
          >
            <span
              :class="[
                'inline-block h-4 w-4 transform rounded-full bg-white transition-transform',
                simulationForm.isAttack ? 'translate-x-6' : 'translate-x-1'
              ]"
            />
          </button>
        </div>

        <!-- Intensity (visible when attack is enabled) -->
        <div v-if="simulationForm.isAttack">
          <label class="block text-[10px] font-bold text-indigo-700 uppercase tracking-wide mb-1">
            Intensity: {{ simulationForm.intensity }}
          </label>
          <input
            v-model.number="simulationForm.intensity"
            type="range"
            min="0"
            max="50"
            class="w-full h-2 bg-indigo-200 rounded-lg appearance-none cursor-pointer accent-red-500"
          />
        </div>

        <!-- Privacy Analysis -->
        <div class="flex items-center justify-between">
          <label class="text-xs font-bold text-indigo-700 uppercase tracking-wide">
            Privacy
          </label>
          <button
            @click="simulationForm.enablePrivacy = !simulationForm.enablePrivacy"
            :class="[
              'relative inline-flex h-6 w-11 items-center rounded-full transition-colors',
              simulationForm.enablePrivacy ? 'bg-purple-500' : 'bg-indigo-300'
            ]"
          >
            <span
              :class="[
                'inline-block h-4 w-4 transform rounded-full bg-white transition-transform',
                simulationForm.enablePrivacy ? 'translate-x-6' : 'translate-x-1'
              ]"
            />
          </button>
        </div>

        <!-- Simulate Button -->
        <button
          @click="handleSimulate({ ...simulationForm }); showSimulationPanel = false"
          :disabled="isSimulating"
          class="w-full py-2.5 bg-indigo-600 hover:bg-indigo-700 disabled:bg-indigo-300 text-white rounded-lg text-xs font-bold uppercase tracking-wider transition-all shadow-md hover:shadow-lg hover:scale-[1.02] active:scale-[0.98] flex items-center justify-center gap-2 disabled:cursor-not-allowed disabled:hover:scale-100"
        >
          <template v-if="isSimulating">
            <span class="material-symbols-outlined text-sm animate-spin">sync</span>
            Running...
          </template>
          <template v-else>
            <span class="material-symbols-outlined text-sm">play_arrow</span>
            Run
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

    <!-- Canvas Map - Fixed at bottom right -->
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

  <!-- Simulation Result Dialog -->
  <div v-if="simulationResult || simulationError" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="simulationResult = null; simulationError = null">
    <div class="bg-white rounded-xl p-6 w-[700px] max-w-[90vw] shadow-2xl max-h-[85vh] flex flex-col" @click.stop>
      <div class="flex items-center justify-between mb-4">
        <div class="flex items-center gap-3">
          <div class="w-10 h-10 bg-indigo-100 rounded-lg flex items-center justify-center">
            <span class="material-symbols-outlined text-indigo-600 text-xl">play_circle</span>
          </div>
          <div>
            <h3 class="text-lg font-semibold text-slate-800">Simulation Result</h3>
            <p class="text-xs text-slate-500" v-if="simulationResult">
              {{ simulationResult.steps || 0 }} states generated from {{ simulationResult.requestedSteps || 0 }} requested steps
            </p>
          </div>
        </div>
        <button @click="simulationResult = null; simulationError = null" class="text-slate-400 hover:text-slate-600">
          <span class="material-symbols-outlined">close</span>
        </button>
      </div>

      <div v-if="simulationError" class="text-red-600 mb-4 p-4 bg-red-50 rounded-lg">
        {{ simulationError }}
      </div>

      <div v-else-if="simulationResult" class="flex-1 overflow-hidden flex flex-col">
        <!-- Logs -->
        <div class="mb-4">
          <h4 class="text-sm font-bold text-slate-700 mb-2">Execution Logs</h4>
          <div class="bg-slate-900 rounded-lg p-3 max-h-32 overflow-y-auto">
            <pre class="text-xs text-green-400 font-mono whitespace-pre-wrap">{{ simulationResult.logs?.join('\n') || 'No logs available' }}</pre>
          </div>
        </div>

        <!-- States Preview -->
        <div class="flex-1 overflow-hidden flex flex-col">
          <h4 class="text-sm font-bold text-slate-700 mb-2">Simulation States ({{ simulationResult.states?.length || 0 }})</h4>
          <div class="flex-1 overflow-y-auto border border-slate-200 rounded-lg">
            <table class="w-full text-xs">
              <thead class="bg-slate-50 sticky top-0">
                <tr>
                  <th class="text-left p-2 font-bold text-slate-600 border-b">State #</th>
                  <th class="text-left p-2 font-bold text-slate-600 border-b">Devices</th>
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
            Show Raw NuSMV Output
          </summary>
          <div class="mt-2 bg-slate-900 rounded-lg p-3 max-h-40 overflow-y-auto">
            <pre class="text-xs text-slate-300 font-mono whitespace-pre-wrap">{{ simulationResult.nusmvOutput || 'No output' }}</pre>
          </div>
        </details>
      </div>

      <div class="mt-4 pt-4 border-t border-slate-200 flex justify-end gap-3">
        <button
          v-if="simulationResult && simulationResult.states && simulationResult.states.length > 0"
          @click="openSimulationTimeline"
          class="px-4 py-2 bg-gradient-to-r from-indigo-500 to-indigo-600 hover:from-indigo-600 hover:to-indigo-700 text-white rounded-lg text-sm font-medium transition-colors flex items-center gap-2"
        >
          <span class="material-symbols-outlined text-lg">play_circle</span>
          View Timeline
        </button>
        <button
          @click="simulationResult = null; simulationError = null"
          class="px-4 py-2 bg-slate-200 hover:bg-slate-300 text-slate-700 rounded-lg text-sm font-medium transition-colors"
        >
          Close
        </button>
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

        <div v-if="!verificationResult.safe && verificationResult.traces && verificationResult.traces.length > 0">
          <h4 class="text-sm font-bold text-slate-700 mb-2">Violations ({{ verificationResult.traces.length }})</h4>
          <div class="space-y-2">
            <div v-for="(trace, i) in verificationResult.traces" :key="i" class="border border-slate-200 rounded p-3">
              <div class="flex items-center justify-between mb-1">
                <div class="text-xs font-bold text-red-600">Violation #{{ Number(i) + 1 }}</div>
                <button
                  @click="selectAndPlayTrace(Number(i))"
                  class="px-2 py-1 bg-red-500 hover:bg-red-600 text-white rounded text-xs font-medium transition-colors flex items-center gap-1"
                >
                  <span class="material-symbols-outlined text-xs">play_arrow</span>
                  View Trace
                </button>
              </div>
              <div class="text-xs font-bold text-slate-600 mb-1">Spec: {{ trace.violatedSpecId }}</div>
              <div v-if="trace.violatedSpecJson" class="text-xs font-mono text-slate-700 bg-slate-50 p-2 rounded mt-1">
                {{ formatSpec(trace.violatedSpecJson) }}
              </div>
              <div class="text-xs text-slate-500 mt-1">
                States: {{ trace.states?.length || 0 }}
              </div>
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
    class="fixed left-2/3 -translate-x-1/2 bottom-8 z-40"
  >
    <div class="bg-white rounded-xl shadow-2xl border border-slate-200 p-4 w-[600px] max-h-[70vh] overflow-y-auto">
      
      <!-- Violation Info - Only show at violation point -->
      <div 
        v-if="traceAnimationState.selectedStateIndex === totalStates - 1"
        class="mb-3 pb-3 border-b border-slate-200"
      >
        <!-- Violated Spec -->
        <div v-if="formattedSpec" class="p-2 bg-red-50 border border-red-200 rounded-lg">
          <div class="flex items-center justify-between mb-2">
            <div class="text-xs font-semibold text-red-600 uppercase">Violated Specification</div>
            <button @click="closeTraceAnimation" class="text-slate-400 hover:text-slate-600">
              <span class="material-symbols-outlined">close</span>
            </button>
          </div>
          <div class="text-xs font-mono text-slate-800">{{ formattedSpec }}</div>
        </div>
      </div>

      <!-- Timeline -->
      <div class="mb-3">
        <div class="flex items-center justify-between mb-2">
          <div class="flex items-center gap-2">
            <span class="text-sm font-bold text-slate-700">State Sequence</span>
            <span class="px-2 py-0.5 bg-red-100 text-red-600 text-xs rounded-full">
              {{ traceAnimationState.selectedStateIndex + 1 }} / {{ totalStates }}
            </span>
          </div>
          <button
            @click="toggleTraceAnimation"
            class="px-3 py-1.5 rounded-lg text-xs font-medium transition-colors flex items-center gap-1"
            :class="traceAnimationState.isPlaying 
              ? 'bg-red-500 text-white' 
              : 'bg-slate-100 text-slate-700 hover:bg-slate-200'"
          >
            <span class="material-symbols-outlined text-sm">{{ traceAnimationState.isPlaying ? 'stop' : 'play_arrow' }}</span>
            {{ traceAnimationState.isPlaying ? 'Stop' : 'Play' }}
          </button>
        </div>
        
        <!-- Timeline bar -->
        <div class="relative h-8 px-2">
          <div class="absolute top-1/2 left-2 right-2 h-2 bg-slate-200 rounded"></div>
          <!-- 红色横线 - 只在非最后一个状态时显示 -->
          <div 
            v-if="traceAnimationState.selectedStateIndex < totalStates - 1"
            class="absolute top-1/2 h-2 bg-red-500 rounded transition-all duration-300"
            :style="{ 
              left: totalStates > 1 ? `${(traceAnimationState.selectedStateIndex / (totalStates - 1)) * 100}%` : '0%',
              width: totalStates > 1 ? `${(1 / (totalStates - 1)) * 100}%` : '100%',
              transform: 'translateY(-50%)'
            }"
          ></div>
          
          <!-- State nodes -->
          <div class="absolute top-1/2 left-2 right-2 flex justify-between items-center -translate-y-1/2">
            <button
              v-for="(_, index) in currentTrace.states || []"
              :key="index"
              @click="goToState(Number(index))"
              class="w-6 h-6 rounded-full border-3 transition-all flex items-center justify-center relative z-10"
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

  <!-- Simulation Timeline 组件 -->
  <SimulationTimeline
    :visible="simulationAnimationState.visible"
    :states="savedSimulationStates"
    @update:visible="simulationAnimationState.visible = $event"
    @highlight-state="handleHighlightTrace"
  />
</template>
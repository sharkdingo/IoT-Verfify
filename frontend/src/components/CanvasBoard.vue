<script setup lang="ts">
import { computed, nextTick, onBeforeUnmount, onMounted, ref, watch } from 'vue'
import { useI18n } from 'vue-i18n'

import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { CanvasPan } from '../types/canvas'

import {
  updateEdgesForNode,
  getSelfLoopD
} from '../utils/canvas/geometry'

import { getLinkPoints } from '../utils/rule'

import {
  findTraceVariableAtOrBefore,
  isEdgeActiveInTrace,
  isEdgeCompromisedInTrace,
  normalizeTraceComparable,
  shouldAnimateEdgeFlow,
  toTraceDeviceId,
  traceDeviceMatchesId,
  traceVariableMatchesName,
  type TraceDeviceLike
} from '../utils/traceEdgePlayback'
import {
  isDeviceRepresentedInPlayback,
  playbackDeviceChanged,
  playbackDeviceSecurityFacts
} from '../utils/traceView'

const { t } = useI18n()

import {
  createNodeDragState,
  beginNodeDrag,
  updateNodeDrag,
  endNodeDrag
} from '../utils/canvas/nodeDrag'

import {
  createNodeResizeState,
  beginNodeResize,
  updateNodeResize,
  endNodeResize
} from '../utils/canvas/nodeResize'

// Particle animation utilities
const getParticleOpacity = (index: number): string => {
  const opacities = ['opacity-80', 'opacity-60', 'opacity-40']
  return opacities[index % opacities.length]
}

// 判断是否为内部变量连线
const isInternalVariableEdge = (edge: DeviceEdge): boolean => {
  return edge.itemType === 'variable' && edge.relation === 'contains'
}

// Get particle color based on source device color (for edges)
const getParticleColorByEdge = (edge: DeviceEdge): string => {
  // 内部变量连线使用简单的灰色
  if (isInternalVariableEdge(edge)) {
    return '#94a3b8'
  }

  const sourceNode = props.nodes.find(n => n.id === edge.from)
  if (!sourceNode) return 'url(#grad-blue)' // fallback

  const colorIndex = getNodeColorIndex(sourceNode.id)
  const gradients = [
    'url(#grad-blue)', 'url(#grad-green)', 'url(#grad-purple)', 'url(#grad-orange)',
    'url(#grad-red)', 'url(#grad-teal)', 'url(#grad-pink)', 'url(#grad-yellow)'
  ]
  return gradients[colorIndex] || gradients[0]
}

const getParticleSize = (index: number): number => {
  const sizes = [3, 2, 2.5]
  return sizes[index % sizes.length]
}

const TRACE_FLOW_DURATION = '1.1s'

// Node color utilities (matching Canvas Map colors)
// Use node ID to generate stable color assignment
const getNodeColorIndex = (nodeId: string): number => {
  // 为每个节点生成随机但一致的颜色索引
  // 使用节点ID作为种子，确保同一个节点始终有相同颜色
  let hash = 5381
  for (let i = 0; i < nodeId.length; i++) {
    const char = nodeId.charCodeAt(i)
    hash = ((hash << 5) + hash) + char // hash * 33 + char
  }

  // 使用更大的模数来获得更多颜色变化
  return Math.abs(hash) % 8 // 现在有8种可能的颜色
}

// Test function to verify color distribution (removed console logs)
const testColorDistribution = () => {
  // 使用后端设备模板名称作为测试数据
  const testIds = [
    'Temperature Sensor', 'Air Conditioner', 'Light', 
    'Window', 'Door', 'Camera', 'Thermostat'
  ]
  const colorCounts = [0, 0, 0, 0]
  testIds.forEach(id => {
    const index = getNodeColorIndex(id)
    colorCounts[index]++
  })
  // Color distribution verified silently
}

const getNodeColorClass = (nodeId: string): string => {
  const colors = [
    'border-primary', 'border-online', 'border-secondary', 'border-offline',
    'border-red-500', 'border-teal-500', 'border-pink-500', 'border-yellow-500'
  ]
  return colors[getNodeColorIndex(nodeId)]
}

const getNodeBgColorClass = (nodeId: string): string => {
  const bgColors = [
    'bg-blue-50', 'bg-green-50', 'bg-purple-50', 'bg-orange-50',
    'bg-red-50', 'bg-teal-50', 'bg-pink-50', 'bg-yellow-50'
  ]
  return bgColors[getNodeColorIndex(nodeId)]
}

// Get actual background color for inline styling
const getNodeBgColor = (nodeId: string): string => {
  const colorIndex = getNodeColorIndex(nodeId)
  const bgColors: Record<number, string> = {
    0: 'rgba(239, 246, 255, 0.9)', // blue-50 with opacity
    1: 'rgba(236, 253, 245, 0.9)', // green-50 with opacity
    2: 'rgba(245, 243, 255, 0.9)', // purple-50 with opacity
    3: 'rgba(255, 247, 237, 0.9)', // orange-50 with opacity
    4: 'rgba(254, 242, 242, 0.9)', // red-50 with opacity
    5: 'rgba(240, 253, 250, 0.9)', // teal-50 with opacity
    6: 'rgba(253, 244, 255, 0.9)', // pink-50 with opacity
    7: 'rgba(254, 249, 195, 0.9)'  // yellow-50 with opacity
  }
  return bgColors[colorIndex] || bgColors[0]
}

// Get actual border color for inline styling
const getNodeBorderColor = (nodeId: string): string => {
  const colorIndex = getNodeColorIndex(nodeId)
  const borderColors: Record<number, string> = {
    0: '#2563EB', // primary blue
    1: '#059669', // online green
    2: '#C026D3', // secondary purple
    3: '#dc2626', // offline red
    4: '#ef4444', // red
    5: '#14b8a6', // teal
    6: '#ec4899', // pink
    7: '#eab308'  // yellow
  }
  return borderColors[colorIndex] || borderColors[0]
}

const getVariableNodeBorderColor = (node: DeviceNode): string => getNodeBorderColor(node.id)

const getVariableNodeBgColor = (node: DeviceNode): string => getNodeBgColor(node.id)

// Get arrow marker ID based on source device color
const getArrowMarker = (edge: DeviceEdge): string => {
  // 内部变量连线不显示箭头
  if (edge.itemType === 'variable' && edge.relation === 'contains') {
    return ''
  }

  const sourceNode = props.nodes.find(n => n.id === edge.from)
  if (!sourceNode) return 'url(#arrow-blue)' // fallback

  const colorIndex = getNodeColorIndex(sourceNode.id)
  const markers = [
    'url(#arrow-blue)', 'url(#arrow-green)', 'url(#arrow-purple)', 'url(#arrow-orange)',
    'url(#arrow-red)', 'url(#arrow-teal)', 'url(#arrow-pink)', 'url(#arrow-yellow)'
  ]
  return markers[colorIndex] || markers[0]
}

// Get particle fill color (solid color) based on source device color
const getParticleFillColor = (edge: DeviceEdge): string => {
  const sourceNode = props.nodes.find(n => n.id === edge.from)
  if (!sourceNode) return '#3B82F6' // fallback blue

  const colorIndex = getNodeColorIndex(sourceNode.id)
  const colors = [
    '#2563EB', '#059669', '#C026D3', '#dc2626',
    '#ef4444', '#14b8a6', '#ec4899', '#eab308'
  ] // solid colors
  return colors[colorIndex] || colors[0]
}

const fallbackDeviceSvg = `<svg width="72" height="72" viewBox="0 0 72 72" fill="none" xmlns="http://www.w3.org/2000/svg">
  <rect x="14" y="12" width="44" height="48" rx="10" fill="#E2E8F0" stroke="#64748B" stroke-width="3"/>
  <circle cx="36" cy="32" r="10" fill="#FFFFFF" stroke="#94A3B8" stroke-width="3"/>
  <path d="M26 50h20" stroke="#64748B" stroke-width="4" stroke-linecap="round"/>
</svg>`

const svgDataUri = (svg: string): string =>
  `data:image/svg+xml;base64,${btoa(unescape(encodeURIComponent(svg)))}`

// Handle image loading errors by showing a stable inline SVG fallback.
const handleImageError = (event: Event) => {
  const img = event.target as HTMLImageElement
  img.onerror = null
  img.src = svgDataUri(fallbackDeviceSvg)
}

const getVariableNodeParts = (node: DeviceNode): { parentId: string; variableName: string } | null => {
  if (!isVariableNode(node)) return null
  const parent = props.nodes
    .filter(candidate => !isVariableNode(candidate) && node.id.startsWith(`${candidate.id}_`))
    .sort((a, b) => b.id.length - a.id.length)[0]
  if (!parent) return null
  return {
    parentId: parent.id,
    variableName: node.id.slice(parent.id.length + 1)
  }
}

// 获取节点的前一个状态（用于动画判断）
const getPreviousState = (node: DeviceNode): string | null => {
  if (!props.highlightedTrace?.states) return null
  if (props.highlightedTrace.selectedStateIndex === undefined || props.highlightedTrace.selectedStateIndex <= 0) return null

  const currentIndex = props.highlightedTrace.selectedStateIndex
  // 查找前一个状态
  for (let i = currentIndex - 1; i >= 0; i--) {
    const state = props.highlightedTrace.states[i]
    if (!state?.devices) continue

    const device = state.devices.find(d => traceDeviceMatchesId(d, node.id))

    if (device) {
      const prev = device.state || null
      return prev
    }
  }
  return null
}

// Check the user-facing compromise state returned by the trace API.
const isDeviceAttacked = (nodeId: string): boolean => {
  if (!props.highlightedTrace?.states || props.highlightedTrace.selectedStateIndex === undefined) {
    return false
  }

  // 从当前选中状态向前查找，找到设备最近的状态
  const currentIndex = props.highlightedTrace.selectedStateIndex
  for (let i = currentIndex; i >= 0; i--) {
    const state = props.highlightedTrace.states[i]
    if (!state?.devices) continue

    const device = state.devices.find(d => traceDeviceMatchesId(d, nodeId))

    if (device?.compromised === true) return true
  }

  return false
}

// 获取节点的当前状态
const getNodeState = (node: DeviceNode): string => {
  if (props.highlightedTrace && props.highlightedTrace.selectedStateIndex !== undefined) {
    const traceDevice = getLatestTraceDeviceForNode(node.id)
    if (!traceDevice) {
      return t('app.traceVisualization.notRepresentedInTrace')
    }
    return traceDevice.state?.trim() || t('app.traceVisualization.stateUnavailableInTrace')
  }
  return node.state || 'Working'
}

// 获取状态显示的样式类
const getStateDisplayClass = (node: DeviceNode): string => {
  const state = getNodeState(node) || 'Working'
  // 根据状态返回不同的样式类
  const stateLower = state.toLowerCase()
  if (stateLower === 'off' || stateLower === 'closed' || stateLower === 'locked' || stateLower === 'stop' || stateLower === 'pause') {
    return 'state-offline'
  }
  if (stateLower === 'on' || stateLower === 'open' || stateLower === 'unlocked' || stateLower === 'run' || stateLower === 'working') {
    return 'state-online'
  }
  if (stateLower.includes('heat') || stateLower.includes('cool') || stateLower.includes('dry')) {
    return 'state-active'
  }
  return 'state-default'
}

const isVariableNode = (_node: DeviceNode): boolean => false

// 获取节点当前状态对应的图标
const getCurrentNodeIcon = (node: DeviceNode): string => {
  if (isTraceActive.value && !getLatestTraceDeviceForNode(node.id)) {
    return props.getNodeIcon(node) || svgDataUri(fallbackDeviceSvg)
  }
  const currentState = getNodeState(node) || 'Working'

  return props.getNodeIcon(node, currentState) || svgDataUri(fallbackDeviceSvg)
}

const getNodeVisualStateKey = (node: DeviceNode): string =>
  `${toTraceDeviceId(node.id)}:${getNodeState(node)}`

const props = defineProps<{
  /** 所有设备节点（Board.vue 的 nodes.value） */
  nodes: DeviceNode[]
  /** 所有边（Board.vue 的 edges.value） */
  edges: DeviceEdge[]
  /** 画布平移（Board.vue 的 canvasPan.value） */
  pan: CanvasPan
  /** 画布缩放（Board.vue 的 canvasZoom.value） */
  zoom: number
  /** 获取节点图标路径（Board.vue 传入 getNodeIcon） */
  getNodeIcon: (node: DeviceNode, stateOverride?: string) => string
  /** 获取节点标签样式（Board.vue 传入 getNodeLabelStyle） */
  getNodeLabelStyle: (node: DeviceNode) => Record<string, string | number>
  /** 高亮显示的反例路径 */
  highlightedTrace?: {
    states: Array<{
      devices: TraceDeviceLike[]
      envVariables?: Array<{ name: string; value: string; trust?: string }>
      rules?: number[]
    }>
    selectedStateIndex?: number
  } | null
  focusedNodeId?: string | null
  focusedRuleId?: string | null
  /** Model playback is a saved snapshot; prevent canvas mutations while it is visible. */
  interactionLocked?: boolean
}>()

const GRID_SIZE_PX = 32

const canvasGridStyle = computed(() => {
  const gridSize = Math.max(8, GRID_SIZE_PX * props.zoom)
  const offsetX = ((props.pan.x % gridSize) + gridSize) % gridSize
  const offsetY = ((props.pan.y % gridSize) + gridSize) % gridSize
  return {
    '--canvas-grid-size': `${gridSize}px`,
    '--canvas-grid-offset-x': `${offsetX}px`,
    '--canvas-grid-offset-y': `${offsetY}px`
  }
})

const getLatestTraceVariableValueForNode = (nodeId: string, variableName: string): string | null => {
  if (!props.highlightedTrace?.states) return null
  const currentIndex = props.highlightedTrace.selectedStateIndex || 0
  const variable = findTraceVariableAtOrBefore(props.highlightedTrace, nodeId, variableName, currentIndex)
  return variable ? normalizeTraceComparable(variable.value) : null
}

const getLatestTraceVariableForNode = (nodeId: string, variableName: string) => {
  if (!props.highlightedTrace?.states) return null
  return findTraceVariableAtOrBefore(
    props.highlightedTrace,
    nodeId,
    variableName,
    props.highlightedTrace.selectedStateIndex || 0
  )
}

const getPreviousTraceVariableValueForNode = (nodeId: string, variableName: string): string | null => {
  if (!props.highlightedTrace?.states || props.highlightedTrace.selectedStateIndex === undefined) return null
  if (props.highlightedTrace.selectedStateIndex <= 0) return null
  const variable = findTraceVariableAtOrBefore(props.highlightedTrace, nodeId, variableName, props.highlightedTrace.selectedStateIndex - 1)
  return variable ? normalizeTraceComparable(variable.value) : null
}

const getLatestTraceDeviceForNodeAtOrBefore = (nodeId: string, endIndex: number): TraceDeviceLike | null => {
  if (!props.highlightedTrace?.states) return null
  const boundedIndex = Math.min(Math.max(endIndex, 0), props.highlightedTrace.states.length - 1)
  for (let i = boundedIndex; i >= 0; i--) {
    const state = props.highlightedTrace.states[i]
    if (!state?.devices) continue
    const device = state.devices.find(d => traceDeviceMatchesId(d, nodeId))
    if (device) return device
  }
  return null
}

const getLatestTraceDeviceForNode = (nodeId: string): TraceDeviceLike | null =>
  getLatestTraceDeviceForNodeAtOrBefore(nodeId, props.highlightedTrace?.selectedStateIndex || 0)

const getPreviousTraceDeviceForNode = (nodeId: string): TraceDeviceLike | null => {
  const selectedIndex = props.highlightedTrace?.selectedStateIndex
  if (selectedIndex === undefined || selectedIndex <= 0) return null
  return getLatestTraceDeviceForNodeAtOrBefore(nodeId, selectedIndex - 1)
}

const getEdgePlaybackClass = (edge: DeviceEdge) => {
  const traceActive = isEdgeActiveInTrace(edge, props.edges, props.highlightedTrace)
  const linkCompromised = isEdgeCompromisedInTrace(edge, props.highlightedTrace)
  const ruleFocused = Boolean(props.focusedRuleId && edge.ruleId === props.focusedRuleId)
  return {
    'edge-line--active': traceActive,
    'edge-line--compromised': linkCompromised,
    'edge-line--focused': ruleFocused,
    'edge-line--dimmed': isTraceActive.value && !traceActive && !linkCompromised && !ruleFocused
  }
}

// 判断是否有反例路径动画在进行
const isTraceActive = computed(() => {
  return Boolean(
    props.highlightedTrace?.states &&
    props.highlightedTrace.selectedStateIndex !== undefined &&
    props.highlightedTrace.selectedStateIndex >= 0
  )
})

// Each selected transition gets a fresh CSS animation mount, including rapid manual jumps.
const nodeAnimationTrigger = ref<Record<string, number>>({})
let nodeAnimationResetTimer: ReturnType<typeof setTimeout> | null = null
let nodeAnimationSequence = 0

// Animate only the delta that produced the selected model state. A manual jump to
// state N still compares N with N-1, rather than with whichever state the user last viewed.
watch(() => props.highlightedTrace?.selectedStateIndex, async (newIndex, oldIndex) => {
  if (newIndex === undefined) {
    nodeAnimationSequence++
    nodeAnimationTrigger.value = {}
    if (nodeAnimationResetTimer) {
      clearTimeout(nodeAnimationResetTimer)
      nodeAnimationResetTimer = null
    }
    return
  }
  if (newIndex === oldIndex) return

  const sequence = ++nodeAnimationSequence
  nodeAnimationTrigger.value = {}
  await nextTick()
  if (sequence !== nodeAnimationSequence || props.highlightedTrace?.selectedStateIndex !== newIndex) return

  const nextTriggers: Record<string, number> = {}
  for (const node of props.nodes) {
    if (!isNodeTraceChanged(node)) continue
    const triggerKey = toTraceDeviceId(node.id)
    nextTriggers[triggerKey] = sequence
  }
  nodeAnimationTrigger.value = nextTriggers

  if (nodeAnimationResetTimer) {
    clearTimeout(nodeAnimationResetTimer)
  }
  nodeAnimationResetTimer = setTimeout(() => {
    nodeAnimationTrigger.value = {}
    nodeAnimationResetTimer = null
  }, 760)
})

const shouldAnimateTraceChange = (node: DeviceNode): boolean =>
  !!nodeAnimationTrigger.value[toTraceDeviceId(node.id)]

const isNodeRepresentedInTrace = (node: DeviceNode): boolean =>
  isTraceActive.value && isDeviceRepresentedInPlayback(props.highlightedTrace?.states, node.id)

// Whether the selected state (or a prior sparse state) has authoritative data for the node.
const isNodeInTrace = (node: DeviceNode): boolean => {
  return isTraceActive.value && getLatestTraceDeviceForNode(node.id) !== null
}

// Trace fallback for non-authoritative variable rows.
const getTraceVariableValue = (node: DeviceNode): { value: string; state: string } | null => {
  if (!isTraceActive.value || !props.highlightedTrace?.states) return null
  
  const variableParts = getVariableNodeParts(node)
  if (!variableParts) return null

  const parentDeviceId = variableParts.parentId
  const variableName = variableParts.variableName
  
  // 从当前选中状态向前查找，找到设备最近的变量值和状态
  const currentIndex = props.highlightedTrace.selectedStateIndex || 0
  for (let i = currentIndex; i >= 0; i--) {
    const state = props.highlightedTrace.states[i]
    if (!state?.devices) continue
    
    const deviceState = state.devices.find(d => traceDeviceMatchesId(d, parentDeviceId))
    
    if (deviceState) {
      // 查找对应的变量值（大小写不敏感匹配）
      const variable = deviceState.variables?.find(v => traceVariableMatchesName(v, variableName))
      
      if (variable) {
        return {
          value: variable.value === null || variable.value === undefined || variable.value === ''
            ? 'Unknown'
            : String(variable.value),
          state: deviceState.state || 'Working'
        }
      }
      // 如果当前状态没有该变量，继续向前查找（使用上一个时间点的值）
    }
  }
  
  return null
}

const emit = defineEmits<{
  /** 背景按下，用于 Board.vue 开始画布平移 */
  (e: 'canvas-pointerdown', evt: PointerEvent): void
  /** dragover 事件，留给 Board.vue 做设备拖拽创建 */
  (e: 'canvas-dragover', evt: DragEvent): void
  /** drop 事件，留给 Board.vue 做设备拖拽创建 */
  (e: 'canvas-drop', evt: DragEvent): void
  /** mouseenter / mouseleave 用于控制 isCanvasHovered */
  (e: 'canvas-enter'): void
  (e: 'canvas-leave'): void
  /** wheel 事件仍交给 Board.vue 控制缩放 */
  (e: 'canvas-wheel', evt: WheelEvent): void
  /** 键盘或辅助技术打开节点详情 */
  (e: 'node-open', node: DeviceNode): void
  /** 鼠标、键盘或辅助技术打开节点上下文菜单 */
  (e: 'node-context', node: DeviceNode, position: { x: number; y: number }): void
  /** 键盘删除节点 */
  (e: 'node-delete', nodeId: string): void
  /** 节点拖拽或缩放结束，通知 Board.vue 持久化 nodes/edges */
  (e: 'node-moved-or-resized', nodeId: string): void
}>()

/* ====== 节点拖拽状态 ====== */

const dragState = createNodeDragState()

const onNodePointerDown = (e: PointerEvent, node: DeviceNode) => {
  e.preventDefault()
  if (e.button !== 0 || !e.isPrimary) {
    return
  }
  if (props.interactionLocked) {
    return
  }
  // 只处理节点自身拖拽，不影响画布平移（事件在模板里用了 .stop）
  beginNodeDrag(e, node, dragState)
  window.addEventListener('pointermove', onNodePointerMove)
  window.addEventListener('pointerup', onNodePointerUp)
}

const onNodePointerMove = (e: PointerEvent) => {
  const changed = updateNodeDrag(e, dragState, props.zoom)
  if (!changed || !dragState.node) return

  // 节点位置变了，更新相关边几何
  updateEdgesForNode(dragState.node.id, props.nodes, props.edges)
}

const onNodePointerUp = () => {
  const node = dragState.node
  const movedEnough = node
    ? Math.hypot(
      node.position.x - dragState.origin.x,
      node.position.y - dragState.origin.y
    ) > 1
    : false
  const moved = endNodeDrag(dragState)
  if (moved) {
    if (movedEnough) {
      emit('node-moved-or-resized', moved.id)
    } else if (!isVariableNode(moved)) {
      emit('node-open', moved)
    }
  }
  window.removeEventListener('pointermove', onNodePointerMove)
  window.removeEventListener('pointerup', onNodePointerUp)
}

/* ====== 节点缩放状态 ====== */

const resizeState = createNodeResizeState()

const onPointerDownResize = (
    e: PointerEvent,
    node: DeviceNode,
    dir: 'tl' | 'tr' | 'bl' | 'br'
) => {
  e.stopPropagation()
  e.preventDefault()
  if (props.interactionLocked) return
  beginNodeResize(e, node, dir, resizeState)
  window.addEventListener('pointermove', onPointerMoveResize)
  window.addEventListener('pointerup', onPointerUpResize)
}

const onPointerMoveResize = (e: PointerEvent) => {
  const changed = updateNodeResize(e, resizeState, props.zoom)
  if (!changed || !resizeState.node) return

  updateEdgesForNode(resizeState.node.id, props.nodes, props.edges)
}

const onPointerUpResize = () => {
  const resized = endNodeResize(resizeState)
  if (resized) {
    emit('node-moved-or-resized', resized.id)
  }
  window.removeEventListener('pointermove', onPointerMoveResize)
  window.removeEventListener('pointerup', onPointerUpResize)
}

/* ====== 自环路径封装（调用 utils/canvas/geometry） ====== */

const getSelfLoopPathD = (edge: DeviceEdge) => {
  return getSelfLoopD(edge, props.nodes)
}

// Check if there are bidirectional edges between two nodes
const hasBidirectionalEdges = (fromId: string, toId: string): boolean => {
  const forwardEdge = props.edges.some(e => e.from === fromId && e.to === toId)
  const backwardEdge = props.edges.some(e => e.from === toId && e.to === fromId)
  return forwardEdge && backwardEdge
}

// Get adjusted link points for bidirectional edges
const getAdjustedLinkPoints = (fromNode: DeviceNode | undefined, toNode: DeviceNode | undefined, edge: DeviceEdge) => {
  if (!fromNode || !toNode) {
    // Fallback to original positions if nodes not found
    return {
      fromPoint: edge.fromPos || { x: 0, y: 0 },
      toPoint: edge.toPos || { x: 0, y: 0 }
    }
  }

  const { fromPoint, toPoint } = getLinkPoints(fromNode, toNode)

  // If bidirectional, add offset to avoid overlap
  if (hasBidirectionalEdges(edge.from, edge.to)) {
    // Determine offset based on lexicographic order of node IDs
    // This ensures: A->B always gets same offset, B->A gets opposite
    const nodes = [edge.from, edge.to].sort()
    const isFirstDirection = (edge.from === nodes[0] && edge.to === nodes[1])
    const offset = isFirstDirection ? 25 : -25 // First lexicographic direction up, second down

    // Add perpendicular offset to the line (simple up/down offset)
    return {
      fromPoint: {
        x: fromPoint.x,
        y: fromPoint.y + offset
      },
      toPoint: {
        x: toPoint.x,
        y: toPoint.y + offset
      }
    }
  }

  return { fromPoint, toPoint }
}

type NodeVisualTier = 'compact' | 'expanded'

const relationSymbols: Record<string, string> = {
  EQ: '=',
  NEQ: '!=',
  GT: '>',
  GTE: '>=',
  LT: '<',
  LTE: '<=',
  in: 'in',
  not_in: 'not in',
  'not in': 'not in'
}

const getRelationSymbol = (relation?: string) =>
  relation ? (relationSymbols[relation] || relation) : ''

const hasValue = (value: unknown) =>
  value !== null && value !== undefined && String(value).trim() !== ''

const truncateCanvasText = (value: string, maxLength = 46) => {
  const normalized = String(value || '').trim()
  if (normalized.length <= maxLength) return normalized
  return `${normalized.slice(0, Math.max(0, maxLength - 1))}…`
}

const getNodeVisualTier = (node: DeviceNode): NodeVisualTier => {
  const screenWidth = node.width * props.zoom
  const screenHeight = node.height * props.zoom
  if (screenWidth < 128 || screenHeight < 98) return 'compact'
  return 'expanded'
}

const getNodeVisualTierClass = (node: DeviceNode) =>
  `device-node--${getNodeVisualTier(node)}`

const getNodeRuntimeBadges = (node: DeviceNode) => {
  const traceDevice = isTraceActive.value ? getLatestTraceDeviceForNode(node.id) : null
  const configuredVariables = node.variables || []
  const traceOnlyVariables = (traceDevice?.variables || [])
    .map(variable => ({
      name: variable.name,
      value: normalizeTraceComparable(variable.value),
      trust: variable.trust
    }))
  const candidates = isTraceActive.value ? traceOnlyVariables : configuredVariables

  return candidates
    .filter(variable =>
      hasValue(variable.value) ||
      (isTraceActive.value && getLatestTraceVariableValueForNode(node.id, variable.name) !== null)
    )
    .slice(0, 3)
    .map(variable => {
      const traceVariable = isTraceActive.value
        ? getLatestTraceVariableForNode(node.id, variable.name)
        : null
      const traceValue = isTraceActive.value
        ? (traceVariable ? normalizeTraceComparable(traceVariable.value) : null)
        : null
      const previousTraceValue = isTraceActive.value
        ? getPreviousTraceVariableValueForNode(node.id, variable.name)
        : null
      const value = traceValue ?? String(variable.value)
      const trust = traceVariable?.trust || variable.trust
      const trustLabel = trust === 'trusted' || trust === 'untrusted'
        ? t(`app.${trust}`)
        : ''
      const changed = traceValue !== null &&
        previousTraceValue !== null &&
        previousTraceValue !== traceValue
      return {
        label: variable.name,
        value,
        previousValue: changed ? previousTraceValue : null,
        trust,
        changed,
        title: `${variable.name}: ${value}${trustLabel ? ` (${trustLabel})` : ''}`
      }
    })
}

const getNodeSecurityBadges = (node: DeviceNode) => {
  if (isTraceActive.value) {
    const traceDevice = getLatestTraceDeviceForNode(node.id)
    if (!traceDevice) return []
    const facts = playbackDeviceSecurityFacts(traceDevice as Parameters<typeof playbackDeviceSecurityFacts>[0])
    const badges: Array<{ kind: 'trust' | 'privacy'; label: string; title: string }> = []
    if (facts.untrustedLabels.length > 0) {
      badges.push({
        kind: 'trust',
        label: t('app.traceVisualization.includesUntrustedSource'),
        title: t('app.traceVisualization.untrustedLabelDetails', { labels: facts.untrustedLabels.join(', ') })
      })
    } else if (facts.hasTrustLabels) {
      badges.push({
        kind: 'trust',
        label: t('app.traceVisualization.shownSourcesTrusted'),
        title: t('app.traceVisualization.shownSourcesTrustedDetails')
      })
    }
    if (facts.privateLabels.length > 0) {
      badges.push({
        kind: 'privacy',
        label: t('app.traceVisualization.includesPrivateData'),
        title: t('app.traceVisualization.privateLabelDetails', { labels: facts.privateLabels.join(', ') })
      })
    }
    return badges
  }

  const badges: Array<{ kind: 'trust' | 'privacy'; label: string; title: string }> = []
  if (node.currentStateTrust) {
    badges.push({
      kind: 'trust',
      label: t(`app.${node.currentStateTrust}`),
      title: t('app.stateTrust')
    })
  }
  const privateLabels = (node.privacies || [])
    .filter(entry => entry.privacy === 'private')
    .map(entry => entry.name)
  if (node.currentStatePrivacy === 'private') {
    privateLabels.unshift(t('app.currentStateProperty'))
  }
  if (privateLabels.length > 0) {
    badges.push({
      kind: 'privacy',
      label: t('app.traceVisualization.includesPrivateData'),
      title: t('app.traceVisualization.configuredPrivateLabelDetails', { labels: privateLabels.join(', ') })
    })
  }
  return badges
}

const isNodeTraceChanged = (node: DeviceNode) => {
  if (!isTraceActive.value) return false
  const current = getLatestTraceDeviceForNode(node.id)
  const previous = getPreviousTraceDeviceForNode(node.id)
  return Boolean(current && playbackDeviceChanged(current, previous))
}

const getNodeStateTitle = (node: DeviceNode) => {
  const current = getNodeState(node)
  const previous = getPreviousState(node)
  if (previous && previous !== getNodeState(node)) {
    return `${previous} -> ${getNodeState(node)}`
  }
  return current
}

const getFullEdgeLabel = (edge: DeviceEdge) => {
  const sourceName = edge.fromLabel || edge.from
  const targetName = edge.toLabel || edge.to
  const relation = getRelationSymbol(edge.relation)
  const sourceSignal = edge.fromApi || edge.itemType || t('app.condition')
  const condition = relation && hasValue(edge.value)
    ? `${sourceName}.${sourceSignal} ${relation} ${edge.value}`
    : `${sourceName}.${sourceSignal}`
  const action = edge.toApi ? `${targetName}.${edge.toApi}` : targetName
  return `${condition} -> ${action}`
}

const getEdgeLabelText = (edge: DeviceEdge) =>
  truncateCanvasText(getFullEdgeLabel(edge))

const getEdgeLabelWidth = (edge: DeviceEdge) => {
  const length = getEdgeLabelText(edge).length
  return Math.min(240, Math.max(76, length * 6 + 18))
}

const hoveredEdgeId = ref<string | null>(null)
const focusedEdgeId = ref<string | null>(null)

const shouldShowEdgeLabel = (edge: DeviceEdge) =>
  !isInternalVariableEdge(edge) &&
  (hoveredEdgeId.value === edge.id || focusedEdgeId.value === edge.id)

const setHoveredEdge = (edgeId: string | null) => {
  hoveredEdgeId.value = edgeId
}

const getEdgeLabelPoint = (edge: DeviceEdge) => {
  const fromNode = props.nodes.find(n => n.id === edge.from)
  const toNode = props.nodes.find(n => n.id === edge.to)
  if (edge.from === edge.to && fromNode) {
    return {
      x: fromNode.position.x + fromNode.width / 2,
      y: fromNode.position.y - 16
    }
  }
  const { fromPoint, toPoint } = getAdjustedLinkPoints(fromNode, toNode, edge)
  return {
    x: (fromPoint.x + toPoint.x) / 2,
    y: (fromPoint.y + toPoint.y) / 2 - 10
  }
}

const onNodeContextInternal = (node: DeviceNode, e: MouseEvent) => {
  e.preventDefault()
  e.stopPropagation()
  if (props.interactionLocked || isVariableNode(node)) return
  emit('node-context', node, { x: e.clientX, y: e.clientY })
}

const getNodeAriaLabel = (node: DeviceNode) => {
  const base = `${node.label}, ${node.templateName}, ${t('app.state')}: ${getNodeState(node)}`
  return isTraceActive.value && !isNodeRepresentedInTrace(node)
    ? `${base}. ${t('app.traceVisualization.currentBoardDeviceNotRepresented')}`
    : base
}

const moveNodeByKeyboard = (node: DeviceNode, dx: number, dy: number) => {
  node.position.x += dx
  node.position.y += dy
  updateEdgesForNode(node.id, props.nodes, props.edges)
  emit('node-moved-or-resized', node.id)
}

const onNodeKeydown = (event: KeyboardEvent, node: DeviceNode) => {
  if (event.key === 'Enter' || event.key === ' ') {
    event.preventDefault()
    if (props.interactionLocked) return
    emit('node-open', node)
    return
  }

  if (event.key === 'Delete' || event.key === 'Backspace') {
    event.preventDefault()
    if (props.interactionLocked) return
    if (isVariableNode(node)) return
    emit('node-delete', node.id)
    return
  }

  if (event.key === 'ContextMenu' || (event.shiftKey && event.key === 'F10')) {
    event.preventDefault()
    if (props.interactionLocked) return
    const element = event.currentTarget as HTMLElement | null
    const rect = element?.getBoundingClientRect()
    emit('node-context', node, {
      x: rect ? rect.left + rect.width / 2 : 0,
      y: rect ? rect.top + rect.height / 2 : 0
    })
    return
  }

  const step = event.shiftKey ? 1 : 10
  const movement: Record<string, { dx: number; dy: number }> = {
    ArrowUp: { dx: 0, dy: -step },
    ArrowDown: { dx: 0, dy: step },
    ArrowLeft: { dx: -step, dy: 0 },
    ArrowRight: { dx: step, dy: 0 }
  }
  const delta = movement[event.key]
  if (!delta || event.repeat) return
  event.preventDefault()
  if (props.interactionLocked) return
  moveNodeByKeyboard(node, delta.dx, delta.dy)
}

/* ====== 生命周期清理 ====== */

// Run test on component mount
onMounted(() => {
  testColorDistribution()
})

onBeforeUnmount(() => {
  if (nodeAnimationResetTimer) clearTimeout(nodeAnimationResetTimer)
  window.removeEventListener('pointermove', onNodePointerMove)
  window.removeEventListener('pointerup', onNodePointerUp)
  window.removeEventListener('pointermove', onPointerMoveResize)
  window.removeEventListener('pointerup', onPointerUpResize)
})
</script>

<template>
  <div
      class="canvas"
      data-testid="canvas-board"
      :style="canvasGridStyle"
      @pointerdown="(e: PointerEvent) => emit('canvas-pointerdown', e)"
      @dragover.prevent="(e: DragEvent) => emit('canvas-dragover', e)"
      @drop.prevent="(e: DragEvent) => emit('canvas-drop', e)"
      @mouseenter="() => emit('canvas-enter')"
      @mouseleave="() => emit('canvas-leave')"
      @wheel="(e: WheelEvent) => emit('canvas-wheel', e)"
  >
    <div
        class="canvas-inner"
        :style="{
        transform: `translate(${pan.x}px, ${pan.y}px) scale(${zoom})`,
        transformOrigin: '0 0'
      }"
    >
      <!-- 连线层 -->
      <svg class="edge-layer">

        <defs>
          <!-- Glow filter for particle effect -->
          <filter id="glow">
            <feGaussianBlur result="coloredBlur" stdDeviation="2"></feGaussianBlur>
            <feMerge>
              <feMergeNode in="coloredBlur"></feMergeNode>
              <feMergeNode in="SourceGraphic"></feMergeNode>
            </feMerge>
          </filter>

          <!-- Gradient definitions -->
          <linearGradient id="grad-blue" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:#3B82F6;stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:#3B82F6;stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:#3B82F6;stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-purple" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:#C026D3;stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:#C026D3;stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:#C026D3;stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-green" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:#059669;stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:#059669;stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:#059669;stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-orange" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:#dc2626;stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:#dc2626;stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:#dc2626;stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-red" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:#ef4444;stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:#ef4444;stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:#ef4444;stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-teal" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:#14b8a6;stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:#14b8a6;stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:#14b8a6;stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-pink" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:#ec4899;stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:#ec4899;stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:#ec4899;stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-yellow" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:#eab308;stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:#eab308;stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:#eab308;stop-opacity:0.2"></stop>
          </linearGradient>

          <!-- Arrow markers for different colors -->
          <marker id="arrow-blue" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="#2563EB"></path>
          </marker>
          <marker id="arrow-green" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="#059669"></path>
          </marker>
          <marker id="arrow-purple" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="#C026D3"></path>
          </marker>
          <marker id="arrow-orange" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="#dc2626"></path>
          </marker>
          <marker id="arrow-red" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="#ef4444"></path>
          </marker>
          <marker id="arrow-teal" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="#14b8a6"></path>
          </marker>
          <marker id="arrow-pink" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="#ec4899"></path>
          </marker>
          <marker id="arrow-yellow" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="#eab308"></path>
          </marker>
        </defs>

        <g
            v-for="(edge, index) in edges"
            :key="edge.id"
            @pointerenter="setHoveredEdge(edge.id)"
            @pointerleave="setHoveredEdge(null)"
        >
          <!-- Base lines removed - only showing particle effects -->
          <path
              v-if="edge.from === edge.to"
              class="edge-base-line"
              :class="getEdgePlaybackClass(edge)"
              :d="getSelfLoopPathD(edge)"
              fill="none"
              :stroke="getParticleColorByEdge(edge)"
              :stroke-dasharray="isInternalVariableEdge(edge) ? '6,6' : ''"
              :marker-end="getArrowMarker(edge)"
          />
          <line
              v-else
              class="edge-base-line"
              :class="getEdgePlaybackClass(edge)"
              :x1="getAdjustedLinkPoints(
                props.nodes.find(n => n.id === edge.from),
                props.nodes.find(n => n.id === edge.to),
                edge
              ).fromPoint.x"
              :y1="getAdjustedLinkPoints(
                props.nodes.find(n => n.id === edge.from),
                props.nodes.find(n => n.id === edge.to),
                edge
              ).fromPoint.y"
              :x2="getAdjustedLinkPoints(
                props.nodes.find(n => n.id === edge.from),
                props.nodes.find(n => n.id === edge.to),
                edge
              ).toPoint.x"
              :y2="getAdjustedLinkPoints(
                props.nodes.find(n => n.id === edge.from),
                props.nodes.find(n => n.id === edge.to),
                edge
              ).toPoint.y"
              fill="none"
              :stroke="getParticleColorByEdge(edge)"
              :stroke-dasharray="isInternalVariableEdge(edge) ? '6,6' : ''"
              :marker-end="getArrowMarker(edge)"
          />

          <path
              v-if="edge.from === edge.to"
              class="edge-hitarea"
              :data-rule-id="edge.ruleId || undefined"
              :d="getSelfLoopPathD(edge)"
              role="img"
              tabindex="0"
              :aria-label="getFullEdgeLabel(edge)"
              @pointerenter="setHoveredEdge(edge.id)"
              @pointerleave="setHoveredEdge(null)"
              @focus="focusedEdgeId = edge.id"
              @blur="focusedEdgeId = null"
          />
          <line
              v-else
              class="edge-hitarea"
              :data-rule-id="edge.ruleId || undefined"
              role="img"
              tabindex="0"
              :aria-label="getFullEdgeLabel(edge)"
              :x1="getAdjustedLinkPoints(
                props.nodes.find(n => n.id === edge.from),
                props.nodes.find(n => n.id === edge.to),
                edge
              ).fromPoint.x"
              :y1="getAdjustedLinkPoints(
                props.nodes.find(n => n.id === edge.from),
                props.nodes.find(n => n.id === edge.to),
                edge
              ).fromPoint.y"
              :x2="getAdjustedLinkPoints(
                props.nodes.find(n => n.id === edge.from),
                props.nodes.find(n => n.id === edge.to),
                edge
              ).toPoint.x"
              :y2="getAdjustedLinkPoints(
                props.nodes.find(n => n.id === edge.from),
                props.nodes.find(n => n.id === edge.to),
                edge
              ).toPoint.y"
              @pointerenter="setHoveredEdge(edge.id)"
              @pointerleave="setHoveredEdge(null)"
              @focus="focusedEdgeId = edge.id"
              @blur="focusedEdgeId = null"
          />

          <!-- During model playback, motion represents a backend-reported delivered automation. -->
          <path
              v-if="edge.from === edge.to && shouldAnimateEdgeFlow(edge, props.highlightedTrace)"
              :key="`edge-flow-loop-${edge.id}-${props.highlightedTrace?.selectedStateIndex ?? -1}`"
              class="edge-line particle-line"
              :data-playback-state="props.highlightedTrace?.selectedStateIndex"
              :class="[getParticleOpacity(index), getEdgePlaybackClass(edge)]"
              :d="getSelfLoopPathD(edge)"
              fill="none"
              filter="url(#glow)"
              :stroke="getParticleColorByEdge(edge)"
              stroke-width="2"
              :stroke-dasharray="isInternalVariableEdge(edge) ? '5,5' : ''"
              :marker-end="getArrowMarker(edge)"
          />
          <line
              v-else-if="shouldAnimateEdgeFlow(edge, props.highlightedTrace)"
              :key="`edge-flow-line-${edge.id}-${props.highlightedTrace?.selectedStateIndex ?? -1}`"
              class="edge-line particle-line"
              :data-playback-state="props.highlightedTrace?.selectedStateIndex"
              :class="[getParticleOpacity(index), getEdgePlaybackClass(edge)]"
              :x1="getAdjustedLinkPoints(
                props.nodes.find(n => n.id === edge.from),
                props.nodes.find(n => n.id === edge.to),
                edge
              ).fromPoint.x"
              :y1="getAdjustedLinkPoints(
                props.nodes.find(n => n.id === edge.from),
                props.nodes.find(n => n.id === edge.to),
                edge
              ).fromPoint.y"
              :x2="getAdjustedLinkPoints(
                props.nodes.find(n => n.id === edge.from),
                props.nodes.find(n => n.id === edge.to),
                edge
              ).toPoint.x"
              :y2="getAdjustedLinkPoints(
                props.nodes.find(n => n.id === edge.from),
                props.nodes.find(n => n.id === edge.to),
                edge
              ).toPoint.y"
              fill="none"
              filter="url(#glow)"
              :stroke="getParticleColorByEdge(edge)"
              stroke-width="2"
              :stroke-dasharray="isInternalVariableEdge(edge) ? '5,5' : ''"
              :marker-end="getArrowMarker(edge)"
          />

          <!-- A compromised or idle automation remains visible as a static edge. -->
          <circle
              v-if="edge.from !== edge.to && shouldAnimateEdgeFlow(edge, props.highlightedTrace)"
              :key="`edge-flow-particle-${edge.id}-${props.highlightedTrace?.selectedStateIndex ?? -1}`"
              class="trace-flow-particle"
              :data-playback-state="props.highlightedTrace?.selectedStateIndex"
              :fill="getParticleFillColor(edge)"
              filter="url(#glow)"
              :r="getParticleSize(index)"
          >
            <animateMotion
                :dur="TRACE_FLOW_DURATION"
                :path="`M ${getAdjustedLinkPoints(
                  props.nodes.find(n => n.id === edge.from),
                  props.nodes.find(n => n.id === edge.to),
                  edge
                ).fromPoint.x} ${getAdjustedLinkPoints(
                  props.nodes.find(n => n.id === edge.from),
                  props.nodes.find(n => n.id === edge.to),
                  edge
                ).fromPoint.y} L ${getAdjustedLinkPoints(
                  props.nodes.find(n => n.id === edge.from),
                  props.nodes.find(n => n.id === edge.to),
                  edge
                ).toPoint.x} ${getAdjustedLinkPoints(
                  props.nodes.find(n => n.id === edge.from),
                  props.nodes.find(n => n.id === edge.to),
                  edge
                ).toPoint.y}`"
                repeatCount="1"
                fill="freeze"
            />
            <animate
                attributeName="opacity"
                values="0;1;1;0"
                keyTimes="0;0.12;0.8;1"
                :dur="TRACE_FLOW_DURATION"
                repeatCount="1"
                fill="freeze"
            />
          </circle>
          <g
              v-if="shouldShowEdgeLabel(edge)"
              class="edge-label"
              :transform="`translate(${getEdgeLabelPoint(edge).x} ${getEdgeLabelPoint(edge).y})`"
          >
            <title>{{ getFullEdgeLabel(edge) }}</title>
            <rect
                class="edge-label__bg"
                :x="-getEdgeLabelWidth(edge) / 2"
                y="-10"
                :width="getEdgeLabelWidth(edge)"
                height="20"
                rx="10"
            />
            <text class="edge-label__text" text-anchor="middle" dominant-baseline="middle">
              {{ getEdgeLabelText(edge) }}
            </text>
          </g>
          <!-- For self-loops, we could add a different animation -->
        </g>
      </svg>

      <!-- 设备节点 -->
      <div
          v-for="node in nodes"
          :key="node.id"
          :data-node-id="node.id"
          class="device-node"
          tabindex="0"
          role="button"
          :aria-disabled="interactionLocked ? 'true' : undefined"
          :aria-label="getNodeAriaLabel(node)"
          :title="isTraceActive && !isNodeRepresentedInTrace(node) ? t('app.traceVisualization.currentBoardDeviceNotRepresented') : undefined"
          :class="[getNodeBgColorClass(node.id), getNodeColorClass(node.id), getNodeVisualTierClass(node), { 'variable-node': isVariableNode(node) }, { 'trace-active': isNodeInTrace(node) }, { 'trace-not-represented': isTraceActive && !isNodeRepresentedInTrace(node) }, { 'trace-changed': isNodeTraceChanged(node) }, { 'trace-change-pulse': shouldAnimateTraceChange(node) }, { 'device-attacked': isDeviceAttacked(node.id) }, { 'node-focused': props.focusedNodeId === node.id }, { 'cursor-default': interactionLocked }]"
          :style="{
          left: node.position.x + 'px',
          top: node.position.y + 'px',
          width: node.width + 'px',
          height: node.height + 'px',
          backgroundColor: isVariableNode(node) ? getVariableNodeBgColor(node) : getNodeBgColor(node.id),
          borderColor: isDeviceAttacked(node.id) ? '#EF4444' : (isVariableNode(node) ? getVariableNodeBorderColor(node) : getNodeBorderColor(node.id)),
          ...(isNodeInTrace(node) ? { '--trace-glow-color': isDeviceAttacked(node.id) ? '#EF4444' : (isVariableNode(node) ? getVariableNodeBorderColor(node) : getNodeBorderColor(node.id)) } : {})
        }"
          @pointerdown.stop="onNodePointerDown($event, node)"
          @contextmenu.stop.prevent="onNodeContextInternal(node, $event)"
          @keydown="onNodeKeydown($event, node)"
      >
        <!-- Non-authoritative variable row fallback: icon-only circle -->
        <div v-if="isVariableNode(node)" class="variable-node-wrapper">
          <div class="variable-node-content">
            <img
                class="variable-img"
                :src="getCurrentNodeIcon(node)"
                :alt="node.label"
                draggable="false"
                @error="handleImageError($event)"
                :class="{ 'variable-changed': isTraceActive && getTraceVariableValue(node) }"
            />
          </div>
          <!-- 自定义悬浮提示 - 反例路径时一直显示 -->
          <div 
            class="variable-tooltip" 
            :class="{ 'variable-tooltip-active': isTraceActive }"
          >
            <div class="variable-tooltip-icon">
              <img
                  :src="getCurrentNodeIcon(node)"
                  :alt="node.label"
                  @error="handleImageError($event)"
              />
            </div>
            <div class="variable-tooltip-info">
              <span class="variable-tooltip-label">{{ node.label }}</span>
              <span v-if="isTraceActive && getTraceVariableValue(node)" class="variable-tooltip-value">
                {{ t('app.variableValue') }}: {{ getTraceVariableValue(node)?.value }}
              </span>
            </div>
          </div>
        </div>

        <!-- 普通设备节点：图标+名字+状态 -->
        <div v-else class="device-node-content">
          <!-- Attack indicator arrow -->
          <div 
            v-if="isDeviceAttacked(node.id)"
            class="attack-indicator"
            :title="t('app.deviceUnderAttack')"
          >
            <span class="material-symbols-outlined">arrow_downward</span>
            <span>{{ t('app.attacked') }}</span>
          </div>
          <!-- 上部分：图标 -->
          <div class="device-top-row">
            <Transition name="trace-device-icon">
              <img
                  :key="getNodeVisualStateKey(node)"
                  class="device-img"
                  :src="getCurrentNodeIcon(node)"
                  :alt="node.label"
                  draggable="false"
                  @error="handleImageError($event)"
              />
            </Transition>
          </div>
          <!-- 名字 -->
          <div class="device-label-wrapper">
            <div class="device-label" :style="getNodeLabelStyle(node)" :title="node.label">
              {{ node.label }}
            </div>
          </div>
          <!-- 下部分：设备状态显示 -->
          <div class="device-state" :class="getStateDisplayClass(node)" :title="getNodeStateTitle(node)">
            <span class="device-state-dot"></span>
            <Transition name="trace-device-state" mode="out-in">
              <span :key="getNodeVisualStateKey(node)" class="device-state-value">{{ getNodeState(node) }}</span>
            </Transition>
          </div>
          <div v-if="getNodeRuntimeBadges(node).length > 0" class="device-runtime-strip">
            <span
                v-for="badge in getNodeRuntimeBadges(node)"
                :key="badge.label"
                class="device-runtime-chip"
                :class="{ 'device-runtime-chip--changed': badge.changed }"
                :title="badge.title"
            >
              <span class="device-runtime-chip__label">{{ badge.label }}</span>
              <span class="device-runtime-chip__value">{{ badge.value }}</span>
            </span>
          </div>
          <div v-if="getNodeSecurityBadges(node).length > 0" class="device-node-actions">
            <span
              v-for="badge in getNodeSecurityBadges(node)"
              :key="badge.kind"
              class="device-node-trust"
              :class="`device-node-trust--${badge.kind}`"
              :title="badge.title"
            >
              {{ badge.label }}
            </span>
          </div>
        </div>

        <!-- 四角缩放手柄 -->
        <div
            v-if="!interactionLocked"
            class="resize-handle tl"
            @pointerdown.stop="onPointerDownResize($event, node, 'tl')"
        ></div>
        <div
            v-if="!interactionLocked"
            class="resize-handle tr"
            @pointerdown.stop="onPointerDownResize($event, node, 'tr')"
        ></div>
        <div
            v-if="!interactionLocked"
            class="resize-handle bl"
            @pointerdown.stop="onPointerDownResize($event, node, 'bl')"
        ></div>
        <div
            v-if="!interactionLocked"
            class="resize-handle br"
            @pointerdown.stop="onPointerDownResize($event, node, 'br')"
        ></div>
      </div>
    </div>
  </div>
</template>

<style scoped>
.edge-hitarea {
  fill: none;
  stroke: transparent;
  stroke-width: 18;
  stroke-linecap: round;
  pointer-events: stroke;
  cursor: help;
}

.edge-hitarea:focus-visible {
  outline: none;
  stroke: color-mix(in srgb, var(--iot-color-accent, #2563eb) 18%, transparent);
}

.edge-base-line,
.edge-line,
.edge-layer circle {
  pointer-events: none;
}

.edge-label {
  pointer-events: none;
  filter: drop-shadow(0 3px 8px rgba(15, 23, 42, 0.18));
}

.edge-label__bg {
  fill: color-mix(in srgb, var(--surface-elevated, #ffffff) 92%, transparent);
  stroke: color-mix(in srgb, var(--border, #cbd5e1) 88%, transparent);
  stroke-width: 1;
}

.edge-label__text {
  fill: var(--text, #0f172a);
  font-size: 10px;
  font-weight: 700;
  letter-spacing: 0;
}

/* Attack indicator - longer arrow with text */
.attack-indicator {
  position: absolute;
  top: -32px;
  left: 50%;
  transform: translateX(-50%);
  background: linear-gradient(135deg, #EF4444 0%, #DC2626 100%);
  color: white;
  padding: 3px 8px;
  border-radius: 12px;
  display: flex;
  align-items: center;
  justify-content: center;
  box-shadow: 0 2px 8px rgba(239, 68, 68, 0.5);
  z-index: 20;
  animation: attackBounce 0.8s ease-in-out infinite;
  white-space: nowrap;
  font-size: 9px;
  font-weight: bold;
  gap: 3px;
  height: auto;
  width: auto;
  min-width: 50px;
}

.attack-indicator .material-symbols-outlined {
  font-size: 14px;
}

@keyframes attackBounce {
  0%, 100% {
    transform: translateX(-50%) translateY(0);
  }
  50% {
    transform: translateX(-50%) translateY(-3px);
  }
}

.device-state {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 4px;
  justify-self: center;
  min-width: 0;
  min-height: 1.25rem;
  width: min(78%, 9rem);
  padding: 3px clamp(6px, 6%, 10px);
  border-radius: 12px;
  font-size: 10px;
  font-weight: 600;
  z-index: 5;
  box-sizing: border-box;
  box-shadow: 0 1px 3px rgba(0, 0, 0, 0.1);
  line-height: 1;
  overflow: hidden;
}

.device-node--expanded .device-state {
  grid-area: state;
  justify-self: start;
  width: min(100%, 9.5rem);
  min-height: 1.35rem;
  padding: 4px 8px;
  border-radius: 999px;
}

.device-state-dot {
  width: 6px;
  height: 6px;
  border-radius: 50%;
  flex-shrink: 0;
  display: inline-block;
}

.device-state-value {
  min-width: 0;
  max-width: 100%;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
  font-size: 10px;
  line-height: 1;
}

.state-offline {
  background: linear-gradient(135deg, rgba(148, 163, 184, 0.2) 0%, rgba(100, 116, 139, 0.15) 100%);
  color: #475569;
  border: 1px solid rgba(148, 163, 184, 0.3);
}

.state-offline .device-state-dot {
  background: #94A3B8;
  box-shadow: 0 0 4px #94A3B8;
}

.state-online {
  background: linear-gradient(135deg, rgba(34, 197, 94, 0.2) 0%, rgba(16, 185, 129, 0.15) 100%);
  color: #059669;
  border: 1px solid rgba(34, 197, 94, 0.3);
}

.state-online .device-state-dot {
  background: #22C55E;
  box-shadow: 0 0 5px #22C55E;
  animation: pulse-green 2s infinite;
}

.state-active {
  background: linear-gradient(135deg, rgba(59, 130, 246, 0.2) 0%, rgba(37, 99, 235, 0.15) 100%);
  color: #2563EB;
  border: 1px solid rgba(59, 130, 246, 0.3);
}

.state-active .device-state-dot {
  background: #3B82F6;
  box-shadow: 0 0 5px #3B82F6;
  animation: pulse-blue 1.5s infinite;
}

/* Playback motion identifies a transition, not a device that merely remains on. */
.device-node.trace-active .device-state-dot {
  animation: none;
}

.state-default {
  background: linear-gradient(135deg, rgba(148, 163, 184, 0.15) 0%, rgba(100, 116, 139, 0.1) 100%);
  color: #64748B;
  border: 1px solid rgba(148, 163, 184, 0.2);
}

.state-default .device-state-dot {
  background: #94A3B8;
}

@keyframes pulse-green {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.5; }
}

@keyframes pulse-blue {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.6; }
}

@media (prefers-reduced-motion: reduce) {
  .device-state-dot {
    animation: none !important;
  }
}

.trace-info-card {
  position: absolute;
  bottom: -4px;
  left: 50%;
  transform: translateX(-50%);
  width: 90%;
  padding: 4px 6px;
  border-radius: 6px;
  font-size: 10px;
  box-shadow: 0 2px 8px rgba(0, 0, 0, 0.15);
  z-index: 10;
}

.trace-info-card.violated {
  background: linear-gradient(135deg, #fef2f2 0%, #fee2e2 100%);
  border: 1px solid #fca5a5;
}

.trace-info-card.intermediate {
  background: linear-gradient(135deg, #fefce8 0%, #fef9c3 100%);
  border: 1px solid #fde047;
}

.trace-state-row {
  display: flex;
  align-items: center;
  gap: 4px;
  margin-bottom: 3px;
}

.trace-state-dot {
  width: 6px;
  height: 6px;
  border-radius: 50%;
}

.violated .trace-state-dot {
  background-color: #ef4444;
  box-shadow: 0 0 4px #ef4444;
  animation: pulse-red 1s infinite;
}

.intermediate .trace-state-dot {
  background-color: #f59e0b;
  box-shadow: 0 0 4px #f59e0b;
  animation: pulse-amber 1s infinite;
}

@keyframes pulse-red {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.5; }
}

@keyframes pulse-amber {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.6; }
}

.trace-state-label {
  color: #6b7280;
  font-weight: 500;
}

.trace-state-value {
  font-weight: bold;
}

.violated .trace-state-value {
  color: #dc2626;
}

.intermediate .trace-state-value {
  color: #d97706;
}

.trace-variables-list {
  display: flex;
  flex-direction: column;
  gap: 2px;
  padding-top: 3px;
  border-top: 1px dashed;
}

.violated .trace-variables-list {
  border-color: #fecaca;
}

.intermediate .trace-variables-list {
  border-color: #fde047;
}

.trace-variable-item {
  display: flex;
  justify-content: space-between;
  align-items: center;
}

.trace-var-name {
  color: #4b5563;
  font-size: 9px;
}

.trace-var-value {
  font-weight: bold;
  color: #1f2937;
  font-size: 10px;
}

/* Device content keeps a stable footprint while trace values cross-fade. */
.device-node-content {
  display: grid;
  grid-template-rows: minmax(0, 1fr) auto auto;
  align-items: center;
  justify-items: center;
  width: 100%;
  height: 100%;
  min-width: 0;
  min-height: 0;
  gap: clamp(0.15rem, 3%, 0.35rem);
  transition: transform 0.28s cubic-bezier(0.22, 1, 0.36, 1);
}

.device-top-row {
  position: relative;
}

.trace-device-icon-enter-active,
.trace-device-icon-leave-active {
  position: absolute;
  transition:
    opacity 0.24s ease,
    transform 0.38s cubic-bezier(0.22, 1, 0.36, 1),
    filter 0.3s ease;
}

.trace-device-icon-enter-from {
  opacity: 0;
  transform: translateY(5px) scale(0.9);
  filter: blur(2px);
}

.trace-device-icon-leave-to {
  opacity: 0;
  transform: translateY(-4px) scale(0.96);
  filter: blur(1px);
}

.trace-device-state-enter-active,
.trace-device-state-leave-active {
  transition: opacity 0.16s ease, transform 0.2s cubic-bezier(0.22, 1, 0.36, 1);
}

.trace-device-state-enter-from {
  opacity: 0;
  transform: translateY(3px);
}

.trace-device-state-leave-to {
  opacity: 0;
  transform: translateY(-2px);
}

@media (prefers-reduced-motion: reduce) {
  .trace-device-icon-enter-active,
  .trace-device-icon-leave-active,
  .trace-device-state-enter-active,
  .trace-device-state-leave-active {
    transition: none;
  }
}
</style>

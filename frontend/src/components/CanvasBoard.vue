<script setup lang="ts">
import { computed, nextTick, onBeforeUnmount, onMounted, ref, watch } from 'vue'
import { useI18n } from 'vue-i18n'

import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { CanvasPan } from '../types/canvas'
import type { ModelTokenSource } from '../types/modelToken'

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
  type TraceDeviceLike,
  type TraceVariableLike
} from '../utils/traceEdgePlayback'
import {
  formatPlaybackSecurityLabel,
  isDeviceRepresentedInPlayback,
  playbackDeviceChanged,
  playbackDeviceSecurityFacts
} from '../utils/traceView'

const { t } = useI18n()

import {
  createNodeDragState,
  beginNodeDrag,
  cancelNodeDrag,
  updateNodeDrag,
  endNodeDrag
} from '../utils/canvas/nodeDrag'

import {
  createNodeResizeState,
  beginNodeResize,
  cancelNodeResize,
  updateNodeResize,
  endNodeResize,
  NODE_HEIGHT_RANGE,
  NODE_WIDTH_RANGE
} from '../utils/canvas/nodeResize'
import {
  getNodeAccentColor,
  getNodeBorderColor,
  getNodeColorIndex,
  getNodeSurfaceColor
} from '../utils/canvas/nodePalette'
import { estimateCanvasTextWidth, truncateCanvasTextToWidth } from '../utils/canvas/canvasText'

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
const NODE_DRAG_THRESHOLD_PX = 5

const prefersReducedMotion = ref(false)
let reducedMotionQuery: MediaQueryList | null = null

const syncReducedMotionPreference = () => {
  prefersReducedMotion.value = reducedMotionQuery?.matches === true
}

const shouldRenderEdgeFlow = (edge: DeviceEdge) =>
  !prefersReducedMotion.value && shouldAnimateEdgeFlow(edge, props.edges, props.highlightedTrace)

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
  return sourceNode ? getNodeAccentColor(sourceNode.id) : 'var(--iot-node-accent-0)'
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
  return props.getNodeEffectiveState(node)
}

const hasDisplayStateMachine = (node: DeviceNode): boolean => {
  if (!isTraceActive.value) return props.hasNodeStateMachine(node)
  const traceDevice = getLatestTraceDeviceForNode(node.id)
  if (!traceDevice) return true
  return Boolean(traceDevice.mode?.trim() || traceDevice.state?.trim())
}

const getNodeDisplayState = (node: DeviceNode): string => {
  if (!hasDisplayStateMachine(node)) return t('app.noStateMachine')
  const state = getNodeState(node)
  if (!isTraceActive.value) return formatNodeModelToken(node, state)
  const traceDevice = getLatestTraceDeviceForNode(node.id)
  return traceDevice ? formatPlaybackModelToken(traceDevice.modelTokenSource, state) : state
}

const getStateDisplayClass = (node: DeviceNode): string =>
  hasDisplayStateMachine(node) ? 'state-defined' : 'state-stateless'

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

type PlaybackTraceVariable = TraceVariableLike & {
  modelTokenSource?: ModelTokenSource | null
}

type PlaybackTraceDevice = Omit<TraceDeviceLike, 'variables'> & {
  modelTokenSource?: ModelTokenSource | null
  variables?: PlaybackTraceVariable[]
}

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
  /** Whether this template has a modelled state machine. */
  hasNodeStateMachine: (node: DeviceNode) => boolean
  /** Resolve the current persisted state against the template's legal states. */
  getNodeEffectiveState: (node: DeviceNode) => string
  /** Localize canonical bundled-template identifiers without changing stored values. */
  formatNodeModelToken?: (node: DeviceNode, value: unknown) => string
  /** Format an immutable playback token strictly from its frozen source. */
  formatPlaybackModelToken?: (source: ModelTokenSource | null | undefined, value: unknown) => string
  /** 高亮显示的反例路径 */
  highlightedTrace?: {
    states: Array<{
      stateIndex?: number
      devices: PlaybackTraceDevice[]
      envVariables?: PlaybackTraceVariable[]
      rules?: number[]
      triggeredRules?: Array<{ ruleIndex: number; ruleId?: string | null; ruleLabel?: string | null }>
      compromisedAutomationLinks?: Array<{ ruleIndex: number; ruleId?: string | null; ruleLabel?: string | null }>
    }>
    selectedStateIndex?: number
  } | null
  focusedNodeId?: string | null
  focusedRuleId?: string | null
  /** Model playback is a saved snapshot; prevent canvas mutations while it is visible. */
  interactionLocked?: boolean
}>()

function formatNodeModelToken(node: DeviceNode, value: unknown): string {
  return props.formatNodeModelToken?.(node, value) ?? String(value ?? '')
}

function formatPlaybackModelToken(
  source: ModelTokenSource | null | undefined,
  value: unknown
): string {
  return props.formatPlaybackModelToken?.(source, value) ?? String(value ?? '')
}

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
  ) as PlaybackTraceVariable | null
}

const getPreviousTraceVariableForNode = (
  nodeId: string,
  variableName: string
): PlaybackTraceVariable | null => {
  if (!props.highlightedTrace?.states || props.highlightedTrace.selectedStateIndex === undefined) return null
  if (props.highlightedTrace.selectedStateIndex <= 0) return null
  return findTraceVariableAtOrBefore(
    props.highlightedTrace,
    nodeId,
    variableName,
    props.highlightedTrace.selectedStateIndex - 1
  ) as PlaybackTraceVariable | null
}

const getLatestTraceDeviceForNodeAtOrBefore = (nodeId: string, endIndex: number): PlaybackTraceDevice | null => {
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

const getLatestTraceDeviceForNode = (nodeId: string): PlaybackTraceDevice | null =>
  getLatestTraceDeviceForNodeAtOrBefore(nodeId, props.highlightedTrace?.selectedStateIndex || 0)

const getPreviousTraceDeviceForNode = (nodeId: string): PlaybackTraceDevice | null => {
  const selectedIndex = props.highlightedTrace?.selectedStateIndex
  if (selectedIndex === undefined || selectedIndex <= 0) return null
  return getLatestTraceDeviceForNodeAtOrBefore(nodeId, selectedIndex - 1)
}

const getEdgePlaybackClass = (edge: DeviceEdge) => {
  const traceActive = isEdgeActiveInTrace(edge, props.edges, props.highlightedTrace)
  const linkCompromised = isEdgeCompromisedInTrace(edge, props.edges, props.highlightedTrace)
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
  /** Keep server snapshots from replacing a node while a pointer interaction owns it. */
  (e: 'node-layout-interaction-start', nodeId: string): void
  (e: 'node-layout-interaction-end', nodeId: string): void
}>()

/* ====== 节点拖拽状态 ====== */

const dragState = createNodeDragState()
let activeDragPointerId: number | null = null
let activeDragTarget: HTMLElement | null = null
let activeDragNodeId: string | null = null
let activeDragStartPoint: { x: number; y: number } | null = null
let activeDragMoved = false

const removeDragListeners = () => {
  window.removeEventListener('pointermove', onNodePointerMove)
  window.removeEventListener('pointerup', onNodePointerUp)
  window.removeEventListener('pointercancel', onNodePointerCancel)
}

const releaseDragPointer = () => {
  const target = activeDragTarget
  const pointerId = activeDragPointerId
  const nodeId = activeDragNodeId
  activeDragPointerId = null
  activeDragTarget = null
  activeDragNodeId = null
  activeDragStartPoint = null
  activeDragMoved = false
  target?.removeEventListener('lostpointercapture', onNodeLostPointerCapture)
  if (target && pointerId !== null) {
    try {
      target.releasePointerCapture(pointerId)
    } catch {
      // The browser may release capture before pointerup/cancel reaches the window.
    }
  }
  removeDragListeners()
  if (nodeId) emit('node-layout-interaction-end', nodeId)
}

const onNodeLostPointerCapture = (e: PointerEvent) => {
  if (e.pointerId !== activeDragPointerId) return
  const restored = cancelNodeDrag(dragState)
  if (restored) updateEdgesForNode(restored.id, props.nodes, props.edges)
  releaseDragPointer()
}

const onNodePointerDown = (e: PointerEvent, node: DeviceNode) => {
  e.preventDefault()
  if (e.button !== 0 || e.isPrimary === false || activeDragPointerId !== null) {
    return
  }
  if (props.interactionLocked) {
    return
  }
  // 只处理节点自身拖拽，不影响画布平移（事件在模板里用了 .stop）
  beginNodeDrag(e, node, dragState)
  activeDragPointerId = e.pointerId
  activeDragTarget = e.currentTarget as HTMLElement
  activeDragNodeId = node.id
  activeDragStartPoint = { x: e.clientX, y: e.clientY }
  activeDragMoved = false
  emit('node-layout-interaction-start', node.id)
  activeDragTarget.focus({ preventScroll: true })
  try {
    activeDragTarget.setPointerCapture?.(e.pointerId)
  } catch {
    // Pointer capture is an enhancement; window listeners still complete the drag.
  }
  activeDragTarget.addEventListener('lostpointercapture', onNodeLostPointerCapture)
  window.addEventListener('pointermove', onNodePointerMove)
  window.addEventListener('pointerup', onNodePointerUp)
  window.addEventListener('pointercancel', onNodePointerCancel)
}

const onNodePointerMove = (e: PointerEvent) => {
  if (e.pointerId !== activeDragPointerId) return
  if (!activeDragMoved && activeDragStartPoint) {
    const distance = Math.hypot(
      e.clientX - activeDragStartPoint.x,
      e.clientY - activeDragStartPoint.y
    )
    if (distance < NODE_DRAG_THRESHOLD_PX) return
    activeDragMoved = true
  }
  const changed = updateNodeDrag(e, dragState, props.zoom)
  if (!changed || !dragState.node) return

  // 节点位置变了，更新相关边几何
  updateEdgesForNode(dragState.node.id, props.nodes, props.edges)
}

const onNodePointerUp = (e: PointerEvent) => {
  if (e.pointerId !== activeDragPointerId) return
  const movedEnough = activeDragMoved
  const moved = endNodeDrag(dragState)
  if (moved) {
    if (movedEnough) {
      emit('node-moved-or-resized', moved.id)
    } else {
      emit('node-open', moved)
    }
  }
  releaseDragPointer()
}

const onNodePointerCancel = (e: PointerEvent) => {
  if (e.pointerId !== activeDragPointerId) return
  const restored = cancelNodeDrag(dragState)
  if (restored) updateEdgesForNode(restored.id, props.nodes, props.edges)
  releaseDragPointer()
}

/* ====== 节点缩放状态 ====== */

const resizeState = createNodeResizeState()
let activeResizePointerId: number | null = null
let activeResizeTarget: HTMLElement | null = null
let activeResizeNodeId: string | null = null

const removeResizeListeners = () => {
  window.removeEventListener('pointermove', onPointerMoveResize)
  window.removeEventListener('pointerup', onPointerUpResize)
  window.removeEventListener('pointercancel', onPointerCancelResize)
}

const releaseResizePointer = () => {
  const target = activeResizeTarget
  const pointerId = activeResizePointerId
  const nodeId = activeResizeNodeId
  activeResizePointerId = null
  activeResizeTarget = null
  activeResizeNodeId = null
  target?.removeEventListener('lostpointercapture', onResizeLostPointerCapture)
  if (target && pointerId !== null) {
    try {
      target.releasePointerCapture(pointerId)
    } catch {
      // Capture may already be released by the browser after pointerup/cancel.
    }
  }
  removeResizeListeners()
  if (nodeId) emit('node-layout-interaction-end', nodeId)
}

const onResizeLostPointerCapture = (e: PointerEvent) => {
  if (e.pointerId !== activeResizePointerId) return
  const restored = cancelNodeResize(resizeState)
  if (restored) updateEdgesForNode(restored.id, props.nodes, props.edges)
  releaseResizePointer()
}

const onPointerDownResize = (
    e: PointerEvent,
    node: DeviceNode,
    dir: 'tl' | 'tr' | 'bl' | 'br'
) => {
  e.stopPropagation()
  e.preventDefault()
  if (props.interactionLocked || e.button !== 0 || e.isPrimary === false || activeResizePointerId !== null) return
  beginNodeResize(e, node, dir, resizeState)
  activeResizePointerId = e.pointerId
  activeResizeTarget = e.currentTarget as HTMLElement
  activeResizeNodeId = node.id
  emit('node-layout-interaction-start', node.id)
  try {
    activeResizeTarget.setPointerCapture?.(e.pointerId)
  } catch {
    // Pointer capture is optional; window listeners still complete the resize.
  }
  activeResizeTarget.addEventListener('lostpointercapture', onResizeLostPointerCapture)
  window.addEventListener('pointermove', onPointerMoveResize)
  window.addEventListener('pointerup', onPointerUpResize)
  window.addEventListener('pointercancel', onPointerCancelResize)
}

const onPointerMoveResize = (e: PointerEvent) => {
  if (e.pointerId !== activeResizePointerId) return
  const changed = updateNodeResize(e, resizeState, props.zoom)
  if (!changed || !resizeState.node) return

  updateEdgesForNode(resizeState.node.id, props.nodes, props.edges)
}

const onPointerUpResize = (e: PointerEvent) => {
  if (e.pointerId !== activeResizePointerId) return
  const resized = endNodeResize(resizeState)
  if (resized) {
    emit('node-moved-or-resized', resized.id)
  }
  releaseResizePointer()
}

const onPointerCancelResize = (e: PointerEvent) => {
  if (e.pointerId !== activeResizePointerId) return
  const restored = cancelNodeResize(resizeState)
  if (restored) updateEdgesForNode(restored.id, props.nodes, props.edges)
  releaseResizePointer()
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

type NodeVisualTier = 'compact' | 'condensed' | 'expanded'

const relationSymbols: Record<string, string> = {
  EQ: '=',
  NEQ: '!=',
  GT: '>',
  GTE: '>=',
  LT: '<',
  LTE: '<='
}

const getRelationSymbol = (relation?: string) => {
  if (!relation) return ''
  if (relation === 'in') return t('app.relationIn')
  if (relation === 'not_in' || relation === 'not in') return t('app.relationNotIn')
  return relationSymbols[relation] || relation
}

const hasValue = (value: unknown) =>
  value !== null && value !== undefined && String(value).trim() !== ''

const getNodeVisualTier = (node: DeviceNode): NodeVisualTier => {
  const screenWidth = node.width * props.zoom
  const screenHeight = node.height * props.zoom
  if (screenWidth < 100 || screenHeight < 72) return 'compact'
  if (screenWidth < 168 || screenHeight < 118) return 'condensed'
  return 'expanded'
}

const getNodeVisualTierClass = (node: DeviceNode) =>
  `device-node--${getNodeVisualTier(node)}`

const POINTER_RESIZE_TARGET_SIZE_PX = 44
const POINTER_RESIZE_ALL_HANDLES_SIZE_PX = POINTER_RESIZE_TARGET_SIZE_PX * 2
const canPointerResizeNode = (node: DeviceNode) =>
  node.width * props.zoom > POINTER_RESIZE_TARGET_SIZE_PX
  && node.height * props.zoom > POINTER_RESIZE_TARGET_SIZE_PX
const canShowAllPointerResizeHandles = (node: DeviceNode) =>
  node.width * props.zoom >= POINTER_RESIZE_ALL_HANDLES_SIZE_PX
  && node.height * props.zoom >= POINTER_RESIZE_ALL_HANDLES_SIZE_PX

const getNodeRuntimeBadges = (node: DeviceNode) => {
  const traceDevice = isTraceActive.value ? getLatestTraceDeviceForNode(node.id) : null
  const configuredVariables = node.variables || []
  const traceOnlyVariables = (traceDevice?.variables || [])
    .map(variable => ({
      name: variable.name,
      value: normalizeTraceComparable(variable.value),
      trust: variable.trust,
      modelTokenSource: variable.modelTokenSource
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
      const previousTraceVariable = isTraceActive.value
        ? getPreviousTraceVariableForNode(node.id, variable.name)
        : null
      const previousTraceValue = previousTraceVariable
        ? normalizeTraceComparable(previousTraceVariable.value)
        : null
      const value = traceValue ?? String(variable.value)
      const trust = traceVariable?.trust || variable.trust
      const trustLabel = trust === 'trusted' || trust === 'untrusted'
        ? t(`app.${trust}`)
        : ''
      const changed = traceValue !== null &&
        previousTraceValue !== null &&
        previousTraceValue !== traceValue
      const displayLabel = isTraceActive.value
        ? formatPlaybackModelToken(traceVariable?.modelTokenSource, traceVariable?.name ?? variable.name)
        : formatNodeModelToken(node, variable.name)
      const displayValue = isTraceActive.value
        ? formatPlaybackModelToken(traceVariable?.modelTokenSource, value)
        : formatNodeModelToken(node, value)
      const displayPreviousValue = changed && previousTraceValue !== null
        ? formatPlaybackModelToken(previousTraceVariable?.modelTokenSource, previousTraceValue)
        : null
      return {
        label: displayLabel,
        value: displayValue,
        previousValue: displayPreviousValue,
        trust,
        changed,
        title: `${displayLabel}: ${displayValue}${trustLabel ? ` (${trustLabel})` : ''}`
      }
    })
}

const getNodeSecurityBadges = (node: DeviceNode) => {
  if (isTraceActive.value) {
    const traceDevice = getLatestTraceDeviceForNode(node.id)
    if (!traceDevice) return []
    const facts = playbackDeviceSecurityFacts(traceDevice as Parameters<typeof playbackDeviceSecurityFacts>[0])
    const formatSecurityLabel = (label: string) => {
      if (/^([^:]+):\s*(.+)$/.test(label)) {
        return formatPlaybackSecurityLabel(
          label,
          value => formatPlaybackModelToken(traceDevice.modelTokenSource, value)
        )
      }
      const variable = traceDevice.variables?.find(candidate => traceVariableMatchesName(candidate, label))
      return formatPlaybackModelToken(variable?.modelTokenSource ?? traceDevice.modelTokenSource, label)
    }
    const formatSecurityLabels = (labels: string[]) => labels.map(formatSecurityLabel).join(', ')
    const badges: Array<{ kind: 'trust' | 'privacy'; label: string; title: string }> = []
    if (facts.untrustedLabels.length > 0) {
      badges.push({
        kind: 'trust',
        label: t('app.traceVisualization.includesUntrustedSource'),
        title: t('app.traceVisualization.untrustedLabelDetails', { labels: formatSecurityLabels(facts.untrustedLabels) })
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
        title: t('app.traceVisualization.privateLabelDetails', { labels: formatSecurityLabels(facts.privateLabels) })
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
    .map(entry => formatNodeModelToken(node, entry.name))
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
  const current = getNodeDisplayState(node)
  if (!hasDisplayStateMachine(node)) return current
  const previousDevice = isTraceActive.value ? getPreviousTraceDeviceForNode(node.id) : null
  const previous = previousDevice?.state?.trim() || null
  if (previous && previous !== getNodeState(node)) {
    return `${formatPlaybackModelToken(previousDevice?.modelTokenSource, previous)} -> ${current}`
  }
  return current
}

const getFullEdgeLabel = (edge: DeviceEdge) => {
  const sourceName = edge.fromLabel || edge.from
  const targetName = edge.toLabel || edge.to
  const sourceNode = props.nodes.find(node => node.id === edge.from)
  const targetNode = props.nodes.find(node => node.id === edge.to)
  const relation = getRelationSymbol(edge.relation)
  const sourceSignal = edge.fromApi
    ? (sourceNode ? formatNodeModelToken(sourceNode, edge.fromApi) : edge.fromApi)
    : edge.itemType || t('app.condition')
  const sourceValue = sourceNode ? formatNodeModelToken(sourceNode, edge.value) : edge.value
  const condition = relation && hasValue(edge.value)
    ? `${sourceName}.${sourceSignal} ${relation} ${sourceValue}`
    : `${sourceName}.${sourceSignal}`
  const targetAction = edge.toApi && targetNode
    ? formatNodeModelToken(targetNode, edge.toApi)
    : edge.toApi
  const action = targetAction ? `${targetName}.${targetAction}` : targetName
  return `${condition} -> ${action}`
}

const getEdgeLabelText = (edge: DeviceEdge) =>
  truncateCanvasTextToWidth(getFullEdgeLabel(edge), 222)

const getEdgeLabelWidth = (edge: DeviceEdge) => {
  const textWidth = estimateCanvasTextWidth(getEdgeLabelText(edge))
  return Math.min(240, Math.max(76, textWidth + 18))
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
  if (props.interactionLocked) return
  emit('node-context', node, { x: e.clientX, y: e.clientY })
}

const getNodeAriaLabel = (node: DeviceNode) => {
  const base = `${node.label}, ${node.templateName}, ${t('app.state')}: ${getNodeDisplayState(node)}`
  return isTraceActive.value && !isNodeRepresentedInTrace(node)
    ? `${base}. ${t('app.traceVisualization.currentBoardDeviceNotRepresented')}`
    : base
}

const getNodeTitle = (node: DeviceNode) => {
  const details = [getNodeAriaLabel(node)]
  const security = getNodeSecurityBadges(node).map(badge => badge.label)
  if (security.length > 0) details.push(security.join(', '))
  return details.join(' - ')
}

const moveNodeByKeyboard = (node: DeviceNode, dx: number, dy: number) => {
  node.position.x += dx
  node.position.y += dy
  updateEdgesForNode(node.id, props.nodes, props.edges)
  emit('node-moved-or-resized', node.id)
}

const resizeNodeByKeyboard = (node: DeviceNode, dw: number, dh: number) => {
  const width = Math.min(NODE_WIDTH_RANGE.max, Math.max(NODE_WIDTH_RANGE.min, node.width + dw))
  const height = Math.min(NODE_HEIGHT_RANGE.max, Math.max(NODE_HEIGHT_RANGE.min, node.height + dh))
  if (width === node.width && height === node.height) return
  node.width = width
  node.height = height
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
  if (event.ctrlKey || event.metaKey) {
    resizeNodeByKeyboard(node, delta.dx, delta.dy)
  } else {
    moveNodeByKeyboard(node, delta.dx, delta.dy)
  }
}

/* ====== 生命周期清理 ====== */

onBeforeUnmount(() => {
  if (nodeAnimationResetTimer) clearTimeout(nodeAnimationResetTimer)
  const restoredDrag = cancelNodeDrag(dragState)
  if (restoredDrag) updateEdgesForNode(restoredDrag.id, props.nodes, props.edges)
  releaseDragPointer()
  const restored = cancelNodeResize(resizeState)
  if (restored) updateEdgesForNode(restored.id, props.nodes, props.edges)
  releaseResizePointer()
  reducedMotionQuery?.removeEventListener?.('change', syncReducedMotionPreference)
})

onMounted(() => {
  if (typeof window === 'undefined' || typeof window.matchMedia !== 'function') return
  reducedMotionQuery = window.matchMedia('(prefers-reduced-motion: reduce)')
  syncReducedMotionPreference()
  reducedMotionQuery.addEventListener?.('change', syncReducedMotionPreference)
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
    <p id="canvas-node-keyboard-instructions" class="sr-only">
      {{ t('app.canvasNodeKeyboardInstructions') }}
    </p>
    <div
        class="canvas-inner"
        :style="{
        transform: `translate(${pan.x}px, ${pan.y}px) scale(${zoom})`,
        transformOrigin: '0 0',
        '--canvas-zoom': zoom,
        '--resize-hit-size': `${44 / Math.max(zoom, 0.01)}px`,
        '--resize-hit-offset': `${-22 / Math.max(zoom, 0.01)}px`,
        '--resize-visual-size': `${11.2 / Math.max(zoom, 0.01)}px`
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
            <stop offset="0%" style="stop-color:var(--iot-node-accent-0);stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:var(--iot-node-accent-0);stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:var(--iot-node-accent-0);stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-purple" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:var(--iot-node-accent-2);stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:var(--iot-node-accent-2);stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:var(--iot-node-accent-2);stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-green" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:var(--iot-node-accent-1);stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:var(--iot-node-accent-1);stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:var(--iot-node-accent-1);stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-orange" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:var(--iot-node-accent-3);stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:var(--iot-node-accent-3);stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:var(--iot-node-accent-3);stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-red" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:var(--iot-node-accent-4);stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:var(--iot-node-accent-4);stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:var(--iot-node-accent-4);stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-teal" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:var(--iot-node-accent-5);stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:var(--iot-node-accent-5);stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:var(--iot-node-accent-5);stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-pink" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:var(--iot-node-accent-6);stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:var(--iot-node-accent-6);stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:var(--iot-node-accent-6);stop-opacity:0.2"></stop>
          </linearGradient>

          <linearGradient id="grad-yellow" x1="0%" x2="100%" y1="0%" y2="0%">
            <stop offset="0%" style="stop-color:var(--iot-node-accent-7);stop-opacity:0.2"></stop>
            <stop offset="50%" style="stop-color:var(--iot-node-accent-7);stop-opacity:1"></stop>
            <stop offset="100%" style="stop-color:var(--iot-node-accent-7);stop-opacity:0.2"></stop>
          </linearGradient>

          <!-- Arrow markers for different colors -->
          <marker id="arrow-blue" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="var(--iot-node-accent-0)"></path>
          </marker>
          <marker id="arrow-green" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="var(--iot-node-accent-1)"></path>
          </marker>
          <marker id="arrow-purple" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="var(--iot-node-accent-2)"></path>
          </marker>
          <marker id="arrow-orange" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="var(--iot-node-accent-3)"></path>
          </marker>
          <marker id="arrow-red" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="var(--iot-node-accent-4)"></path>
          </marker>
          <marker id="arrow-teal" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="var(--iot-node-accent-5)"></path>
          </marker>
          <marker id="arrow-pink" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="var(--iot-node-accent-6)"></path>
          </marker>
          <marker id="arrow-yellow" markerWidth="10" markerHeight="10" refX="10" refY="3" orient="auto">
            <path d="M0,0 L0,6 L9,3 z" fill="var(--iot-node-accent-7)"></path>
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
              v-if="edge.from === edge.to && shouldRenderEdgeFlow(edge)"
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
              v-else-if="shouldRenderEdgeFlow(edge)"
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
              v-if="edge.from !== edge.to && shouldRenderEdgeFlow(edge)"
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
          aria-describedby="canvas-node-keyboard-instructions"
          :title="getNodeTitle(node)"
          :class="[getNodeVisualTierClass(node), { 'trace-active': isNodeInTrace(node) }, { 'trace-not-represented': isTraceActive && !isNodeRepresentedInTrace(node) }, { 'trace-changed': isNodeTraceChanged(node) }, { 'trace-change-pulse': shouldAnimateTraceChange(node) }, { 'device-attacked': isDeviceAttacked(node.id) }, { 'node-focused': props.focusedNodeId === node.id }, { 'cursor-default': interactionLocked }]"
          :style="{
          left: node.position.x + 'px',
          top: node.position.y + 'px',
          width: node.width + 'px',
          height: node.height + 'px',
          '--node-accent-color': getNodeAccentColor(node.id),
          backgroundColor: getNodeSurfaceColor(node.id),
          borderColor: isDeviceAttacked(node.id) ? '#EF4444' : getNodeBorderColor(node.id),
          ...(isNodeInTrace(node) ? { '--trace-glow-color': isDeviceAttacked(node.id) ? '#EF4444' : getNodeBorderColor(node.id) } : {})
        }"
          @pointerdown.stop="onNodePointerDown($event, node)"
          @contextmenu.stop.prevent="onNodeContextInternal(node, $event)"
          @keydown="onNodeKeydown($event, node)"
      >
        <div class="device-node-content">
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
            <div class="device-label" :title="node.label">
              {{ node.label }}
            </div>
          </div>
          <!-- 下部分：设备状态显示 -->
          <div class="device-state" :class="getStateDisplayClass(node)" :title="getNodeStateTitle(node)">
            <span class="device-state-dot"></span>
            <Transition name="trace-device-state" mode="out-in">
              <span :key="getNodeVisualStateKey(node)" class="device-state-value">{{ getNodeDisplayState(node) }}</span>
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
            v-if="!interactionLocked && canShowAllPointerResizeHandles(node)"
            class="resize-handle tl"
            aria-hidden="true"
            @pointerdown.stop="onPointerDownResize($event, node, 'tl')"
        ></div>
        <div
            v-if="!interactionLocked && canShowAllPointerResizeHandles(node)"
            class="resize-handle tr"
            aria-hidden="true"
            @pointerdown.stop="onPointerDownResize($event, node, 'tr')"
        ></div>
        <div
            v-if="!interactionLocked && canShowAllPointerResizeHandles(node)"
            class="resize-handle bl"
            aria-hidden="true"
            @pointerdown.stop="onPointerDownResize($event, node, 'bl')"
        ></div>
        <div
            v-if="!interactionLocked && canPointerResizeNode(node)"
            class="resize-handle br"
            aria-hidden="true"
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
  gap: clamp(0.2rem, 2.4cqmin, 0.5rem);
  justify-self: center;
  min-width: 0;
  min-height: clamp(1.15rem, 13cqmin, 10rem);
  width: 82%;
  padding: clamp(0.18rem, 1.7cqmin, 1.5rem) clamp(0.4rem, 4cqmin, 4rem);
  border: 1px solid var(--border);
  border-radius: 999px;
  background: color-mix(in srgb, var(--surface-elevated) 86%, transparent);
  color: var(--text);
  font-weight: 700;
  z-index: 5;
  box-sizing: border-box;
  box-shadow: 0 1px 3px color-mix(in srgb, var(--text) 12%, transparent);
  line-height: 1;
  overflow: hidden;
}

.device-node--expanded .device-state {
  grid-area: state;
  justify-self: start;
  width: 100%;
}

.device-state-dot {
  width: clamp(0.35rem, 3.5cqmin, 0.75rem);
  height: clamp(0.35rem, 3.5cqmin, 0.75rem);
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
  font-size: clamp(0.625rem, 5cqmin, 5rem);
  line-height: 1;
}

.state-defined {
  border-color: color-mix(in srgb, var(--node-accent-color) 44%, var(--border));
  background: color-mix(in srgb, var(--node-accent-color) 13%, var(--surface-elevated));
}

.state-defined .device-state-dot {
  background: var(--node-accent-color);
  box-shadow: 0 0 0 2px color-mix(in srgb, var(--node-accent-color) 18%, transparent);
}

.state-stateless {
  background: color-mix(in srgb, var(--surface-muted) 88%, transparent);
  color: var(--text-muted);
}

.state-stateless .device-state-dot {
  background: var(--text-muted);
}

@media (prefers-reduced-motion: reduce) {
  .attack-indicator,
  .device-state-dot,
  .trace-state-dot {
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

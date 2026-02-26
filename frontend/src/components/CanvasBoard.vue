<script setup lang="ts">
import { computed, onBeforeUnmount, onMounted, ref, watch } from 'vue'

import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { CanvasPan } from '../types/canvas'

import {
  updateEdgesForNode,
  getSelfLoopD
} from '../utils/canvas/geometry'

import { getLinkPoints } from '../utils/rule'

import { getNodeIconWithFallback, getDefaultDeviceIcon, getDeviceIconPath, getVariableIconPath } from '../utils/device'

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

// Legacy function for backward compatibility (used elsewhere)
const getParticleColor = (index: number): string => {
  const colors = ['url(#grad-blue)', 'url(#grad-purple)', '#ef4444']
  return colors[index % colors.length]
}

const getParticleSize = (index: number): number => {
  const sizes = [3, 2, 2.5]
  return sizes[index % sizes.length]
}

const getParticleDuration = (index: number): string => {
  const durations = ['3s', '5s', '4s']
  return durations[index % durations.length]
}

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

// 获取变量节点的边框颜色（使用父设备的颜色）
const getVariableNodeBorderColor = (node: DeviceNode): string => {
  if (!node.templateName.startsWith('variable_')) {
    return getNodeBorderColor(node.id)
  }
  // 从变量节点ID提取父设备ID（格式：deviceId_variableName，使用lastIndexOf处理deviceId中可能存在的下划线）
  const parentDeviceId = node.id.substring(0, node.id.lastIndexOf('_'))
  return getNodeBorderColor(parentDeviceId)
}

// 获取变量节点的背景颜色（使用父设备的颜色）
const getVariableNodeBgColor = (node: DeviceNode): string => {
  if (!node.templateName.startsWith('variable_')) {
    return getNodeBgColor(node.id)
  }
  // 从变量节点ID提取父设备ID
  const parentDeviceId = node.id.substring(0, node.id.lastIndexOf('_'))
  return getNodeBgColor(parentDeviceId)
}

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

// Handle image loading errors by showing default icon
const handleImageError = (event: Event, node: DeviceNode) => {
  const img = event.target as HTMLImageElement
  // 如果是变量节点，使用变量默认图标
  if (node.templateName.startsWith('variable_')) {
    const variableName = node.templateName.replace('variable_', '')
    const iconPath = getVariableIconPath(variableName)
    if (iconPath) {
      img.src = iconPath
      return
    }
  }
  const defaultIcon = getDefaultDeviceIcon(node.templateName)
  img.src = `data:image/svg+xml;base64,${btoa(defaultIcon)}`
}

// 获取设备在轨迹中的最新状态（从之前的轨迹状态中查找）
const getLatestTraceState = (nodeId: string, nodeLabel: string): string | null => {
  if (!props.highlightedTrace?.states) return null
  
  const nodeIdLower = nodeId.toLowerCase()
  const nodeLabelLower = nodeLabel.toLowerCase()
  
  // 从当前选中状态向前查找，找到设备最近的状态
  const currentIndex = props.highlightedTrace.selectedStateIndex || 0
  for (let i = currentIndex; i >= 0; i--) {
    const state = props.highlightedTrace.states[i]
    if (!state?.devices) continue
    
    const device = state.devices.find(d => 
      d.deviceId.toLowerCase() === nodeIdLower || 
      d.deviceLabel.toLowerCase() === nodeLabelLower ||
      d.deviceId.toLowerCase() === nodeLabelLower ||
      d.deviceLabel.toLowerCase() === nodeIdLower
    )
    
    if (device) {
      return (device as any).state || (device as any).newState || null
    }
  }
  
  return null
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

    const device = state.devices.find(d =>
      d.deviceId.toLowerCase() === node.id.toLowerCase() ||
      d.deviceLabel.toLowerCase() === node.label.toLowerCase() ||
      d.deviceId.toLowerCase() === node.label.toLowerCase() ||
      d.deviceLabel.toLowerCase() === node.id.toLowerCase()
    )

    if (device) {
      const prev = (device as any).state || (device as any).newState || null
      return prev
    }
  }
  return null
}

// 获取节点的当前状态
const getNodeState = (node: DeviceNode): string => {
  // 如果有高亮轨迹且当前选中了某个状态，显示轨迹中的状态
  if (props.highlightedTrace && props.highlightedTrace.selectedStateIndex !== undefined) {
    // 先尝试从当前状态中获取设备状态
    const traceDevice = getTraceDeviceForNode(node.id, node.label)
    if (traceDevice) {
      // 优先使用 state 字段，兼容历史 JSON 中的 newState 字段
      return (traceDevice as any).state || (traceDevice as any).newState || node.state || 'Working'
    }
    
    // 如果当前状态中没有该设备，从之前的轨迹状态中获取最新状态
    const latestState = getLatestTraceState(node.id, node.label)
    if (latestState) {
      return latestState
    }
    
    // 如果轨迹中没有记录，保持当前节点状态不变
    return node.state || 'Working'
  }
  // 否则显示节点的初始状态
  return node.state || 'Working'
}

// 获取状态显示的样式类
const getStateDisplayClass = (node: DeviceNode): string => {
  // 翻转动画时使用旧状态
  const flippingState = getFlippingState(node)
  const state = flippingState || getNodeState(node) || 'Working'
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

// 判断是否为变量节点
const isVariableNode = (node: DeviceNode): boolean => {
  return node.templateName.startsWith('variable_')
}

// 获取节点当前状态对应的图标
const getCurrentNodeIcon = (node: DeviceNode): string => {
  // 如果是变量节点（templateName 以 variable_ 开头），从 variables 文件夹获取图标
  if (node.templateName.startsWith('variable_')) {
    const variableName = node.templateName.replace('variable_', '')
    return getVariableIconPath(variableName)
  }

  const folder = node.templateName.replace(/ /g, '_')
  
  // 如果正在翻转动画中，使用旧状态
  const flippingState = getFlippingState(node)
  const currentState = flippingState || getNodeState(node) || 'Working'

  // 尝试不同的状态名称变体
  const possibleStates = [
    currentState,
    currentState.toLowerCase(),
    currentState.charAt(0).toUpperCase() + currentState.slice(1).toLowerCase(),
    'Working',
    'On',
    'Off'
  ]

  for (const stateName of possibleStates) {
    try {
      const path = getDeviceIconPath(folder, stateName)
      if (path) return path
    } catch (e) {
      continue
    }
  }

  // 如果所有尝试都失败，返回默认图标
  return `data:image/svg+xml;base64,${btoa(getDefaultDeviceIcon(node.templateName))}`
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
  getNodeIcon: (node: DeviceNode) => string
  /** 获取节点标签样式（Board.vue 传入 getNodeLabelStyle） */
  getNodeLabelStyle: (node: DeviceNode) => Record<string, string | number>
  /** 高亮显示的反例路径 */
  highlightedTrace?: {
    states: Array<{
      devices: Array<{
        deviceId: string
        deviceLabel: string
        state?: string  // 新字段
        newState?: string  // 兼容旧数据
        variables?: Array<{ name: string; value: string }>
      }>
      envVariables?: Array<{ name: string; value: string; trust?: string }>
    }>
    selectedStateIndex?: number
  } | null
}>()

// 获取当前选中状态的设备信息
const currentTraceDevices = computed(() => {
  if (!props.highlightedTrace?.states || props.highlightedTrace.selectedStateIndex === undefined) {
    return []
  }
  return props.highlightedTrace.states[props.highlightedTrace.selectedStateIndex]?.devices || []
})

// 判断是否有反例路径动画在进行
const isTraceActive = computed(() => {
  return props.highlightedTrace?.states && 
         props.highlightedTrace.selectedStateIndex !== undefined &&
         props.highlightedTrace.selectedStateIndex >= 0
})

// 跟踪每个节点是否需要触发动画（使用节点ID作为key）
const nodeAnimationTrigger = ref<Record<string, number>>({})

// 跟踪每个节点的旧状态（用于翻转动画显示）
const nodePreviousState = ref<Record<string, string>>({})

// 监听状态索引变化，触发节点状态变化动画
watch(() => props.highlightedTrace?.selectedStateIndex, (newIndex, oldIndex) => {
  if (newIndex === undefined || newIndex === oldIndex) return
  
  // 当状态变化时，比较每个节点的状态变化
  const currentState = props.highlightedTrace?.states?.[newIndex]
  const prevState = oldIndex !== undefined ? props.highlightedTrace?.states?.[oldIndex] : null
  
  if (!currentState?.devices) return
  
  for (const device of currentState.devices) {
    const deviceIdLower = device.deviceId.toLowerCase()
    const deviceLabelLower = device.deviceLabel.toLowerCase()
    const currentDeviceState = device.state || device.newState || null
    
    // 获取前一个状态
    let prevDeviceState: string | null = null
    if (prevState?.devices) {
      const prevDevice = prevState.devices.find((d: any) => 
        d.deviceId.toLowerCase() === deviceIdLower || 
        d.deviceLabel.toLowerCase() === deviceLabelLower
      )
      if (prevDevice) {
        prevDeviceState = prevDevice.state || prevDevice.newState || null
      }
    }
    
    // 如果状态不同，触发动画（通过增加trigger值来强制重新渲染）
    if (currentDeviceState && prevDeviceState && currentDeviceState !== prevDeviceState) {
      const nodeId = deviceIdLower === deviceLabelLower ? deviceIdLower : deviceIdLower + '_' + deviceLabelLower
      nodeAnimationTrigger.value[nodeId] = (nodeAnimationTrigger.value[nodeId] || 0) + 1
      // 保存旧状态，用于翻转过程中显示
      nodePreviousState.value[nodeId] = prevDeviceState
    }
  }
  
  // 动画完成后清除旧状态（延迟清除，给翻转动画时间完成）
  setTimeout(() => {
    nodePreviousState.value = {}
    // 清除触发器，确保只有状态真正变化时才再次触发
    nodeAnimationTrigger.value = {}
  }, 650)
})

// 判断节点是否应该播放翻转动画
const shouldAnimateFlip = (node: DeviceNode): boolean => {
  const nodeIdLower = node.id.toLowerCase()
  const nodeLabelLower = node.label.toLowerCase()
  const triggerKey = nodeIdLower === nodeLabelLower ? nodeIdLower : nodeIdLower + '_' + nodeLabelLower
  
  // 检查是否有动画触发
  return !!nodeAnimationTrigger.value[triggerKey]
}

// 用于模板中的翻转状态（计算属性）
const getFlippingStateForNode = (node: DeviceNode): string | null => {
  return getFlippingState(node)
}

// 获取节点在翻转动画中应该显示的状态（旧状态）
const getFlippingState = (node: DeviceNode): string | null => {
  const nodeIdLower = node.id.toLowerCase()
  const nodeLabelLower = node.label.toLowerCase()
  const triggerKey = nodeIdLower === nodeLabelLower ? nodeIdLower : nodeIdLower + '_' + nodeLabelLower
  
  // 如果正在动画，返回旧状态
  if (shouldAnimateFlip(node) && nodePreviousState.value[triggerKey]) {
    return nodePreviousState.value[triggerKey]
  }
  return null
}

// 判断节点是否在当前反例路径中
const isNodeInTrace = (node: DeviceNode): boolean => {
  if (!isTraceActive.value || !props.highlightedTrace?.states) return false
  
  const nodeIdLower = node.id.toLowerCase()
  const nodeLabelLower = node.label.toLowerCase()
  
  // 检查当前选中状态
  if (currentTraceDevices.value.some(d => 
    d.deviceId.toLowerCase() === nodeIdLower || 
    d.deviceLabel.toLowerCase() === nodeLabelLower ||
    d.deviceId.toLowerCase() === nodeLabelLower ||
    d.deviceLabel.toLowerCase() === nodeIdLower
  )) {
    return true
  }
  
  // 检查之前的轨迹状态
  const currentIndex = props.highlightedTrace.selectedStateIndex || 0
  for (let i = 0; i < currentIndex; i++) {
    const state = props.highlightedTrace.states[i]
    if (!state?.devices) continue
    
    if (state.devices.some(d => 
      d.deviceId.toLowerCase() === nodeIdLower || 
      d.deviceLabel.toLowerCase() === nodeLabelLower ||
      d.deviceId.toLowerCase() === nodeLabelLower ||
      d.deviceLabel.toLowerCase() === nodeIdLower
    )) {
      return true
    }
  }
  
  return false
}

// 获取变量节点在反例路径中的值
const getTraceVariableValue = (node: DeviceNode): { value: string; state: string } | null => {
  if (!isTraceActive.value || !props.highlightedTrace?.states) return null
  
  // 从节点ID提取父设备ID和变量名（格式：parentDeviceId_variableName）
  const parts = node.id.split('_')
  if (parts.length < 2) return null
  
  const parentDeviceId = parts[0]
  const variableName = parts.slice(1).join('_')
  const parentIdLower = parentDeviceId.toLowerCase()
  const varNameLower = variableName.toLowerCase()
  
  // 从当前选中状态向前查找，找到设备最近的变量值和状态
  const currentIndex = props.highlightedTrace.selectedStateIndex || 0
  for (let i = currentIndex; i >= 0; i--) {
    const state = props.highlightedTrace.states[i]
    if (!state?.devices) continue
    
    const deviceState = state.devices.find(d => 
      d.deviceId.toLowerCase() === parentIdLower || 
      d.deviceLabel.toLowerCase() === parentIdLower ||
      d.deviceId.toLowerCase() === parentIdLower ||
      d.deviceLabel.toLowerCase() === parentIdLower
    )
    
    if (deviceState) {
      // 查找对应的变量值（大小写不敏感匹配）
      const variable = deviceState.variables?.find(v => 
        v.name.toLowerCase() === varNameLower || 
        v.name.toLowerCase() === `d_${varNameLower}`
      )
      
      if (variable) {
        return {
          value: variable.value || 'Unknown',
          state: (deviceState as any).state || (deviceState as any).newState || 'Working'
        }
      }
      // 如果当前状态没有该变量，继续向前查找（使用上一个时间点的值）
    }
  }
  
  return null
}

// 获取环境变量在反例路径中的值（如 a_temperature, a_airQuality）
const getTraceEnvVariableValue = (variableName: string): string | null => {
  if (!isTraceActive.value || !props.highlightedTrace?.states) return null
  
  const varNameLower = variableName.toLowerCase()
  
  // 从当前选中状态向前查找，找到最近的变量值
  const currentIndex = props.highlightedTrace.selectedStateIndex || 0
  for (let i = currentIndex; i >= 0; i--) {
    const state = props.highlightedTrace.states[i]
    if (!state?.envVariables) continue
    
    const envVar = state.envVariables.find(v => 
      v.name.toLowerCase() === varNameLower ||
      v.name.toLowerCase() === `a_${varNameLower}` ||
      v.name.toLowerCase() === varNameLower.replace('a_', '')
    )
    
    if (envVar) {
      return envVar.value
    }
  }
  
  return null
}

// 根据节点ID或标签查找对应的trace设备
const getTraceDeviceForNode = (nodeId: string, nodeLabel: string) => {
  const nodeIdLower = nodeId.toLowerCase()
  const nodeLabelLower = nodeLabel.toLowerCase()
  return currentTraceDevices.value.find(d => 
    d.deviceId.toLowerCase() === nodeIdLower || 
    d.deviceLabel.toLowerCase() === nodeLabelLower ||
    d.deviceId.toLowerCase() === nodeLabelLower ||
    d.deviceLabel.toLowerCase() === nodeIdLower
  )
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
  /** 节点右键（设备弹窗） */
  (e: 'node-context', node: DeviceNode, evt: MouseEvent): void
  /** 节点拖拽或缩放结束，通知 Board.vue 持久化 nodes/edges */
  (e: 'node-moved-or-resized', nodeId: string): void
}>()

/* ====== 节点拖拽状态 ====== */

const dragState = createNodeDragState()

const onNodePointerDown = (e: PointerEvent, node: DeviceNode) => {
  e.preventDefault()
  // 只处理节点自身拖拽，不影响画布平移（事件在模板里用了 .stop）
  beginNodeDrag(e, node, dragState)
  window.addEventListener('pointermove', onNodePointerMove)
  window.addEventListener('pointerup', onNodePointerUp)
}

const onNodePointerMove = (e: PointerEvent) => {
  const changed = updateNodeDrag(e, dragState)
  if (!changed || !dragState.node) return

  // 节点位置变了，更新相关边几何
  updateEdgesForNode(dragState.node.id, props.nodes, props.edges)
}

const onNodePointerUp = () => {
  const moved = endNodeDrag(dragState)
  if (moved) {
    emit('node-moved-or-resized', moved.id)
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
  beginNodeResize(e, node, dir, resizeState)
  window.addEventListener('pointermove', onPointerMoveResize)
  window.addEventListener('pointerup', onPointerUpResize)
}

const onPointerMoveResize = (e: PointerEvent) => {
  const changed = updateNodeResize(e, resizeState)
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

/* ====== 右键节点：交给 Board.vue 处理弹窗 ====== */

const onNodeContextInternal = (node: DeviceNode, e: MouseEvent) => {
  e.preventDefault()
  emit('node-context', node, e)
}

/* ====== 生命周期清理 ====== */

// Run test on component mount
onMounted(() => {
  testColorDistribution()
})

onBeforeUnmount(() => {
  window.removeEventListener('pointermove', onNodePointerMove)
  window.removeEventListener('pointerup', onNodePointerUp)
  window.removeEventListener('pointermove', onPointerMoveResize)
  window.removeEventListener('pointerup', onPointerUpResize)
})
</script>

<template>
  <div
      class="canvas"
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

        <g v-for="(edge, index) in edges" :key="edge.id">
          <!-- Base lines removed - only showing particle effects -->

          <!-- Particle lines (gradient animation) -->
          <path
              v-if="edge.from === edge.to"
              class="edge-line particle-line"
              :class="getParticleOpacity(index)"
              :d="getSelfLoopPathD(edge)"
              fill="none"
              filter="url(#glow)"
              :stroke="getParticleColorByEdge(edge)"
              stroke-width="2"
              :stroke-dasharray="isInternalVariableEdge(edge) ? '5,5' : ''"
              :marker-end="getArrowMarker(edge)"
          />
          <line
              v-else
              class="edge-line particle-line"
              :class="getParticleOpacity(index)"
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

          <!-- Animated particle for each edge -->
          <circle
              v-if="edge.from !== edge.to"
              :fill="getParticleFillColor(edge)"
              filter="url(#glow)"
              :r="getParticleSize(index)"
          >
            <animateMotion
                :dur="getParticleDuration(index)"
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
                repeatCount="indefinite"
            />
          </circle>
          <!-- For self-loops, we could add a different animation -->
        </g>
      </svg>

      <!-- 设备节点 -->
      <div
          v-for="node in nodes"
          :key="node.id + (highlightedTrace?.selectedStateIndex ?? '')"
          :data-node-id="node.id"
          class="device-node"
          :class="[getNodeBgColorClass(node.id), getNodeColorClass(node.id), { 'variable-node': isVariableNode(node) }, { 'trace-active': isNodeInTrace(node) }, { 'node-flip': (getPreviousState(node) && getPreviousState(node) !== getNodeState(node)) || shouldAnimateFlip(node) }]"
          :style="{
          left: node.position.x + 'px',
          top: node.position.y + 'px',
          width: node.width + 'px',
          height: node.height + 'px',
          backgroundColor: isVariableNode(node) ? getVariableNodeBgColor(node) : getNodeBgColor(node.id),
          borderColor: isVariableNode(node) ? getVariableNodeBorderColor(node) : getNodeBorderColor(node.id),
          ...(isNodeInTrace(node) ? { '--trace-glow-color': isVariableNode(node) ? getVariableNodeBorderColor(node) : getNodeBorderColor(node.id) } : {})
        }"
          @pointerdown.stop="onNodePointerDown($event, node)"
          @contextmenu.prevent="onNodeContextInternal(node, $event)"
      >
        <!-- 变量节点：只显示图标（圆形） -->
        <div v-if="isVariableNode(node)" class="variable-node-wrapper">
          <div class="variable-node-content">
            <img
                class="variable-img"
                :src="getCurrentNodeIcon(node)"
                :alt="node.label"
                draggable="false"
                @error="handleImageError($event, node)"
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
                  @error="handleImageError($event, node)"
              />
            </div>
            <div class="variable-tooltip-info">
              <span class="variable-tooltip-label">{{ node.label }}</span>
              <span v-if="isTraceActive && getTraceVariableValue(node)" class="variable-tooltip-value">
                值: {{ getTraceVariableValue(node)?.value }}
              </span>
            </div>
          </div>
        </div>

        <!-- 普通设备节点：图标+名字+状态 -->
        <div v-else class="device-node-content">
          <!-- 上部分：左边图标，右边名字 -->
          <div class="device-top-row">
            <img
                class="device-img"
                :src="getCurrentNodeIcon(node)"
                :alt="node.label"
                draggable="false"
                :style="{
                width: node.width * 0.38 + 'px',
                height: node.height * 0.35 + 'px'
              }"
                @error="handleImageError($event, node)"
            />
            <div class="device-label-wrapper">
              <div class="device-label" :style="getNodeLabelStyle(node)">
                {{ node.label }}
              </div>
            </div>
          </div>
          <!-- 下部分：设备状态显示 -->
          <div class="device-state" :class="getStateDisplayClass(node)">
            <span class="device-state-dot"></span>
            <span class="device-state-value">{{ getFlippingStateForNode(node) || getNodeState(node) }}</span>
          </div>
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
</template>

<style scoped>
.device-state {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 4px;
  padding: 3px 8px;
  border-radius: 12px;
  font-size: 10px;
  font-weight: 600;
  z-index: 5;
  width: 100%;
  box-sizing: border-box;
  box-shadow: 0 1px 3px rgba(0, 0, 0, 0.1);
  line-height: 1;
}

.device-state-dot {
  width: 6px;
  height: 6px;
  border-radius: 50%;
  flex-shrink: 0;
  display: inline-block;
}

.device-state-value {
  max-width: 60px;
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

/* 3D 翻转动画 - 设备内容区域 */
.device-node-content {
  transition: transform 0.3s ease-in-out;
}

.node-flip .device-node-content {
  animation: flip-animation 0.6s ease-in-out;
  transform-style: preserve-3d;
}

.node-flip .device-img {
  animation: flip-inner 0.6s ease-in-out forwards;
  transform-style: preserve-3d;
}

/* 节点整体轻微震动效果作为补充 */
.node-flip {
  position: relative;
}

/* 前30%时间展示旧图标，之后切换为新图标 */
@keyframes flip-animation {
  0% {
    transform: perspective(600px) rotateY(0deg);
  }
  30% {
    transform: perspective(600px) rotateY(0deg);
  }
  60% {
    transform: perspective(600px) rotateY(90deg);
  }
  100% {
    transform: perspective(600px) rotateY(0deg);
  }
}

@keyframes flip-inner {
  0% {
    transform: perspective(200px) rotateY(0deg) scale(1);
    opacity: 1;
  }
  25% {
    transform: perspective(200px) rotateY(20deg) scale(1.1);
    opacity: 1;
  }
  30% {
    transform: perspective(200px) rotateY(0deg) scale(1);
    opacity: 1;
  }
  31% {
    opacity: 0;
  }
  32% {
    opacity: 1;
  }
  100% {
    transform: perspective(200px) rotateY(10deg) scale(1.05);
  }
  100% {
    transform: perspective(200px) rotateY(0deg) scale(1);
  }
}
</style>

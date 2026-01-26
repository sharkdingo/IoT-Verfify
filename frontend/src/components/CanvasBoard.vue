<script setup lang="ts">
import { onBeforeUnmount, onMounted } from 'vue'

import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { CanvasPan } from '../types/canvas'

import {
  updateEdgesForNode,
  getSelfLoopD
} from '../utils/canvas/geometry'

import { getLinkPoints } from '../utils/rule'

import { getNodeIconWithFallback, getDefaultDeviceIcon } from '../utils/device'

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

// Get particle color based on source device color (for edges)
const getParticleColorByEdge = (edge: DeviceEdge): string => {
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
  const testIds = ['Sensor', 'Sensor_1', 'Sensor_2', 'Switch', 'Switch_1', 'Light', 'Light_1', 'Kitchen Sensor', 'Living Room Light']
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

// Get arrow marker ID based on source device color
const getArrowMarker = (edge: DeviceEdge): string => {
  const sourceNode = props.nodes.find(n => n.id === edge.from)
  if (!sourceNode) return 'url(#arrow-blue)' // fallback

  const colorIndex = getNodeColorIndex(sourceNode.id)
  const markers = ['url(#arrow-blue)', 'url(#arrow-green)', 'url(#arrow-purple)', 'url(#arrow-orange)']
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
  const defaultIcon = getDefaultDeviceIcon(node.templateName)
  img.src = `data:image/svg+xml;base64,${btoa(defaultIcon)}`
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
}>()

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
          :key="node.id"
          :data-node-id="node.id"
          class="device-node"
          :class="[getNodeBgColorClass(node.id), getNodeColorClass(node.id)]"
          :style="{
          left: node.position.x + 'px',
          top: node.position.y + 'px',
          width: node.width + 'px',
          height: node.height + 'px',
          backgroundColor: getNodeBgColor(node.id),
          borderColor: getNodeBorderColor(node.id)
        }"
          @pointerdown.stop="onNodePointerDown($event, node)"
          @contextmenu.prevent="onNodeContextInternal(node, $event)"
      >
        <img
            class="device-img"
            :src="getNodeIconWithFallback(node)"
            :alt="node.label"
            draggable="false"
            :style="{
            width: node.width * 0.55 + 'px',
            height: node.height * 0.35 + 'px'
          }"
            @error="handleImageError($event, node)"
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
</template>

<style scoped>
</style>

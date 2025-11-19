<script setup lang="ts">
import { onBeforeUnmount } from 'vue'

import type { DeviceNode } from '../types/node'
import type { DeviceEdge } from '../types/edge'
import type { CanvasPan } from '../types/canvas'

import {
  updateEdgesForNode,
  getSelfLoopD
} from '../utils/canvas/geometry'

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

/* ====== 右键节点：交给 Board.vue 处理弹窗 ====== */

const onNodeContextInternal = (node: DeviceNode, e: MouseEvent) => {
  e.preventDefault()
  emit('node-context', node, e)
}

/* ====== 生命周期清理 ====== */

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
          <marker
              id="arrow"
              markerWidth="10"
              markerHeight="10"
              refX="10"
              refY="3"
              orient="auto"
          >
            <!-- 跟你原来一样，颜色用 CSS 变量 -->
            <path d="M0,0 L0,6 L9,3 z" :fill="`var(--iot-color-edge)`"></path>
          </marker>
        </defs>

        <g v-for="edge in edges" :key="edge.id">
          <!-- 自环：from === to，用 path -->
          <path
              v-if="edge.from === edge.to"
              class="edge-line"
              :d="getSelfLoopPathD(edge)"
              marker-end="url(#arrow)"
          />
          <!-- 普通边：用 line -->
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
          @contextmenu.prevent="onNodeContextInternal(node, $event)"
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
</template>

<style scoped>
</style>

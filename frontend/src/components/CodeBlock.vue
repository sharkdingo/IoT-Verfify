<script setup lang="ts">
import { ref, computed, type VNode } from "vue";
import { CheckOutlined, CopyOutlined } from '@ant-design/icons-vue';

const props = defineProps<{
  highlightVnode: VNode;
  language: string;
}>();

const copied = ref(false);
const contentRef = ref<HTMLElement>();

function copyHandle() {
  if (!contentRef.value) return;
  const text = contentRef.value.textContent || "";
  navigator.clipboard.writeText(text).then(() => {
    copied.value = true;
    setTimeout(() => (copied.value = false), 2000);
  });
}

const langLabel = computed(() => props.language?.toUpperCase() || "TEXT");
</script>

<template>
  <div class="code-block-container">
    <div class="code-header">
      <span class="lang-label">{{ langLabel }}</span>
      <div class="copy-btn" @click="copyHandle">
        <span v-if="copied" class="copy-text">
          <CheckOutlined /> Copied!
        </span>
        <span v-else class="copy-text">
          <CopyOutlined /> Copy
        </span>
      </div>
    </div>

    <div ref="contentRef" class="code-content">
      <component :is="props.highlightVnode" />
    </div>
  </div>
</template>

<style scoped>
/* 使用 CSS 变量或针对 .dark-mode 的层级选择器来实现主题切换
  这里我们假设你的外层容器会在 html 或 body 上添加 .dark 类
*/

.code-block-container {
  margin: 16px 0;
  border-radius: 8px;
  overflow: hidden;
  border: 1px solid #e5e5e5;
  background: #f8f8f8; /* 默认浅色底 */
  transition: all 0.3s ease;
}

/* 浅色模式下的 Header */
.code-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  background: #eeeeee;
  padding: 6px 12px;
  color: #666;
  border-bottom: 1px solid #e5e5e5;
  user-select: none;
}

.lang-label {
  font-size: 12px;
  font-weight: 600;
  color: #555;
}

.copy-btn {
  cursor: pointer;
  display: flex;
  align-items: center;
  font-size: 12px;
  color: #666;
  transition: color 0.2s;
}

.copy-btn:hover {
  color: #000;
}

.copy-text {
  display: flex;
  align-items: center;
  gap: 4px;
}

.code-content {
  padding: 12px 16px;
  overflow-x: auto;
  font-family: Consolas, Monaco, 'Andale Mono', monospace;
  font-size: 14px;
  line-height: 1.5;
  /* 浅色模式文字颜色由 shiki 决定，这里设置默认值 */
  color: #333;
}

/* ============== 深色模式适配 (Dark Mode) ============== */
/* Vue 组件中，如果使用了 :deep 或全局类名，
   需要确保 .dark 类在父级能被选中。
   在 Tailwind 或 Element Plus 中，通常是在 html.dark 下生效
*/
:global(.dark) .code-block-container {
  border-color: #444;
  background: #1e1e1e;
}

:global(.dark) .code-header {
  background: #2d2d2d;
  border-bottom-color: #444;
  color: #cdcdcd;
}

:global(.dark) .lang-label {
  color: #9ca3af;
}

:global(.dark) .copy-btn {
  color: #9ca3af;
}

:global(.dark) .copy-btn:hover {
  color: #fff;
}

:global(.dark) .code-content {
  color: #e5e5e5;
}

/* 强制覆盖 shiki 生成的样式，确保背景色透明，以便使用我们容器的背景 */
:deep(pre.shiki) {
  background-color: transparent !important;
  margin: 0;
  padding: 0;
}
</style>
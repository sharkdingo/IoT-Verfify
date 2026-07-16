<script setup lang="ts">
import { ref, computed, onUnmounted, type VNode } from "vue";
import { CheckOutlined, CopyOutlined } from '@ant-design/icons-vue';
import { useI18n } from 'vue-i18n';

const props = defineProps<{
  highlightVnode: VNode;
  language: string;
}>();

const copyState = ref<'idle' | 'copied' | 'failed'>('idle');
const contentRef = ref<HTMLElement>();
const { t } = useI18n();
let copyResetTimer: ReturnType<typeof setTimeout> | null = null;

function showCopyState(state: 'copied' | 'failed') {
  copyState.value = state;
  if (copyResetTimer) clearTimeout(copyResetTimer);
  copyResetTimer = setTimeout(() => {
    copyState.value = 'idle';
    copyResetTimer = null;
  }, 2000);
}

async function copyHandle() {
  if (!contentRef.value) return;
  const text = contentRef.value.textContent || "";
  try {
    if (!navigator.clipboard?.writeText) throw new Error('Clipboard API unavailable');
    await navigator.clipboard.writeText(text);
    showCopyState('copied');
  } catch {
    showCopyState('failed');
  }
}

onUnmounted(() => {
  if (copyResetTimer) clearTimeout(copyResetTimer);
});

const langLabel = computed(() => props.language?.toUpperCase() || "TEXT");
</script>

<template>
  <div class="code-block-container">
    <div class="code-header">
      <span class="lang-label">{{ langLabel }}</span>
      <button type="button" class="copy-btn" :aria-label="t('app.copy')" @click="copyHandle">
        <span v-if="copyState === 'copied'" class="copy-text" aria-live="polite">
          <CheckOutlined /> {{ t('app.copied') }}
        </span>
        <span v-else-if="copyState === 'failed'" class="copy-text" aria-live="polite">
          <CopyOutlined /> {{ t('app.copyFailed') }}
        </span>
        <span v-else class="copy-text" aria-live="polite">
          <CopyOutlined /> {{ t('app.copy') }}
        </span>
      </button>
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
  padding: 4px;
  border: 0;
  background: transparent;
}

.copy-btn:hover {
  color: #000;
}

.copy-btn:focus-visible {
  outline: 2px solid #2563eb;
  outline-offset: 2px;
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

/* ============== 🌙 深色模式适配 ============== */

/* 1. 修正选择器：使用 .dark-mode 而不是 .dark */
:global(.dark-mode) .code-block-container {
  border-color: #333;
  /* 使用更深的背景色，增加对比度 */
  background: #0d1117;
}

:global(.dark-mode) .code-header {
  background: #161b22; /* 稍微亮一点的头部 */
  border-bottom-color: #333;
  color: #8b949e;
}

:global(.dark-mode) .lang-label {
  color: #c9d1d9;
}

:global(.dark-mode) .copy-btn {
  color: #8b949e;
}

:global(.dark-mode) .copy-btn:hover {
  color: #c9d1d9;
}

/* 强制让 Shiki 的 pre 背景透明，以便显示我们容器的背景 */
:deep(pre.shiki) {
  background-color: transparent !important;
  margin: 0;
  padding: 0;
}
</style>

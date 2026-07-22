<script setup lang="ts">
import { computed } from 'vue';
import { VueMarkdownRenderer } from 'vue-mdr';
import CodeBlock from '@/components/CodeBlock.vue';
import 'katex/dist/katex.min.css';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import java from '@shikijs/langs/java';
import { useTheme } from '@/composables/useTheme';
import { safeMarkdownPlugin } from '@/utils/safeMarkdown';

defineProps<{
  source: string;
}>();

const { theme } = useTheme();
const currentTheme = computed((): 'light' | 'dark' => theme.value);
const extraLangs = [java];
const remarkPlugins = [remarkMath];
const rehypePlugins = [rehypeKatex as any, safeMarkdownPlugin];
const remarkRehypeOptions = { allowDangerousHtml: false };
</script>

<template>
  <VueMarkdownRenderer
    :source="source"
    :theme="currentTheme"
    :code-block-renderer="CodeBlock"
    :extra-langs="extraLangs"
    :remark-plugins="remarkPlugins"
    :rehype-plugins="rehypePlugins"
    :remark-rehype-options="remarkRehypeOptions"
  />
</template>

<style scoped>
:deep(.markdown-image-alt) {
  color: var(--chat-text-muted, #64748b);
  font-style: italic;
}
</style>

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
  /* `--chat-muted` is the token `ChatView` actually declares. This read `--chat-text-muted`, which is
     defined nowhere — a name that never existed, held up by its own fallback. It happened to render the
     right colour because `--chat-muted` resolves to `var(--text-muted)` too, so the typo was invisible;
     it would have surfaced the first time the chat panel's muted tone diverged from the page's. */
  color: var(--chat-muted);
  font-style: italic;
}
</style>

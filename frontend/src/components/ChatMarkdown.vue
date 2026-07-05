<script setup lang="ts">
import { computed } from 'vue';
import { VueMarkdownRenderer } from 'vue-mdr';
import CodeBlock from '@/components/CodeBlock.vue';
import 'katex/dist/katex.min.css';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import java from '@shikijs/langs/java';
import { useTheme } from '@/composables/useTheme';

defineProps<{
  source: string;
}>();

const { theme } = useTheme();
const currentTheme = computed((): 'light' | 'dark' => theme.value);
const extraLangs = [java];
const remarkPlugins = [remarkMath];
const rehypePlugins = [rehypeKatex as any];
</script>

<template>
  <VueMarkdownRenderer
    :source="source"
    :theme="currentTheme"
    :code-block-renderer="CodeBlock"
    :extra-langs="extraLangs"
    :remark-plugins="remarkPlugins"
    :rehype-plugins="rehypePlugins"
  />
</template>

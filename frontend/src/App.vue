<script setup lang="ts">
import Header from "./components/Header.vue";
import ChatbotBall from "@/components/ChatbotBall.vue";
</script>

<template>
  <div class="app-layout">
    <header class="app-header">
      <Header />
    </header>

    <main class="app-main">
      <router-view />
      <ChatbotBall />
    </main>
  </div>
</template>

<style scoped>
.app-layout {
  height: 100vh;              /* 整个应用占满视口 */
  display: flex;
  flex-direction: column;
}

/* 头部不参与滚动，高度由内容撑开即可 */
.app-header {
  flex: 0 0 auto;
}

/* 下面这一块才是可以滚动的区域 */
.app-main {
  flex: 1 1 auto;
  overflow: auto;
}
</style>
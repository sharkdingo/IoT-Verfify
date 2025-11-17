<script setup lang="ts">
import Header from "./components/Header.vue";
</script>

<template>
  <div class="app-layout">
    <header class="app-header">
      <Header />
    </header>

    <main class="app-main">
      <router-view />
    </main>
  </div>
</template>

<style scoped>
</style>
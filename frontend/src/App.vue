<script setup lang="ts">
import Header from "./components/Header.vue";
import ChatView from "./components/ChatView.vue";
import {ref} from "vue";
import { useRoute } from "vue-router";

const route = useRoute();
const routerViewRef = ref<any>(null);
const handleSystemCommand = (cmd: any) => {
  console.log("App收到指令:", cmd);

  if (cmd.type === 'REFRESH_DATA') {
    // 判断目标是不是 device_list，且当前路由组件是否有 refreshDevices 方法
    if (cmd.payload?.target === 'device_list') {
      // 🚀 使用可选链调用，因为当前页面可能不是 Board，或者还没加载完
      if (routerViewRef.value && typeof routerViewRef.value.refreshDevices === 'function') {
        routerViewRef.value.refreshDevices();
      } else {
        console.warn("当前页面无法响应 refreshDevices 指令");
      }
    }
  }

  // 处理其他指令...
  if (cmd.type === 'NAVIGATE') {
    // router.push(...)
  }
};
</script>

<template>
  <div class="app-layout">
    <header v-if="route.path !== '/create-template'" class="app-header">
      <Header />
    </header>

    <main class="app-main">
      <router-view v-slot="{ Component }">
        <keep-alive>
          <component :is="Component" ref="routerViewRef" />
        </keep-alive>
      </router-view>

      <ChatView @command="handleSystemCommand" />
    </main>
  </div>
</template>

<style scoped>
.app-layout {
  min-height: 100vh;              /* 改为最小高度，允许内容撑开 */
  display: flex;
  flex-direction: column;
}

/* 头部不参与滚动，高度由内容撑开即可 */
.app-header {
  flex: 0 0 auto;
}

/* 页面主内容区 */
.app-main {
  flex: 1 1 auto;
  display: flex;
  flex-direction: column;
}
</style>

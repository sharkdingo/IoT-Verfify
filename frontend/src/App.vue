<script setup lang="ts">
import Header from "./components/Header.vue";
import ChatView from "./components/ChatView.vue";
import { ref, computed } from "vue";
import { useRoute } from "vue-router";
import type { StreamCommand } from "@/types/chat";

const route = useRoute();
const routerViewRef = ref<any>(null);

const isAuthPage = computed(() => {
  return route.path === '/login' || route.path === '/register';
});

const invokeViewMethod = async (methodName: string) => {
  const view = routerViewRef.value;
  if (!view || typeof view[methodName] !== 'function') {
    console.warn(`Current view does not support command method: ${methodName}`);
    return;
  }
  await view[methodName]();
};

const handleSystemCommand = async (cmd: StreamCommand) => {
  console.log("App received command:", cmd);

  if (cmd.type === 'REFRESH_DATA') {
    const target = cmd.payload?.target as string | undefined;
    if (!target) {
      return;
    }

    switch (target) {
      case 'device_list':
        await invokeViewMethod('refreshDevices');
        break;
      case 'rule_list':
        await invokeViewMethod('refreshRules');
        break;
      case 'spec_list':
        await invokeViewMethod('refreshSpecifications');
        break;
      case 'template_list':
        await invokeViewMethod('refreshDeviceTemplates');
        break;
      default:
        console.warn(`Unsupported REFRESH_DATA target: ${target}`);
    }
    return;
  }

  if (cmd.type === 'NAVIGATE') {
    // router.push(...)
  }
};
</script>

<template>
  <div class="app-layout">
    <header v-if="!isAuthPage" class="app-header">
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
  min-height: 100vh;
  display: flex;
  flex-direction: column;
}

.app-header {
  flex: 0 0 auto;
}

.app-main {
  flex: 1 1 auto;
  display: flex;
  flex-direction: column;
}
</style>

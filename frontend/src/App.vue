<script setup lang="ts">
import { ref, computed, defineAsyncComponent } from "vue";
import { useRoute } from "vue-router";
import type { StreamCommand } from "@/types/chat";
import { useChatStore } from "@/stores/chat";

const route = useRoute();
const routerViewRef = ref<any>(null);
const Header = defineAsyncComponent(() => import("./components/Header.vue"));
const ChatView = defineAsyncComponent(() => import("./components/ChatView.vue"));
const chatStore = useChatStore();

const showAppHeader = computed(() => !route.meta.public && !route.meta.usesOwnHeader);
const shouldMountChat = computed(() => !route.meta.public && chatStore.state.visible);

const invokeViewMethod = async (methodName: string) => {
  const view = routerViewRef.value;
  if (!view || typeof view[methodName] !== 'function') {
    console.warn(`Current view does not support command method: ${methodName}`);
    return;
  }
  await view[methodName]();
};

const handleSystemCommand = async (cmd: StreamCommand) => {
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
    <header v-if="showAppHeader" class="app-header">
      <Header />
    </header>

    <main class="app-main">
      <router-view v-slot="{ Component }">
        <keep-alive>
          <component :is="Component" ref="routerViewRef" />
        </keep-alive>
      </router-view>

      <ChatView v-if="shouldMountChat" @command="handleSystemCommand" />
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

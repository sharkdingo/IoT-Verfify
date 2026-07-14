<script setup lang="ts">
import { ref, computed, defineAsyncComponent, watch } from "vue";
import { useRoute } from "vue-router";
import type { StreamCommand } from "@/types/chat";
import { useChatStore } from "@/stores/chat";

const route = useRoute();
const routerViewRef = ref<any>(null);
const ChatView = defineAsyncComponent(() => import("./components/ChatView.vue"));
const chatStore = useChatStore();

// Load the assistant lazily on first open, then keep it mounted while hidden. Closing a
// floating panel must not discard the selected conversation or abort an active stream.
const hasMountedChat = ref(false);
watch(() => chatStore.state.visible, visible => {
  if (visible) hasMountedChat.value = true;
}, { immediate: true });
const shouldMountChat = computed(() => !route.meta.public && hasMountedChat.value);
const isBoardChat = computed(() => route.name === 'board');
const isBoardChatInteractionLocked = computed(() => {
  const view = routerViewRef.value;
  return isBoardChat.value
    && typeof view?.isChatInteractionLocked === 'function'
    && Boolean(view.isChatInteractionLocked());
});

const getBoardChatContext = () => {
  const view = routerViewRef.value;
  if (!view || typeof view.getChatSuggestionContext !== 'function') {
    return null;
  }
  return view.getChatSuggestionContext();
};

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
      case 'environment_list':
        await invokeViewMethod('refreshEnvironmentVariables');
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
      case 'run_history':
        await invokeViewMethod('refreshRunHistory');
        break;
      case 'board_state':
        await invokeViewMethod('refreshAllBoardState');
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
    <main class="app-main">
      <router-view v-slot="{ Component }">
        <keep-alive>
          <component :is="Component" ref="routerViewRef" />
        </keep-alive>
      </router-view>

      <ChatView
        v-if="shouldMountChat"
        :board-mode="isBoardChat"
        :get-board-context="getBoardChatContext"
        :interaction-locked="isBoardChatInteractionLocked"
        @command="handleSystemCommand"
      />
    </main>
  </div>
</template>

<style scoped>
.app-layout {
  min-height: 100vh;
  display: flex;
  flex-direction: column;
}

.app-main {
  flex: 1 1 auto;
  display: flex;
  flex-direction: column;
}
</style>

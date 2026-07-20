<script setup lang="ts">
import { ref, computed, defineAsyncComponent, watch } from "vue";
import { useRoute } from "vue-router";
import type { ChatLogoutPreparation, StreamCommand } from "@/types/chat";
import { useChatStore } from "@/stores/chat";
import { useAuth } from "@/stores/auth";
import { publishBoardInvalidation } from "@/utils/boardInvalidation";
import AppErrorBoundary from "./components/AppErrorBoundary.vue";

const route = useRoute();
const routerViewRef = ref<any>(null);
const chatViewRef = ref<any>(null);
const ChatView = defineAsyncComponent(() => import("./components/ChatView.vue"));
const chatStore = useChatStore();
const { getUser } = useAuth();

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

const invokeViewMethod = async (methodName: string): Promise<boolean> => {
  const view = routerViewRef.value;
  if (!view || typeof view[methodName] !== 'function') {
    console.warn(`Current view does not support command method: ${methodName}`);
    return false;
  }
  return await view[methodName]() !== false;
};

const invokeBoardRefresh = async (methodName: string): Promise<boolean> => {
  const refreshed = await invokeViewMethod(methodName);
  if (refreshed) publishBoardInvalidation(getUser()?.userId, 'chat-tool');
  return refreshed;
};

const handleSystemCommand = async (cmd: StreamCommand): Promise<boolean> => {
  if (cmd.type === 'REFRESH_DATA') {
    const target = cmd.payload?.target as string | undefined;
    if (!target) {
      return false;
    }

    switch (target) {
      case 'device_list':
        return await invokeBoardRefresh('refreshDevices');
      case 'environment_list':
        return await invokeBoardRefresh('refreshEnvironmentVariables');
      case 'rule_list':
        return await invokeBoardRefresh('refreshRules');
      case 'spec_list':
        return await invokeBoardRefresh('refreshSpecifications');
      case 'template_list':
        return await invokeBoardRefresh('refreshDeviceTemplates');
      case 'run_history':
        return await invokeViewMethod('refreshRunHistory');
      case 'board_state':
        return await invokeBoardRefresh('refreshAllBoardState');
      default:
        console.warn(`Unsupported REFRESH_DATA target: ${target}`);
        return false;
    }
  }

  if (cmd.type === 'NAVIGATE') {
    // router.push(...)
    return false;
  }
  return false;
};

const prepareChatForLogout = async (): Promise<ChatLogoutPreparation> => {
  const view = chatViewRef.value;
  if (!view || typeof view.prepareForLogout !== 'function') return 'ready';
  return await view.prepareForLogout();
};

const routerViewProps = computed(() => isBoardChat.value
  ? { prepareChatForLogout }
  : {});
</script>

<template>
  <div class="app-layout">
    <main class="app-main">
      <router-view v-slot="{ Component }">
        <AppErrorBoundary :reset-key="route.fullPath">
          <component :is="Component" ref="routerViewRef" v-bind="routerViewProps" />
        </AppErrorBoundary>
      </router-view>

      <AppErrorBoundary v-if="shouldMountChat" :reset-key="route.fullPath">
        <ChatView
          ref="chatViewRef"
          :board-mode="isBoardChat"
          :get-board-context="getBoardChatContext"
          :interaction-locked="isBoardChatInteractionLocked"
          :execute-command="handleSystemCommand"
        />
      </AppErrorBoundary>
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

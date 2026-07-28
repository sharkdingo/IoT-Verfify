<script setup lang="ts">
import { ref, computed, defineAsyncComponent, watch } from "vue";
import { useRoute, useRouter } from "vue-router";
import type { ChatLogoutPreparation, StreamCommand } from "@/types/chat";
import { useChatStore } from "@/stores/chat";
import { useAuth } from "@/stores/auth";
import { publishBoardInvalidation } from "@/utils/boardInvalidation";
import AppErrorBoundary from "./components/AppErrorBoundary.vue";
import { loginRedirectTarget } from "@/router/loginRedirect";
import { isNavigationInProgress } from "@/router";
import {
  assistantRefreshEffects,
  isAssistantRefreshTarget
} from "@/views/board/assistantRefresh";

const route = useRoute();
const router = useRouter();
const routerViewRef = ref<any>(null);
const chatViewRef = ref<any>(null);
const ChatView = defineAsyncComponent(() => import("./components/ChatView.vue"));
const chatStore = useChatStore();
const { state: authState, getUser } = useAuth();

// Authentication is a hard ownership boundary. Remount private route components when
// the subject changes so no request, timer, or subscription from the previous account
// can write into the next account's workspace.
//
// Keyed on the route *identity*, not `fullPath`: query params address content within a
// view (e.g. the board's open run), and remounting on every param change would discard
// the view's state and re-run its whole load — the very state the URL is meant to restore.
const routeAuthScopeKey = computed(() =>
  `${String(route.name ?? route.path)}:${route.meta.public ? 'public' : (authState.user?.userId ?? 'anonymous')}`
);
const canRenderCurrentRoute = computed(() => Boolean(route.meta.public) || authState.isLoggedIn);

watch(() => authState.isLoggedIn, authenticated => {
  if (authenticated || route.meta.public) return;
  // The route guard's own `revalidateSession()` flips this flag mid-navigation; it resolves the
  // redirect from the *incoming* route itself, so stepping in here would use the stale current route
  // and abort the navigation it is already handling.
  if (isNavigationInProgress()) return;
  const target = loginRedirectTarget(route);
  if (target) void router.replace(target);
}, { flush: 'sync' });

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
    const target = cmd.payload?.target;
    // An unknown target is a contract mismatch, not something to guess at.
    if (!isAssistantRefreshTarget(target)) {
      if (target) console.warn(`Unsupported REFRESH_DATA target: ${String(target)}`);
      return false;
    }

    // One table owns which board method a target reloads and whether it changed persisted state,
    // so this dispatch and the board's own follow-ups cannot disagree.
    const effects = assistantRefreshEffects(target);
    return effects.invalidatesOtherTabs
      ? await invokeBoardRefresh(effects.method)
      : await invokeViewMethod(effects.method);
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
        <AppErrorBoundary :reset-key="routeAuthScopeKey">
          <component
            v-if="canRenderCurrentRoute"
            :is="Component"
            :key="routeAuthScopeKey"
            ref="routerViewRef"
            v-bind="routerViewProps"
          />
        </AppErrorBoundary>
      </router-view>

      <AppErrorBoundary v-if="shouldMountChat" :reset-key="routeAuthScopeKey">
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

<script setup lang="ts">
import { ref, computed, defineAsyncComponent, onMounted, onUnmounted, watch } from "vue";
import { useRoute, useRouter } from "vue-router";
import type { ChatLogoutPreparation, StreamCommand } from "@/types/chat";
import { useChatStore } from "@/stores/chat";
import { useAuth } from "@/stores/auth";
import { getSessionActivity, getSessionList, requestSessionStop } from "@/api/chat";
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
// Once ChatView has mounted it owns the session projection, including while its panel is hidden.
// App only fills the pre-mount gap so the two components never reconcile the same completion.
const hasMountedChat = ref(false);

let chatSessionStateRequestEpoch = 0;
let hiddenChatStateTimer: number | null = null;
let assistantSessionStateUserId: number | null = null;
type HiddenAssistantObservation = {
  active: boolean;
  latestTerminalMessageId: number | null;
};
let hiddenAssistantObservations = new Map<string, HiddenAssistantObservation>();
let hiddenAssistantObservationsInitialized = false;
const pendingAssistantReconciliationKeys = new Set<string>();
let hiddenAssistantReconciliationPromise: Promise<boolean> | null = null;
let executeHiddenAssistantReconciliation: () => Promise<boolean> = async () => false;

const resetHiddenAssistantSessionState = (userId: number | null) => {
  assistantSessionStateUserId = userId;
  hiddenAssistantObservations = new Map();
  hiddenAssistantObservationsInitialized = false;
  pendingAssistantReconciliationKeys.clear();
  hiddenAssistantReconciliationPromise = null;
};

const reconcileHiddenAssistantCompletions = async (userId: number) => {
  if (pendingAssistantReconciliationKeys.size === 0
      || hiddenAssistantReconciliationPromise) return;
  const completionKeys = new Set(pendingAssistantReconciliationKeys);
  chatStore.setReconciliationRequired(true);
  const ownedReconciliation = executeHiddenAssistantReconciliation();
  hiddenAssistantReconciliationPromise = ownedReconciliation;
  try {
    const reconciled = await ownedReconciliation;
    if (!reconciled || assistantSessionStateUserId !== userId
        || authState.user?.userId !== userId || route.meta.public) return;
    completionKeys.forEach(completionKey =>
      pendingAssistantReconciliationKeys.delete(completionKey));
    if (pendingAssistantReconciliationKeys.size === 0) {
      chatStore.setReconciliationRequired(false);
    }
  } catch (error) {
    console.warn('Could not reconcile a completed background assistant session:', error);
  } finally {
    if (hiddenAssistantReconciliationPromise === ownedReconciliation) {
      hiddenAssistantReconciliationPromise = null;
    }
  }
};

const refreshChatSessionState = async () => {
  const userId = authState.user?.userId ?? null;
  const requestEpoch = ++chatSessionStateRequestEpoch;
  if (userId === null || route.meta.public) {
    resetHiddenAssistantSessionState(null);
    chatStore.setActiveCount(0);
    chatStore.setUnreadCount(0);
    chatStore.setReconciliationRequired(false);
    chatStore.setStreaming(false);
    return;
  }
  if (assistantSessionStateUserId !== userId) {
    resetHiddenAssistantSessionState(userId);
    chatStore.setActiveCount(0);
    chatStore.setUnreadCount(0);
    chatStore.setReconciliationRequired(false);
  }
  if (hasMountedChat.value) return;
  try {
    const sessions = await getSessionList();
    if (requestEpoch !== chatSessionStateRequestEpoch || chatStore.state.visible
        || hasMountedChat.value
        || authState.user?.userId !== userId || route.meta.public) return;
    const ownedSessions = sessions.filter(session => session.userId === userId);
    const nextObservations = new Map(ownedSessions.map(session => [session.id, {
      active: session.active,
      latestTerminalMessageId: session.latestTerminalMessageId
    }]));
    if (hiddenAssistantObservationsInitialized) {
      nextObservations.forEach((observation, sessionId) => {
        const previous = hiddenAssistantObservations.get(sessionId);
        if (observation.latestTerminalMessageId !== null
            && observation.latestTerminalMessageId !== previous?.latestTerminalMessageId) {
          pendingAssistantReconciliationKeys.add(
            `${sessionId}:terminal:${observation.latestTerminalMessageId}`);
        }
      });
    } else {
      hiddenAssistantObservationsInitialized = true;
    }
    hiddenAssistantObservations.forEach((previous, sessionId) => {
      if (previous.active && nextObservations.get(sessionId)?.active !== true) {
        const terminalMessageId = nextObservations.get(sessionId)?.latestTerminalMessageId;
        pendingAssistantReconciliationKeys.add(terminalMessageId === undefined
          ? `${sessionId}:removed-while-active`
          : `${sessionId}:terminal:${terminalMessageId ?? 'missing'}`);
      }
    });
    hiddenAssistantObservations = nextObservations;
    const activeCount = ownedSessions.filter(session => session.active).length;
    chatStore.setActiveCount(activeCount);
    chatStore.setUnreadCount(ownedSessions.filter(session => session.hasUnreadUpdate).length);
    await reconcileHiddenAssistantCompletions(userId);
  } catch (error) {
    console.warn('Could not refresh assistant session state:', error);
  }
};

const refreshHiddenChatOnWindowFocus = () => {
  if (!chatStore.state.visible) void refreshChatSessionState();
};

const refreshHiddenChatOnVisibility = () => {
  if (!document.hidden && !chatStore.state.visible) void refreshChatSessionState();
};

watch(
  [() => authState.user?.userId ?? null, () => Boolean(route.meta.public)],
  () => void refreshChatSessionState(),
  { immediate: true }
);

watch(() => chatStore.state.reconciliationRequired, required => {
  const userId = authState.user?.userId;
  if (!required && !hasMountedChat.value
      && pendingAssistantReconciliationKeys.size > 0 && userId !== undefined
      && assistantSessionStateUserId === userId) {
    void reconcileHiddenAssistantCompletions(userId);
  }
});

onMounted(() => {
  window.addEventListener('focus', refreshHiddenChatOnWindowFocus);
  document.addEventListener('visibilitychange', refreshHiddenChatOnVisibility);
  hiddenChatStateTimer = window.setInterval(() => {
    if (!chatStore.state.visible && !route.meta.public) void refreshChatSessionState();
  }, 5000);
});

onUnmounted(() => {
  chatSessionStateRequestEpoch += 1;
  resetHiddenAssistantSessionState(null);
  if (hiddenChatStateTimer !== null) window.clearInterval(hiddenChatStateTimer);
  hiddenChatStateTimer = null;
  window.removeEventListener('focus', refreshHiddenChatOnWindowFocus);
  document.removeEventListener('visibilitychange', refreshHiddenChatOnVisibility);
});

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

const prepareBoardChatInteraction = (): boolean => {
  if (!isBoardChat.value) return true;
  const view = routerViewRef.value;
  if (typeof view?.prepareChatInteraction === 'function') {
    return view.prepareChatInteraction() !== false;
  }
  return !isBoardChatInteractionLocked.value;
};

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

executeHiddenAssistantReconciliation = () => isBoardChat.value
  ? handleSystemCommand({
      type: 'REFRESH_DATA',
      payload: { target: 'board_state' }
    })
  : Promise.resolve(false);

const prepareChatForLogout = async (): Promise<ChatLogoutPreparation> => {
  const view = chatViewRef.value;
  if (view && typeof view.prepareForLogout === 'function') {
    return await view.prepareForLogout();
  }

  // ChatView is lazy-mounted. Logout must still stop work started in another tab when this
  // tab never opened the panel, otherwise the UI would discard auth while the server keeps
  // mutating the user's Board.
  const userId = authState.user?.userId;
  if (userId === undefined || route.meta.public) return 'ready';
  let sessions;
  try {
    sessions = await getSessionList();
  } catch (error) {
    console.warn('Could not read assistant sessions before logout:', error);
    return 'outcome-unknown';
  }
  const activeSessionIds = sessions.filter(session => session.active).map(session => session.id);
  if (activeSessionIds.length === 0 && !chatStore.state.reconciliationRequired) return 'ready';

  const stopResults = await Promise.allSettled(activeSessionIds.map(sessionId =>
    requestSessionStop(sessionId, undefined, authState.token)));
  if (stopResults.some(result => result.status === 'rejected'
      && (result.reason?.response?.status !== 404))) {
    return 'outcome-unknown';
  }

  const deadline = Date.now() + 10_000;
  for (const sessionId of activeSessionIds) {
    let idle = false;
    while (Date.now() < deadline) {
      try {
        idle = !(await getSessionActivity(sessionId)).active;
        if (idle) break;
      } catch (error: any) {
        if (error?.response?.status === 404) {
          idle = true;
          break;
        }
        return 'outcome-unknown';
      }
      await new Promise(resolve => window.setTimeout(resolve, 500));
    }
    if (!idle) return 'outcome-unknown';
  }

  const reconciled = await executeHiddenAssistantReconciliation();
  if (!reconciled) return 'reconciliation-failed';
  chatStore.setReconciliationRequired(false);
  return 'ready';
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
          :prepare-interaction="prepareBoardChatInteraction"
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

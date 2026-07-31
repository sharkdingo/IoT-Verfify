// src/stores/chat.ts - Chat AI 助手全局状态管理
import { reactive, readonly } from 'vue';

interface ChatState {
  visible: boolean;
  streaming: boolean;
  activeCount: number;
  unreadCount: number;
  reconciliationRequired: boolean;
}

// 初始状态
const state = reactive<ChatState>({
  visible: false,
  streaming: false,
  activeCount: 0,
  unreadCount: 0,
  reconciliationRequired: false,
});

// 供外部使用
export const useChatStore = () => {
  // 切换显示/隐藏
  const toggleChat = () => {
    state.visible = !state.visible;
  };

  // 打开 AI 面板
  const openChat = () => {
    state.visible = true;
  };

  // 关闭 AI 面板
  const closeChat = () => {
    state.visible = false;
  };

  const setStreaming = (streaming: boolean) => {
    state.streaming = streaming;
  };

  const setActiveCount = (activeCount: number) => {
    state.activeCount = Math.max(0, Math.floor(activeCount));
  };

  const setUnreadCount = (unreadCount: number) => {
    state.unreadCount = Math.max(0, Math.floor(unreadCount));
  };

  const setReconciliationRequired = (required: boolean) => {
    state.reconciliationRequired = required;
  };

  return {
    state: readonly(state),
    toggleChat,
    openChat,
    closeChat,
    setStreaming,
    setActiveCount,
    setUnreadCount,
    setReconciliationRequired,
  };
};


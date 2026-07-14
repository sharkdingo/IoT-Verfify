// src/stores/chat.ts - Chat AI 助手全局状态管理
import { reactive, readonly } from 'vue';

interface ChatState {
  visible: boolean;
  streaming: boolean;
}

// 初始状态
const state = reactive<ChatState>({
  visible: false,
  streaming: false,
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

  return {
    state: readonly(state),
    toggleChat,
    openChat,
    closeChat,
    setStreaming,
  };
};


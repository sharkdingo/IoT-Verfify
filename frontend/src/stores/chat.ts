// src/stores/chat.ts - Chat AI 助手全局状态管理
import { reactive, readonly } from 'vue';

interface ChatState {
  visible: boolean;      // AI 面板是否显示
  isExpanded: boolean;    // 是否全屏展开
}

// 初始状态
const state = reactive<ChatState>({
  visible: false,
  isExpanded: false,
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

  // 切换全屏展开
  const toggleExpand = () => {
    state.isExpanded = !state.isExpanded;
  };

  // 设置展开状态
  const setExpanded = (expanded: boolean) => {
    state.isExpanded = expanded;
  };

  return {
    state: readonly(state),
    toggleChat,
    openChat,
    closeChat,
    toggleExpand,
    setExpanded,
  };
};


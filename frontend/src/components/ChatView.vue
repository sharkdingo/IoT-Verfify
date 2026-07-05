<script setup lang="ts">
import { defineAsyncComponent, nextTick, onUnmounted, ref, watch, computed } from 'vue';
import { useI18n } from 'vue-i18n';
import {
  ArrowsAltOutlined, AudioOutlined,
  CloseOutlined, DeleteOutlined,
  MessageOutlined, PlusOutlined, RobotOutlined, SendOutlined,
  ShrinkOutlined, UserOutlined, StopOutlined,
  MenuFoldOutlined, MenuUnfoldOutlined,
  CopyOutlined, ThunderboltOutlined, SafetyCertificateOutlined,
  CodeOutlined, ExperimentOutlined
} from '@ant-design/icons-vue';
import 'ant-design-vue/dist/reset.css';

import { ElMessage, ElMessageBox } from 'element-plus';
import 'element-plus/es/components/message/style/css';
import 'element-plus/es/components/message-box/style/css';

import type { ChatMessage, ChatSession, StreamCommand } from '@/types/chat';
import { ChatStreamError, createSession, deleteSession, getSessionHistory, getSessionList, sendStreamChat } from '@/api/chat';
import { useChatStore } from '@/stores/chat';

const emit = defineEmits(['command']);
const { t, locale } = useI18n();
const ChatMarkdown = defineAsyncComponent(() => import('@/components/ChatMarkdown.vue'));

// 使用全局状态
const chatStore = useChatStore();
const visible = computed(() => chatStore.state.visible);
const isExpanded = computed(() => chatStore.state.isExpanded);

const loadingRegex = /^(正在执行指令|Executing command)[.\s\n]*/;
const presetTasks = computed(() => [
  {
    icon: ThunderboltOutlined,
    title: t('app.chat.presetTasks.quickDevice.title'),
    desc: t('app.chat.presetTasks.quickDevice.desc'),
    text: t('app.chat.presetTasks.quickDevice.text')
  },
  {
    icon: SafetyCertificateOutlined,
    title: t('app.chat.presetTasks.verification.title'),
    desc: t('app.chat.presetTasks.verification.desc'),
    text: t('app.chat.presetTasks.verification.text')
  },
  {
    icon: ExperimentOutlined,
    title: t('app.chat.presetTasks.scenario.title'),
    desc: t('app.chat.presetTasks.scenario.desc'),
    text: t('app.chat.presetTasks.scenario.text')
  },
  {
    icon: CodeOutlined,
    title: t('app.chat.presetTasks.script.title'),
    desc: t('app.chat.presetTasks.script.desc'),
    text: t('app.chat.presetTasks.script.text')
  }
]);

// State - 使用全局状态，不重复定义
// visible 和 isExpanded 来自 chatStore (上面已定义)
const isSidebarOpen = ref(true);
const isRecording = ref(false);
const sessions = ref<ChatSession[]>([]);
const currentSessionId = ref<string>('');
const messages = ref<ChatMessage[]>([]);
const inputValue = ref('');
const isLoading = ref(false);
const scrollRef = ref<HTMLElement | null>(null);
const abortController = ref<AbortController | null>(null);

// 联动：全屏时自动展开侧边栏
watch(isExpanded, (newVal) => {
  isSidebarOpen.value = newVal;
});

// ================= 文本处理辅助函数 =================

const convertLatexDelimiters = (text: string) => {
  const pattern = /(```[\S\s]*?```|`.*?`)|\\\[([\S\s]*?[^\\])\\]|\\\((.*?)\\\)/g;
  return text.replace(pattern, (match, codeBlock, squareBracket, roundBracket) => {
    if (codeBlock !== undefined) return codeBlock;
    if (squareBracket !== undefined) return `$$${squareBracket}$$`;
    if (roundBracket !== undefined) return `$${roundBracket}$`;
    return match;
  });
};

const shouldShowMessage = (msg: ChatMessage) => {
  if (msg.role === 'tool') return false;
  // 兼容旧数据的过滤
  if (msg.content && msg.content.startsWith(':::TOOL_CALLS:::')) return false;
  return true;
};

const getRawContentWithoutThinking = (content: string) => {
  if (!content) return '';
  const match = content.match(loadingRegex);
  if (match) {
    const prefixLength = match[0].length;
    // 如果只有提示语，为了避免空内容，暂时返回提示语（或可返回空字符串让界面显示 Loading）
    if (content.length <= prefixLength) return content;
    return content.substring(prefixLength);
  }
  return content;
};

/**
 * 最终渲染内容的预处理
 */
const getProcessedContent = (content: string) => {
  if (!content) return '';
  // 1. 去除 Thinking 前缀
  let text = getRawContentWithoutThinking(content);
  // 2. 标准化 LaTeX
  return convertLatexDelimiters(text);
};

const copyFullMessage = async (content: string) => {
  try {
    const cleanContent = content.replace('CallEnd|>', '');
    await navigator.clipboard.writeText(cleanContent);
    ElMessage.success({ message: t('app.chat.copied'), zIndex: 30000 });
  } catch (err) {
    ElMessage.error(t('app.chat.copyFailed'));
  }
};

// ================= 交互逻辑 =================

const formatStreamError = (error: unknown) => {
  const message = error instanceof Error ? error.message : String(error);
  if (error instanceof ChatStreamError && error.serverFrame) {
    return message || 'Server stream error';
  }
  return message || 'Request failed';
};

const startListening = () => {
  const SpeechRecognition = (window as any).SpeechRecognition || (window as any).webkitSpeechRecognition;
  if (!SpeechRecognition) {
    ElMessage.warning(t('app.chat.speechUnsupported'));
    return;
  }
  if (isRecording.value) return;

  try {
    const recognition = new SpeechRecognition();
    recognition.lang = locale.value === 'zh-CN' ? 'zh-CN' : 'en-US';
    recognition.interimResults = false;
    recognition.maxAlternatives = 1;

    recognition.onstart = () => { isRecording.value = true; ElMessage.info(t('app.chat.startSpeaking')); };
    recognition.onend = () => { isRecording.value = false; };
    recognition.onerror = () => { isRecording.value = false; ElMessage.error(t('app.chat.speechError')); };
    recognition.onresult = (event: any) => {
      const transcript = event.results[0][0].transcript;
      if (transcript) inputValue.value += transcript;
    };
    recognition.start();
  } catch (e) {
    ElMessage.error(t('app.chat.speechStartFailed'));
    isRecording.value = false;
  }
};



// 监听 visible 变化，执行相应逻辑
watch(visible, (newVal) => {
  // 仅当首次打开且无会话时加载，避免重复请求
  if (newVal && sessions.value.length === 0) initSessions();
  // 每次打开时，如果不是全屏模式，默认收起侧边栏
  if (newVal && !isExpanded.value) isSidebarOpen.value = false;
});

const initSessions = async () => {
  try {
    const res = await getSessionList();
    if (Array.isArray(res)) sessions.value = res;
  } catch (e) { console.error(e); }
};

const handleCreateSession = async () => {
  try {
    const session = await createSession();
    if (session && session.id) {
      sessions.value.unshift(session);
      return session.id;
    }
    return null;
  } catch (e) {
    console.error('创建会话失败:', e);
    return null;
  }
};

const onNewChatClick = async () => {
  const newId = await handleCreateSession();
  if (newId) await handleSelectSession(newId);
  // 新建对话后自动收起侧边栏（移动端友好）
  if (!isExpanded.value) isSidebarOpen.value = false;
};

const handleDelete = async (sessionId: string) => {
  try {
    await ElMessageBox.confirm(
        t('app.chat.deleteSessionMessage'),
        t('app.chat.deleteSessionTitle'),
        { confirmButtonText: t('app.delete'), cancelButtonText: t('app.cancel'), type: 'warning', lockScroll: false, appendTo: 'body' }
    );
    await deleteSession(sessionId);
    sessions.value = sessions.value.filter(s => s.id !== sessionId);
    if (currentSessionId.value === sessionId) {
      currentSessionId.value = '';
      messages.value = [];
    }
    ElMessage.success(t('app.chat.sessionDeleted'));
  } catch (error) { if (error !== 'cancel') ElMessage.error(t('app.chat.deleteFailed')); }
};

const handleSelectSession = async (sessionId: string) => {
  if (currentSessionId.value === sessionId) return;

  // 切换会话时，中断上一次的请求
  abortActiveRequest(false);

  currentSessionId.value = sessionId;
  messages.value = [];
  isLoading.value = true;

  // 移动端体验优化：选中后收起侧边栏
  if (!isExpanded.value) isSidebarOpen.value = false;

  try {
    const messagesData = await getSessionHistory(sessionId);
    // 统一清洗历史消息中的脏数据
    messages.value = messagesData.map(m => ({
      ...m,
      content: m.content ? m.content.replace('CallEnd|>', '') : ''
    }));
    scrollToBottom(true);
  } catch (e) { ElMessage.error(t('app.chat.networkError')); } finally { isLoading.value = false; }
};

const markActiveAssistantAsCancelled = () => {
  const lastMessage = messages.value[messages.value.length - 1];
  if (lastMessage?.role === 'assistant' && !lastMessage.content?.trim()) {
    lastMessage.content = t('app.chat.cancelled');
    scrollToBottom(false);
  }
};

const abortActiveRequest = (showCancelledMessage = false) => {
  if (abortController.value) {
    abortController.value.abort();
    abortController.value = null;
    isLoading.value = false;
    if (showCancelledMessage) {
      markActiveAssistantAsCancelled();
    }
  }
};

const handleStop = () => {
  abortActiveRequest(true);
};

onUnmounted(() => {
  abortActiveRequest(false);
});

const handleSend = async () => {
  const content = inputValue.value.trim();
  if (!content || isLoading.value) return;

  inputValue.value = '';
  messages.value.push({role: 'user', content});
  scrollToBottom(true);

  isLoading.value = true;
  abortController.value = new AbortController();

  // 用于跟踪是否收到了任何内容
  let hasReceivedContent = false;
  let streamErrorHandled = false;
  let aiMsgIndex = -1;

  try {
    let targetSessionId = currentSessionId.value;
    // 自动创建新会话
    if (!targetSessionId) {
      const newId = await handleCreateSession();
      if (!newId) throw new Error(t('app.chat.createSessionFailed'));
      targetSessionId = newId;
      currentSessionId.value = targetSessionId;
    }

    // 先插入一条空的 AI 消息占位
    aiMsgIndex = messages.value.push({role: 'assistant', content: ''}) - 1;
    scrollToBottom(true);

    const renderStreamError = (error: unknown) => {
      streamErrorHandled = true;
      const msg = messages.value[aiMsgIndex];
      if (!msg) return;

      const prefix = error instanceof ChatStreamError && error.serverFrame
          ? t('app.chat.serverError')
          : t('app.chat.requestFailed');
      const errorText = `${prefix}: ${formatStreamError(error)}`;
      if (hasReceivedContent && msg.content) {
        msg.content += `\n\n> ${errorText}`;
      } else {
        msg.content = errorText;
        hasReceivedContent = true;
      }
      scrollToBottom(false);
    };

    await sendStreamChat(
        targetSessionId,
        content,
        {
          onMessage: (chunk) => {
            const cleanChunk = chunk.replace('CallEnd|>', '');
            if (!cleanChunk) return;

            hasReceivedContent = true;
            const msg = messages.value[aiMsgIndex];
            // 直接追加，渲染器会自动处理 Markdown 格式
            msg.content += cleanChunk;
            scrollToBottom(false);
          },
          onCommand: (cmd: StreamCommand) => {
            emit('command', cmd); // 转发指令emit
          },
          onError: (err: any) => {
            renderStreamError(err);
            console.error('[Chat] 流式错误:', err);
          },
          onFinish: async () => {
            isLoading.value = false;
            abortController.value = null;
            // 刷新会话列表（更新时间/标题）
            await initSessions();
          }
        },
        abortController.value
    );
  } catch (error) {
    console.error('[Chat] 发送消息失败:', error);
    // 只有在没有收到内容时才显示错误提示
    if (!streamErrorHandled && !hasReceivedContent) {
      ElMessage.error(t('app.chat.sendFailedWithReason', {
        reason: error instanceof Error ? error.message : String(error)
      }));
    }
    isLoading.value = false;
    abortController.value = null;
  }
};

const handleTaskClick = (text: string) => {
  inputValue.value = text;
  // 可选：聚焦输入框 (如果 textarea 组件有 ref)
  // const textarea = document.querySelector('.modern-textarea') as HTMLTextAreaElement;
  // if (textarea) textarea.focus();
};

const scrollToBottom = (force = false) => {
  nextTick(() => {
    if (!scrollRef.value) return;
    const { scrollTop, scrollHeight, clientHeight } = scrollRef.value;
    // 只有当用户确实在底部，或者强制滚动时，才自动滚动。防止用户回看历史时被强制拉回底部。
    const isNearBottom = scrollHeight - scrollTop - clientHeight < 150;
    if (force || isNearBottom) scrollRef.value.scrollTop = scrollHeight;
  });
};
</script>

<template>
  <div class="global-chat-wrapper">

    <transition name="panel-zoom">
      <div v-show="visible" :class="['chat-panel', { expanded: isExpanded }]">

        <div :class="['sidebar', { collapsed: !isSidebarOpen }]">
          <div class="sidebar-header">
            <button class="new-chat-btn" @click="onNewChatClick">
              <PlusOutlined/> <span class="btn-label">{{ t('app.chat.newChat') }}</span>
            </button>
          </div>

          <div class="session-list">
            <div
                v-for="session in sessions"
                :key="session.id"
                :class="['session-item', { active: currentSessionId === session.id }]"
                @click="handleSelectSession(session.id)"
            >
              <MessageOutlined class="item-icon"/>
              <span class="item-title">{{ session.title || t('app.chat.newChat') }}</span>
              <div class="delete-btn-wrapper" @click.stop="handleDelete(session.id)">
                <DeleteOutlined class="delete-icon"/>
              </div>
            </div>
          </div>

          <div class="sidebar-footer">
            <!-- 移除深色模式切换功能 -->
          </div>
        </div>

        <div class="main-content">
          <div class="glass-header">
            <div class="header-left-group">
              <component
                  :is="isSidebarOpen ? MenuFoldOutlined : MenuUnfoldOutlined"
                  class="control-icon sidebar-toggle"
                  @click="isSidebarOpen = !isSidebarOpen"
              />
              <div class="header-title">
                <span class="logo-emoji">💬</span> {{ t('app.chat.onlineSupport') }}
              </div>
            </div>
            <div class="header-controls">
              <component
                  :is="isExpanded ? ShrinkOutlined : ArrowsAltOutlined"
                  class="control-icon"
                  @click="chatStore.toggleExpand()"
              />
              <CloseOutlined class="control-icon close-icon" @click="chatStore.closeChat()"/>
            </div>
          </div>

          <div class="messages-viewport" ref="scrollRef">
            <div v-if="messages.length === 0" class="welcome-screen">
              <div class="brand-logo">
                <div class="logo-inner">
                  <img src="/AI.png" :alt="t('app.aiAssistant')" class="custom-logo-img" />
                </div>
              </div>
              <h3 class="welcome-title">{{ t('app.chat.welcomeTitle') }}</h3>
              <p class="welcome-subtitle">{{ t('app.chat.welcomeSubtitle') }}</p>

              <div class="task-grid">
                <div
                    v-for="(task, index) in presetTasks"
                    :key="index"
                    class="task-card"
                    @click="handleTaskClick(task.text)"
                    :style="{ animationDelay: `${index * 0.1}s` }"
                >
                  <div class="task-icon">
                    <component :is="task.icon" />
                  </div>
                  <div class="task-info">
                    <div class="task-title">{{ task.title }}</div>
                    <div class="task-desc">{{ task.desc }}</div>
                  </div>
                </div>
              </div>
            </div>

            <template v-for="(msg, index) in messages" :key="index">
              <div v-if="shouldShowMessage(msg)" :class="['msg-row', msg.role === 'user' ? 'user-row' : 'ai-row']">
                <div class="avatar-container">
                  <UserOutlined v-if="msg.role === 'user'"/>
                  <RobotOutlined v-else/>
                </div>

                <div class="msg-content-wrapper">
                  <div v-if="msg.role === 'user'" class="msg-body user-msg-body">
                    {{ msg.content }}
                  </div>

                  <article v-else class="msg-body vue-markdown-wrapper">
                    <ChatMarkdown :source="getProcessedContent(msg.content) || ''" />
                  </article>

                  <div v-if="msg.role === 'assistant' && msg.content && !isLoading" class="msg-actions">
                    <div class="action-btn-small" @click="copyFullMessage(msg.content)" :title="t('app.chat.copyAll')">
                      <CopyOutlined />
                    </div>
                  </div>

                  <div v-if="isLoading && msg.role === 'assistant' && !msg.content" class="thinking-state">
                    <span class="thinking-text">{{ t('app.chat.thinking') }}</span>
                    <div class="typing-indicator"><span></span><span></span><span></span></div>
                  </div>
                </div>
              </div>
            </template>
            <div class="scroll-spacer"></div>
          </div>

          <div class="input-floating-area">
            <div class="input-card">
              <a-textarea
                  v-model:value="inputValue"
                  :placeholder="t('app.chat.inputPlaceholder')"
                  :auto-size="{ minRows: 1, maxRows: 5 }"
                  @keydown.ctrl.enter="handleSend"
                  class="modern-textarea"
              />
              <div class="input-actions">
                <div class="left-tools">
                  <div :class="['tool-icon', { active: isRecording }]" @click="startListening">
                    <AudioOutlined/>
                  </div>
                </div>
                <div class="right-tools">
                  <button v-if="isLoading" class="action-btn stop" @click="handleStop"><StopOutlined/></button>
                  <button v-else class="action-btn send" @click="handleSend" :disabled="!inputValue.trim()"><SendOutlined/></button>
                </div>
              </div>
            </div>
          </div>
        </div>
      </div>
    </transition>
  </div>
</template>

<style>
/* 1. 覆盖 Element UI 层级 */
.el-overlay, .el-message-box__wrapper, .el-message { z-index: 20002 !important; }

/* 2. 核心：流式渲染动画 */
.vue-markdown-wrapper > *,
.vue-markdown-wrapper .text-segmenter,
.vue-markdown-wrapper .shiki-stream span {
  animation: fade-in 0.5s ease-in-out;
}
@keyframes fade-in {
  0% { opacity: 0; transform: translateY(5px); }
  100% { opacity: 1; transform: translateY(0); }
}

/* 3. Markdown 内容样式 */
.vue-markdown-wrapper table {
  border-collapse: collapse;
  width: 100%;
  margin: 12px 0;
  font-size: 14px;
}
.vue-markdown-wrapper th,
.vue-markdown-wrapper td {
  border: 1px solid var(--border);
  padding: 8px 12px;
  text-align: left;
}
.vue-markdown-wrapper th {
  background-color: rgba(0,0,0,0.05);
  font-weight: 600;
}
.vue-markdown-wrapper p {
  margin-bottom: 0.8em;
  line-height: 1.6;
}
</style>

<style scoped>
/* ================= 1. 变量定义 (CSS Variables) ================= */
.global-chat-wrapper {
  /* 基础颜色 */
  --primary-color: #1677ff;
  --highlight-color: #10a37f;

  /* 浅色模式 */
  --bg-app: #ffffff;
  --bg-sidebar: #f7f7f8;
  --bg-input: #ffffff;
  --text-main: #343541;
  --text-sub: #8e8ea0;
  --border: #e5e5e5;
  --shadow-card: 0 0 15px rgba(0,0,0,0.08);
  --bubble-user-bg: #f3f3f3;

  /* 定位 */
  position: fixed;
  z-index: 9999;
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
}

:global(:root[data-theme='dark']) .global-chat-wrapper {
  --bg-app: #111827;
  --bg-sidebar: #0f172a;
  --bg-input: #020617;
  --text-main: #f8fafc;
  --text-sub: #94a3b8;
  --border: #334155;
  --shadow-card: 0 16px 48px rgba(2, 6, 23, 0.38);
  --bubble-user-bg: #1e293b;
}

/* ================= 2. 聊天主面板 (Panel) ================= */
.chat-panel {
  position: fixed;
  bottom: 90px;
  right: 30px;
  width: 420px;
  height: 600px;
  background: var(--bg-app);
  border-radius: 12px;
  box-shadow: 0 12px 40px rgba(0,0,0,0.15);
  border: 1px solid var(--border);
  display: flex;
  overflow: hidden;
  transition: all 0.4s cubic-bezier(0.25, 1, 0.5, 1);
}

/* 响应式展开状态 */
.chat-panel.expanded {
  width: 90vw;
  height: 92vh;
  bottom: 4vh;
  right: 5vw;
  max-width: 1400px;
  border-radius: 10px;
}

/* 移动端全屏 */
@media (max-width: 480px) {
  .chat-panel { width: 100vw; height: 100vh; bottom: 0; right: 0; border-radius: 0; }
}

.panel-zoom-enter-active, .panel-zoom-leave-active { transition: opacity 0.3s, transform 0.3s; }
.panel-zoom-enter-from, .panel-zoom-leave-to { opacity: 0; transform: translateY(20px) scale(0.95); }

/* ================= 4. 侧边栏 (Sidebar) ================= */
.sidebar {
  width: clamp(160px, 25%, 300px); /* 响应式宽度：最小160，最大300，占比25% */
  background: var(--bg-sidebar);
  border-right: 1px solid var(--border);
  display: flex;
  flex-direction: column;
  transition: width 0.3s ease, padding 0.3s ease, opacity 0.2s ease;
  overflow: hidden;
  white-space: nowrap;
}
.sidebar.collapsed { width: 0; padding: 0; border-right: none; opacity: 0; }

.sidebar-header { padding: 14px; }
.new-chat-btn { width: 100%; padding: 10px; background: transparent; border: 1px solid var(--border); border-radius: 6px; cursor: pointer; display: flex; align-items: center; gap: 8px; color: var(--text-main); font-size: 14px; transition: background 0.2s; }
.new-chat-btn:hover { background: rgba(0,0,0,0.05); }

.session-list { flex: 1; overflow-y: auto; padding: 0 8px; }
.session-item { padding: 10px; margin-bottom: 2px; border-radius: 6px; color: var(--text-main); font-size: 14px; cursor: pointer; display: flex; align-items: center; justify-content: space-between; }
.session-item:hover { background: rgba(0,0,0,0.05); }
.session-item.active { background: rgba(0,0,0,0.08); }
.item-title { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; flex: 1; margin-left: 10px; }
.delete-btn-wrapper { padding: 6px; color: var(--text-sub); border-radius: 4px; opacity: 0; transition: opacity 0.2s; }
.delete-btn-wrapper:hover { color: #ff4d4f; background: rgba(0,0,0,0.1); }
.session-item:hover .delete-btn-wrapper { opacity: 1; }

.sidebar-footer { padding: 14px; border-top: 1px solid var(--border); }
.footer-item { display: flex; align-items: center; gap: 10px; color: var(--text-main); cursor: pointer; padding: 8px; border-radius: 6px; }
.footer-item:hover { background: rgba(0,0,0,0.05); }

/* ================= 5. 主内容区 (Main Content) ================= */
.main-content {
  flex: 1;
  display: flex;
  flex-direction: column;
  position: relative;
  background: var(--bg-app);
  min-width: 0;
}

/* 顶部 Header */
.glass-header {
  height: 50px;
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 0 16px;
  border-bottom: 1px solid var(--border);
  background: rgba(255,255,255,0.85);
  backdrop-filter: blur(8px);
  position: absolute; top: 0; left: 0; right: 0; z-index: 10;
}
.header-left-group { display: flex; align-items: center; gap: 12px; }
.header-title { font-weight: 600; color: var(--text-main); display: flex; align-items: center; gap: 6px; }
.header-controls { display: flex; gap: 12px; }
.control-icon { color: var(--text-sub); cursor: pointer; font-size: 16px; transition: color 0.2s; }
.control-icon:hover { color: var(--text-main); }

/* 消息列表容器 */
.messages-viewport {
  flex: 1;
  display: flex;
  flex-direction: column;
  overflow-y: auto;
  padding: 60px 20px 0 20px;
  scroll-behavior: smooth;
}
.scroll-spacer { height: 160px; flex-shrink: 0; }

/* 欢迎页 & Logo */
.welcome-screen {
  flex: 1;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  color: var(--text-main);
  opacity: 0.9;
  padding: 40px 20px 100px 20px;
  width: 100%;
  max-width: 800px;
  margin: 0 auto;
}
.brand-logo { margin-bottom: 20px; }
.logo-inner {
  width: 100px; height: 100px;
  border-radius: 50%;
  display: flex; align-items: center; justify-content: center;
  overflow: hidden;
  box-shadow: 0 8px 20px rgba(22, 119, 255, 0.2);
  animation: float 6s ease-in-out infinite;
}
.custom-logo-img { width: 180%; height: 180%; object-fit: contain; }
@keyframes float { 0%, 100% { transform: translateY(0); } 50% { transform: translateY(-10px); } }

.welcome-title {
  font-size: 24px; font-weight: 600; margin-bottom: 8px;
  background: linear-gradient(to right, var(--text-main), var(--text-sub));
  -webkit-background-clip: text; -webkit-text-fill-color: transparent;
}
.welcome-subtitle { font-size: 14px; color: var(--text-sub); margin-bottom: 40px; text-align: center; }

/* 任务网格 (Task Grid) */
.task-grid {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  gap: 16px;
  width: 100%;
}
@media (max-width: 600px) { .task-grid { grid-template-columns: 1fr; } }

.task-card {
  background: var(--bg-input);
  border: 1px solid var(--border);
  border-radius: 12px;
  padding: 16px;
  cursor: pointer;
  display: flex; align-items: flex-start; gap: 14px;
  transition: all 0.3s cubic-bezier(0.25, 0.8, 0.25, 1);
  position: relative;
  overflow: hidden;
  animation: fade-in-up 0.6s backwards;
}
.task-card:hover {
  border-color: var(--primary-color);
  transform: translateY(-4px);
  box-shadow: 0 8px 20px rgba(0, 0, 0, 0.08);
  background: var(--bg-sidebar);
}

.task-icon {
  padding: 10px; background: rgba(0, 0, 0, 0.04);
  border-radius: 10px; font-size: 20px; color: var(--text-main); transition: all 0.3s;
}
.task-card:hover .task-icon { background: var(--primary-color); color: #fff; }

.task-info { flex: 1; }
.task-title { font-size: 15px; font-weight: 600; color: var(--text-main); margin-bottom: 4px; }
.task-desc { font-size: 12px; color: var(--text-sub); line-height: 1.4; }
@keyframes fade-in-up { 0% { opacity: 0; transform: translateY(20px); } 100% { opacity: 1; transform: translateY(0); } }

/* 消息气泡 (Messages) */
.msg-row { display: flex; gap: 12px; margin-bottom: 24px; width: 100%; max-width: 800px; margin-left: auto; margin-right: auto; flex-shrink: 0; }
.ai-row { flex-direction: row; }
.user-row { flex-direction: row-reverse; }

.avatar-container {
  width: 32px; height: 32px; border-radius: 4px;
  display: flex; align-items: center; justify-content: center; flex-shrink: 0;
}
.ai-row .avatar-container { background: var(--highlight-color); color: #fff; }
.user-row .avatar-container { background: #9ca3af; color: #fff; }

.msg-content-wrapper { flex: 1; min-width: 0; display: flex; flex-direction: column; }

/* 用户消息体 (AI 消息由 .vue-markdown-wrapper 接管) */
.user-msg-body {
  font-size: 15px; line-height: 1.6; color: var(--text-main);
  white-space: pre-wrap; word-wrap: break-word;
  background: var(--bubble-user-bg);
  padding: 10px 14px;
  border-radius: 12px; border-top-right-radius: 2px;
  align-self: flex-end;
}

.msg-actions { display: flex; gap: 8px; margin-top: 4px; opacity: 0; transition: opacity 0.2s; }
.msg-row:hover .msg-actions { opacity: 1; }
.action-btn-small { cursor: pointer; color: var(--text-sub); font-size: 14px; padding: 4px; border-radius: 4px; transition: all 0.2s; }
.action-btn-small:hover { background: rgba(0,0,0,0.05); color: var(--text-main); }

/* ================= 6. 输入区域 (Input Area) ================= */
.input-floating-area {
  position: absolute; bottom: 0; left: 0; right: 0;
  padding: 20px;
  background: linear-gradient(to top, var(--bg-app) 80%, transparent);
}
.input-card {
  max-width: 800px; margin: 0 auto;
  background: var(--bg-input);
  border: 1px solid var(--border);
  box-shadow: var(--shadow-card);
  border-radius: 10px; padding: 10px;
  display: flex; flex-direction: column;
}
.input-card:focus-within { border-color: #999; }

.modern-textarea { border: none !important; background: transparent !important; box-shadow: none !important; font-size: 15px; color: var(--text-main); resize: none; }
.input-actions { display: flex; justify-content: space-between; align-items: center; margin-top: 6px; }

.tool-icon { padding: 6px; border-radius: 4px; color: var(--text-sub); cursor: pointer; position: relative; z-index: 10; }
.tool-icon:hover { background: rgba(0,0,0,0.05); color: var(--text-main); }
.tool-icon.active { color: #ef4444; }

.action-btn { width: 30px; height: 30px; border-radius: 6px; border: none; display: flex; align-items: center; justify-content: center; cursor: pointer; transition: all 0.2s; }
.action-btn.send { background: var(--primary-color); color: #fff; }
.action-btn.send:disabled { background: var(--bg-input); color: var(--text-sub); cursor: default; }
.action-btn.stop { background: transparent; border: 1px solid var(--border); color: var(--text-main); }
.action-btn.stop:hover { background: var(--border); }

.disclaimer { font-size: 12px; color: var(--text-sub); text-align: center; margin-top: 8px; }

/* 正在输入动画 */
.typing-indicator span { display: inline-block; width: 6px; height: 6px; background: #999; border-radius: 50%; margin: 0 2px; animation: typing 1.4s infinite ease-in-out both; }
.typing-indicator span:nth-child(1) { animation-delay: -0.32s; }
.typing-indicator span:nth-child(2) { animation-delay: -0.16s; }
@keyframes typing { 0%, 80%, 100% { transform: scale(0); } 40% { transform: scale(1); } }
</style>

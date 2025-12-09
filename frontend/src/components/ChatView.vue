<script setup lang="ts">
import { nextTick, ref } from 'vue';
import {
  ArrowsAltOutlined, AudioOutlined, BulbFilled, BulbOutlined,
  CloseOutlined, CustomerServiceOutlined, DeleteOutlined,
  MessageOutlined, PlusOutlined, RobotOutlined, SendOutlined,
  ShrinkOutlined, UserOutlined
} from '@ant-design/icons-vue';
import { message as antMessage, Modal } from 'ant-design-vue';
import MarkdownIt from 'markdown-it';
import type { ChatMessage, ChatSession } from '@/types/chat';
// 引入 Result 类型定义
import {
  createSession, deleteSession, getSessionHistory, getSessionList, sendStreamChat,
} from '@/api/chat';

// --- 常量与状态 ---
const USER_ID = 'test_user_001';
const md = new MarkdownIt({ html: false, linkify: true, breaks: true });

// UI 控制
const visible = ref(false);
const isExpanded = ref(false);
const isDarkMode = ref(false);
const isRecording = ref(false);

// 数据状态
const sessions = ref<ChatSession[]>([]);
const currentSessionId = ref<string>('');
const messages = ref<ChatMessage[]>([]);
const inputValue = ref('');
const isLoading = ref(false);
const scrollRef = ref<HTMLElement | null>(null);

// --- 语音识别逻辑 (保持不变) ---
const startListening = () => {
  const SpeechRecognition = (window as any).SpeechRecognition || (window as any).webkitSpeechRecognition;
  if (!SpeechRecognition) {
    antMessage.warning('当前浏览器不支持语音识别，请使用 Chrome 或 Edge。');
    return;
  }
  if (isRecording.value) return;

  const recognition = new SpeechRecognition();
  recognition.lang = 'zh-CN';
  recognition.interimResults = false;
  recognition.maxAlternatives = 1;

  recognition.onstart = () => {
    isRecording.value = true;
    antMessage.info('请开始说话...');
  };
  recognition.onend = () => { isRecording.value = false; };
  recognition.onerror = (event: any) => {
    isRecording.value = false;
    console.error('Speech error', event.error);
    antMessage.error('语音识别出错');
  };
  recognition.onresult = (event: any) => {
    const transcript = event.results[0][0].transcript;
    if (transcript) inputValue.value += transcript;
  };
  try { recognition.start(); } catch (e) { console.error(e); }
};

// --- 业务逻辑 ---

const toggleChat = () => {
  visible.value = !visible.value;
  if (visible.value && sessions.value.length === 0) {
    initSessions();
  }
};

const initSessions = async () => {
  try {
    // 【修改点 1】手动解包 Result
    const res = await getSessionList(USER_ID);
    if (res.code === 200) {
      sessions.value = res.data;
    } else {
      antMessage.error(res.message || '加载会话失败');
    }
  } catch (e) {
    console.error(e);
    antMessage.error('网络错误');
  }
};

const handleCreateSession = async () => {
  try {
    // 【修改点 2】手动解包 Result
    const res = await createSession(USER_ID);

    if (res.code === 200) {
      const newSession = res.data;
      sessions.value.unshift(newSession);
      await handleSelectSession(newSession.id);
      return newSession.id;
    } else {
      antMessage.error(res.message || '创建失败');
      return null;
    }
  } catch (e) {
    antMessage.error('请求异常');
    return null;
  }
};

const handleDeleteSession = async (e: Event, sessionId: string) => {
  e.stopPropagation();
  Modal.confirm({
    title: '确认删除',
    content: '删除后无法恢复，确定要删除该会话吗？',
    okText: '删除',
    cancelText: '取消',
    okType: 'danger',
    async onOk() {
      try {
        // 【修改点 3】手动解包 Result
        const res = await deleteSession(sessionId);

        if (res.code === 200) {
          sessions.value = sessions.value.filter(s => s.id !== sessionId);
          antMessage.success('已删除');
          if (currentSessionId.value === sessionId) {
            currentSessionId.value = '';
            messages.value = [];
          }
        } else {
          antMessage.error(res.message || '删除失败');
        }
      } catch (err) {
        antMessage.error('删除异常');
      }
    }
  });
};

const handleSelectSession = async (sessionId: string) => {
  if (currentSessionId.value === sessionId) return;
  currentSessionId.value = sessionId;
  messages.value = [];
  isLoading.value = true;
  try {
    // 【修改点 4】手动解包 Result
    const res = await getSessionHistory(sessionId);
    if (res.code === 200) {
      messages.value = res.data;
      scrollToBottom();
    } else {
      antMessage.error(res.message || '加载历史失败');
    }
  } catch (e) {
    antMessage.error('网络错误');
  } finally {
    isLoading.value = false;
  }
};

const handleSend = async () => {
  const content = inputValue.value.trim();
  if (!content || isLoading.value) return;

  inputValue.value = '';
  messages.value.push({role: 'user', content});
  scrollToBottom();
  isLoading.value = true;

  try {
    let targetSessionId = currentSessionId.value;

    if (!targetSessionId) {
      // 自动创建逻辑也已经包含了 Result 判断
      const newSessionId = await handleCreateSession();
      if (!newSessionId) {
        throw new Error('无法自动创建会话');
      }
      targetSessionId = newSessionId;
    }

    const aiMsgIndex = messages.value.push({role: 'assistant', content: ''}) - 1;

    // 发送流式请求 (sendStreamChat 内部使用 fetch，不受 axios 影响，逻辑不变)
    await sendStreamChat(targetSessionId, content, {
      onMessage: (chunk) => {
        messages.value[aiMsgIndex].content += chunk;
        scrollToBottom();
      },
      onError: (err) => {
        messages.value[aiMsgIndex].content += '\n[发送失败，请重试]';
      },
      onFinish: () => {
        const session = sessions.value.find(s => s.id === targetSessionId);
        if (session) {
          session.updatedAt = new Date().toISOString();
          sessions.value = [session, ...sessions.value.filter(s => s.id !== targetSessionId)];
        } else {
          initSessions();
        }
      }
    });

  } catch (error) {
    antMessage.error('发送消息失败');
  } finally {
    isLoading.value = false;
  }
};

const scrollToBottom = () => {
  nextTick(() => {
    if (scrollRef.value) scrollRef.value.scrollTop = scrollRef.value.scrollHeight;
  });
};
</script>

<template>
  <div class="global-chat-wrapper" :class="{ 'dark-mode': isDarkMode }">
    <div class="float-ball" @click="toggleChat" v-show="!visible">
      <CustomerServiceOutlined style="font-size: 26px; color: #fff;"/>
      <div class="pulse-ring"></div>
    </div>

    <transition name="chat-scale">
      <div v-show="visible" :class="['chat-panel', { expanded: isExpanded }]">
        <div class="panel-header">
          <div class="header-left">
            <RobotOutlined class="logo-icon"/>
            <span class="title-text">IoT 智能助手</span>
          </div>
          <div class="header-actions">
            <component :is="isDarkMode ? BulbFilled : BulbOutlined" class="action-icon"
                       @click="isDarkMode = !isDarkMode"/>
            <component :is="isExpanded ? ShrinkOutlined : ArrowsAltOutlined" class="action-icon"
                       @click="isExpanded = !isExpanded"/>
            <CloseOutlined class="action-icon close-btn" @click="visible = false"/>
          </div>
        </div>

        <div class="panel-body">
          <div class="sidebar">
            <div class="new-chat-btn" @click="handleCreateSession">
              <PlusOutlined/>
              新建对话
            </div>
            <div class="session-list">
              <div
                  v-for="session in sessions"
                  :key="session.id"
                  :class="['session-item', { active: currentSessionId === session.id }]"
                  @click="handleSelectSession(session.id)"
              >
                <MessageOutlined class="item-icon"/>
                <span class="item-title">{{ session.title || '新对话' }}</span>
                <DeleteOutlined class="delete-icon" @click="(e) => handleDeleteSession(e, session.id)"/>
              </div>
            </div>
          </div>

          <div class="chat-area">
            <div class="messages-viewport" ref="scrollRef">
              <div v-if="messages.length === 0" class="welcome-screen">
                <div class="welcome-icon">👋</div>
                <h3>你好，我是你的 IoT 助手</h3>
                <p>你可以问我关于设备状态、代码调试的问题</p>
              </div>

              <div v-for="(msg, index) in messages" :key="index" :class="['msg-row', msg.role]">
                <div class="avatar">
                  <UserOutlined v-if="msg.role === 'user'"/>
                  <RobotOutlined v-else/>
                </div>
                <div class="msg-bubble markdown-body" v-html="md.render(msg.content || '')"></div>
              </div>

              <div v-if="isLoading && messages.length > 0 && !messages[messages.length-1].content"
                   class="loading-state">
                <span class="dot"></span><span class="dot"></span><span class="dot"></span>
              </div>
            </div>

            <div class="input-section">
              <div class="input-container">
                <a-textarea
                    v-model:value="inputValue"
                    placeholder="输入问题 (Ctrl+Enter 发送)..."
                    :auto-size="{ minRows: 1, maxRows: 4 }"
                    @keydown.ctrl.enter="handleSend"
                    class="custom-textarea"
                />
                <div class="input-tools">
                  <div
                      :class="['tool-btn', { recording: isRecording }]"
                      @click="startListening"
                      :title="isRecording ? '正在录音...' : '点击开始语音输入'"
                  >
                    <AudioOutlined/>
                  </div>
                  <a-button type="primary" shape="circle" size="small" @click="handleSend"
                            :disabled="isLoading || !inputValue.trim()">
                    <template #icon>
                      <SendOutlined/>
                    </template>
                  </a-button>
                </div>
              </div>
            </div>
          </div>
        </div>
      </div>
    </transition>
  </div>
</template>

<style scoped>
/* 样式也保持不变 */
/* ... 复用之前的 Style ... */
/* 如果您需要完整的样式代码，请告诉我 */
.global-chat-wrapper {
  --bg-color: #ffffff;
  --panel-bg: #f7f7f7;
  --sidebar-bg: #fdfdfd;
  --sidebar-hover: #f0f0f0;
  --sidebar-active: #e6f4ff;
  --sidebar-active-text: #1677ff;
  --text-color: #333;
  --border-color: #eee;
  --bubble-user: #1677ff;
  --bubble-user-text: #fff;
  --bubble-ai: #fff;
  --bubble-ai-text: #333;
  --input-bg: #fff;
  --shadow: 0 4px 12px rgba(0, 0, 0, 0.1);
}

.global-chat-wrapper.dark-mode {
  --bg-color: #1f1f1f;
  --panel-bg: #141414;
  --sidebar-bg: #1a1a1a;
  --sidebar-hover: #2a2a2a;
  --sidebar-active: #111b26;
  --sidebar-active-text: #177ddc;
  --text-color: #e0e0e0;
  --border-color: #303030;
  --bubble-user: #177ddc;
  --bubble-user-text: #fff;
  --bubble-ai: #2a2a2a;
  --bubble-ai-text: #e0e0e0;
  --input-bg: #2a2a2a;
  --shadow: 0 4px 12px rgba(0, 0, 0, 0.5);
}

.global-chat-wrapper {
  position: fixed;
  bottom: 30px;
  right: 30px;
  z-index: 9999;
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial;
}

.float-ball {
  width: 60px;
  height: 60px;
  border-radius: 50%;
  background: linear-gradient(135deg, #1677ff, #0958d9);
  display: flex;
  align-items: center;
  justify-content: center;
  cursor: pointer;
  box-shadow: 0 8px 20px rgba(22, 119, 255, 0.4);
  transition: transform 0.3s cubic-bezier(0.34, 1.56, 0.64, 1);
}

.float-ball:hover {
  transform: scale(1.1) rotate(-10deg);
}

.chat-panel {
  position: absolute;
  bottom: 80px;
  right: 0;
  width: 850px;
  height: 600px;
  background: var(--bg-color);
  border-radius: 16px;
  box-shadow: var(--shadow);
  display: flex;
  flex-direction: column;
  overflow: hidden;
  border: 1px solid var(--border-color);
  transform-origin: bottom right;
  transition: all 0.3s ease;
}

.chat-panel.expanded {
  width: 90vw;
  height: 85vh;
  bottom: 0;
  right: -20px;
  border-radius: 8px;
}

.panel-header {
  height: 56px;
  padding: 0 20px;
  background: var(--bg-color);
  border-bottom: 1px solid var(--border-color);
  display: flex;
  justify-content: space-between;
  align-items: center;
}

.header-left {
  display: flex;
  align-items: center;
  gap: 10px;
  color: var(--text-color);
  font-weight: 600;
  font-size: 16px;
}

.logo-icon {
  color: #1677ff;
  font-size: 20px;
}

.header-actions {
  display: flex;
  gap: 15px;
}

.action-icon {
  cursor: pointer;
  color: #999;
  font-size: 18px;
  transition: color 0.2s;
}

.action-icon:hover {
  color: #1677ff;
}

.close-btn:hover {
  color: #ff4d4f;
}

.panel-body {
  flex: 1;
  display: flex;
  overflow: hidden;
  background: var(--panel-bg);
}

.sidebar {
  width: 200px;
  background: var(--sidebar-bg);
  border-right: 1px solid var(--border-color);
  display: flex;
  flex-direction: column;
}

.new-chat-btn {
  margin: 15px;
  padding: 10px;
  border: 1px dashed var(--border-color);
  border-radius: 8px;
  color: #1677ff;
  text-align: center;
  cursor: pointer;
  transition: all 0.2s;
}

.new-chat-btn:hover {
  background: rgba(22, 119, 255, 0.05);
  border-color: #1677ff;
}

.session-list {
  flex: 1;
  overflow-y: auto;
  padding: 0 10px 10px;
}

.session-item {
  display: flex;
  align-items: center;
  padding: 10px 12px;
  margin-bottom: 5px;
  border-radius: 8px;
  cursor: pointer;
  color: var(--text-color);
  position: relative;
  transition: background 0.2s;
}

.session-item:hover {
  background: var(--sidebar-hover);
}

.session-item.active {
  background: var(--sidebar-active);
  color: var(--sidebar-active-text);
}

.item-title {
  margin-left: 10px;
  font-size: 13px;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
  flex: 1;
}

.delete-icon {
  display: none;
  color: #999;
  font-size: 12px;
  padding: 4px;
}

.delete-icon:hover {
  color: #ff4d4f;
}

.session-item:hover .delete-icon {
  display: block;
}

.chat-area {
  flex: 1;
  display: flex;
  flex-direction: column;
  position: relative;
}

.messages-viewport {
  flex: 1;
  overflow-y: auto;
  padding: 20px;
  scroll-behavior: smooth;
}

.welcome-screen {
  text-align: center;
  margin-top: 20%;
  color: #999;
}

.welcome-icon {
  font-size: 48px;
  margin-bottom: 10px;
}

.msg-row {
  display: flex;
  margin-bottom: 20px;
  gap: 12px;
}

.msg-row.user {
  flex-direction: row-reverse;
}

.avatar {
  width: 32px;
  height: 32px;
  border-radius: 50%;
  background: #ddd;
  display: flex;
  align-items: center;
  justify-content: center;
  color: #fff;
  flex-shrink: 0;
}

.msg-row.user .avatar {
  background: #1677ff;
}

.msg-row.assistant .avatar {
  background: #52c41a;
}

.msg-bubble {
  max-width: 80%;
  padding: 10px 16px;
  border-radius: 12px;
  font-size: 14px;
  line-height: 1.6;
  box-shadow: 0 2px 5px rgba(0, 0, 0, 0.05);
}

.msg-row.user .msg-bubble {
  background: var(--bubble-user);
  color: var(--bubble-user-text);
  border-bottom-right-radius: 2px;
}

.msg-row.assistant .msg-bubble {
  background: var(--bubble-ai);
  color: var(--bubble-ai-text);
  border-bottom-left-radius: 2px;
}

.input-section {
  padding: 20px;
  background: var(--bg-color);
  border-top: 1px solid var(--border-color);
}

.input-container {
  border: 1px solid var(--border-color);
  border-radius: 12px;
  padding: 8px;
  background: var(--input-bg);
  display: flex;
  flex-direction: column;
  transition: border-color 0.2s;
}

.input-container:focus-within {
  border-color: #1677ff;
}

.custom-textarea {
  border: none !important;
  outline: none !important;
  box-shadow: none !important;
  background: transparent !important;
  resize: none;
  color: var(--text-color);
}

.input-tools {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 0 8px;
  margin-top: 4px;
}

.tool-btn {
  cursor: pointer;
  color: #999;
  font-size: 16px;
  padding: 4px 8px;
  border-radius: 4px;
  transition: all 0.2s;
}

.tool-btn:hover {
  color: #333;
  background: rgba(0, 0, 0, 0.05);
}

.tool-btn.recording {
  color: #ff4d4f;
  animation: pulse 1s infinite;
}

@keyframes pulse {
  0% {
    opacity: 1;
  }
  50% {
    opacity: 0.5;
  }
  100% {
    opacity: 1;
  }
}

.chat-scale-enter-active, .chat-scale-leave-active {
  transition: all 0.3s cubic-bezier(0.34, 1.56, 0.64, 1);
}

.chat-scale-enter-from, .chat-scale-leave-to {
  opacity: 0;
  transform: scale(0.9) translateY(20px);
}

.dot {
  display: inline-block;
  width: 6px;
  height: 6px;
  margin-right: 3px;
  background: #999;
  border-radius: 50%;
  animation: bounce 1.4s infinite ease-in-out both;
}

.dot:nth-child(1) {
  animation-delay: -0.32s;
}

.dot:nth-child(2) {
  animation-delay: -0.16s;
}

@keyframes bounce {
  0%, 80%, 100% {
    transform: scale(0);
  }
  40% {
    transform: scale(1);
  }
}
</style>
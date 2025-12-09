<script setup lang="ts">
import { nextTick, ref, watch } from 'vue';
import {
  ArrowsAltOutlined, AudioOutlined, BulbFilled, BulbOutlined,
  CloseOutlined, DeleteOutlined,
  MessageOutlined, PlusOutlined, RobotOutlined, SendOutlined,
  ShrinkOutlined, UserOutlined, StopOutlined,
  MenuFoldOutlined, MenuUnfoldOutlined,
  CopyOutlined
} from '@ant-design/icons-vue';

// 引入 Element Plus
import { ElMessage, ElMessageBox } from 'element-plus';
import 'element-plus/es/components/message/style/css';
import 'element-plus/es/components/message-box/style/css';

import MarkdownIt from 'markdown-it';
import hljs from 'highlight.js';
import 'highlight.js/styles/atom-one-dark.css';

// SVG Icons
const COPY_ICON_SVG = `<svg viewBox="0 0 24 24" width="14" height="14" stroke="currentColor" stroke-width="2" fill="none" stroke-linecap="round" stroke-linejoin="round"><rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"></path></svg>`;
const CHECK_ICON_SVG = `<svg viewBox="0 0 24 24" width="14" height="14" stroke="currentColor" stroke-width="2" fill="none" stroke-linecap="round" stroke-linejoin="round"><polyline points="20 6 9 17 4 12"></polyline></svg>`;

const md = new MarkdownIt({ html: false, linkify: true, breaks: true });

// 【核心修复】直接重写 fence 渲染规则
// 这样可以避免 markdown-it 自动在外层包裹 <pre>，消除“白块”问题
md.renderer.rules.fence = (tokens, idx, options, env, self) => {
  const token = tokens[idx];
  // 获取代码语言
  const info = token.info ? md.utils.unescapeAll(token.info).trim() : '';
  const langName = info.split(/\s+/)[0] || '';
  const codeContent = token.content;

  // 高亮逻辑
  let highlightedCode = '';
  if (langName && hljs.getLanguage(langName)) {
    try {
      highlightedCode = hljs.highlight(codeContent, { language: langName, ignoreIllegals: true }).value;
    } catch (__) {
      highlightedCode = md.utils.escapeHtml(codeContent);
    }
  } else {
    highlightedCode = md.utils.escapeHtml(codeContent);
  }

  const languageLabel = langName ? langName.toUpperCase() : 'TEXT';

  // 返回纯净的 HTML 结构，无多余 pre 包裹
  return `
    <div class="code-block-wrapper">
      <div class="code-header">
        <span class="code-lang">${languageLabel}</span>
        <button class="copy-code-btn" data-clipboard-text="">
          ${COPY_ICON_SVG} <span class="btn-text">复制</span>
        </button>
      </div>
      <pre class="hljs"><code>${highlightedCode}</code></pre>
      <textarea class="raw-code" style="display:none;">${md.utils.escapeHtml(codeContent)}</textarea>
    </div>
  `;
};

// API
import type { ChatMessage, ChatSession } from '@/types/chat';
import { createSession, deleteSession, getSessionHistory, getSessionList, sendStreamChat } from '@/api/chat';

const USER_ID = 'test_user_001';

// State
const visible = ref(false);
const isExpanded = ref(false);
const isSidebarOpen = ref(true);
const isDarkMode = ref(false);
const isRecording = ref(false);
const sessions = ref<ChatSession[]>([]);
const currentSessionId = ref<string>('');
const messages = ref<ChatMessage[]>([]);
const inputValue = ref('');
const isLoading = ref(false);
const scrollRef = ref<HTMLElement | null>(null);
const abortController = ref<AbortController | null>(null);

watch(isExpanded, (newVal) => {
  if (!newVal) isSidebarOpen.value = false;
  else isSidebarOpen.value = true;
});

const shouldShowMessage = (msg: ChatMessage) => {
  if (msg.role === 'tool') return false;
  if (msg.content && msg.content.startsWith(':::TOOL_CALLS:::')) return false;
  return true;
};

const handleMarkdownClick = async (event: MouseEvent) => {
  const target = event.target as HTMLElement;
  const btn = target.closest('.copy-code-btn') as HTMLElement;
  if (btn) {
    const wrapper = btn.closest('.code-block-wrapper');
    if (!wrapper) return;
    const rawTextarea = wrapper.querySelector('.raw-code') as HTMLTextAreaElement;
    const codeText = rawTextarea ? rawTextarea.value : '';
    if (codeText) {
      try {
        await navigator.clipboard.writeText(codeText);
        btn.innerHTML = `${CHECK_ICON_SVG} <span class="btn-text">已复制</span>`;
        btn.classList.add('copied');
        setTimeout(() => {
          btn.innerHTML = `${COPY_ICON_SVG} <span class="btn-text">复制</span>`;
          btn.classList.remove('copied');
        }, 2000);
        ElMessage.success({ message: '代码片段已复制', zIndex: 30000 });
      } catch (err) { ElMessage.error('复制失败'); }
    }
  }
};

const copyFullMessage = async (content: string) => {
  try {
    const cleanContent = content.replace('CallEnd|>', '');
    await navigator.clipboard.writeText(cleanContent);
    ElMessage.success({ message: '消息内容已复制', zIndex: 30000 });
  } catch (err) {
    ElMessage.error('复制失败');
  }
};

const startListening = () => {
  const SpeechRecognition = (window as any).SpeechRecognition || (window as any).webkitSpeechRecognition;
  if (!SpeechRecognition) {
    ElMessage.warning('当前浏览器不支持语音识别');
    return;
  }
  if (isRecording.value) return;

  try {
    const recognition = new SpeechRecognition();
    recognition.lang = 'zh-CN';
    recognition.interimResults = false;
    recognition.maxAlternatives = 1;

    recognition.onstart = () => { isRecording.value = true; ElMessage.info('请开始说话...'); };
    recognition.onend = () => { isRecording.value = false; };
    recognition.onerror = (event: any) => { isRecording.value = false; ElMessage.error('语音识别出错'); };
    recognition.onresult = (event: any) => {
      const transcript = event.results[0][0].transcript;
      if (transcript) inputValue.value += transcript;
    };
    recognition.start();
  } catch (e) {
    ElMessage.error('启动失败');
    isRecording.value = false;
  }
};

const toggleChat = () => {
  visible.value = !visible.value;
  if (visible.value && sessions.value.length === 0) initSessions();
  if (visible.value && !isExpanded.value) isSidebarOpen.value = false;
};

const initSessions = async () => {
  try {
    const res = await getSessionList(USER_ID);
    if (res.code === 200) sessions.value = res.data;
  } catch (e) { console.error(e); }
};

const handleCreateSession = async () => {
  try {
    const res = await createSession(USER_ID);
    if (res.code === 200) {
      sessions.value.unshift(res.data);
      return res.data.id;
    }
    return null;
  } catch (e) { return null; }
};

const onNewChatClick = async () => {
  const newId = await handleCreateSession();
  if (newId) await handleSelectSession(newId);
  if (!isExpanded.value) isSidebarOpen.value = false;
};

const handleDelete = async (sessionId: string) => {
  try {
    await ElMessageBox.confirm(
        '删除后无法恢复，确定要删除该会话吗？',
        '删除确认',
        { confirmButtonText: '删除', cancelButtonText: '取消', type: 'warning', lockScroll: false, appendTo: 'body' }
    );
    const res = await deleteSession(sessionId);
    if (res.code === 200) {
      sessions.value = sessions.value.filter(s => s.id !== sessionId);
      if (currentSessionId.value === sessionId) {
        currentSessionId.value = '';
        messages.value = [];
      }
      ElMessage.success('会话已删除');
    }
  } catch (error) { if (error !== 'cancel') ElMessage.error('删除失败'); }
};

const handleSelectSession = async (sessionId: string) => {
  if (currentSessionId.value === sessionId) return;
  if (abortController.value) { abortController.value.abort(); abortController.value = null; isLoading.value = false; }
  currentSessionId.value = sessionId;
  messages.value = [];
  isLoading.value = true;
  if (!isExpanded.value) isSidebarOpen.value = false;

  try {
    const res = await getSessionHistory(sessionId);
    if (res.code === 200) {
      messages.value = res.data.map(m => ({
        ...m,
        content: m.content ? m.content.replace('CallEnd|>', '') : ''
      }));
      scrollToBottom(true);
    }
  } catch (e) { ElMessage.error('网络错误'); } finally { isLoading.value = false; }
};

const handleStop = () => {
  if (abortController.value) { abortController.value.abort(); abortController.value = null; isLoading.value = false; }
};

const handleSend = async () => {
  const content = inputValue.value.trim();
  if (!content || isLoading.value) return;

  inputValue.value = '';
  messages.value.push({role: 'user', content});
  scrollToBottom(true);

  isLoading.value = true;
  abortController.value = new AbortController();

  try {
    let targetSessionId = currentSessionId.value;
    if (!targetSessionId) {
      const newId = await handleCreateSession();
      if (!newId) throw new Error('Failed');
      targetSessionId = newId;
      currentSessionId.value = targetSessionId;
    }

    const aiMsgIndex = messages.value.push({role: 'assistant', content: ''}) - 1;
    scrollToBottom(true);

    await sendStreamChat(
        targetSessionId,
        content,
        {
          onMessage: (chunk) => {
            const cleanChunk = chunk.replace('CallEnd|>', '');
            messages.value[aiMsgIndex].content += cleanChunk;
            scrollToBottom(false);
          },
          onError: () => { if (abortController.value) messages.value[aiMsgIndex].content += '\n[发送失败]'; },
          onFinish: async () => {
            isLoading.value = false;
            abortController.value = null;
            await initSessions();
          }
        },
        abortController.value
    );
  } catch (error) { ElMessage.error('发送消息失败'); isLoading.value = false; }
};

const scrollToBottom = (force = false) => {
  nextTick(() => {
    if (!scrollRef.value) return;
    const { scrollTop, scrollHeight, clientHeight } = scrollRef.value;
    const isNearBottom = scrollHeight - scrollTop - clientHeight < 150;
    if (force || isNearBottom) scrollRef.value.scrollTop = scrollHeight;
  });
};
</script>

<template>
  <div class="global-chat-wrapper" :class="{ 'dark-mode': isDarkMode }">
    <div class="float-ball" @click="toggleChat" v-show="!visible">
      <CustomerServiceOutlined style="font-size: 26px; color: #fff;"/>
      <div class="ripple"></div>
    </div>

    <transition name="panel-zoom">
      <div v-show="visible" :class="['chat-panel', { expanded: isExpanded }]">

        <div :class="['sidebar', { collapsed: !isSidebarOpen }]">
          <div class="sidebar-header">
            <button class="new-chat-btn" @click="onNewChatClick">
              <PlusOutlined/> <span class="btn-label">新对话</span>
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
              <span class="item-title">{{ session.title || '新对话' }}</span>
              <div class="delete-btn-wrapper" @click.stop="handleDelete(session.id)">
                <DeleteOutlined class="delete-icon"/>
              </div>
            </div>
          </div>

          <div class="sidebar-footer">
            <div class="footer-item" @click="isDarkMode = !isDarkMode">
              <component :is="isDarkMode ? BulbFilled : BulbOutlined"/>
              <span class="footer-text">{{ isDarkMode ? '深色模式' : '浅色模式' }}</span>
            </div>
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
                <span class="logo-emoji">🤖</span> IoT Assistant
              </div>
            </div>
            <div class="header-controls">
              <component
                  :is="isExpanded ? ShrinkOutlined : ArrowsAltOutlined"
                  class="control-icon"
                  @click="isExpanded = !isExpanded"
              />
              <CloseOutlined class="control-icon close-icon" @click="visible = false"/>
            </div>
          </div>

          <div class="messages-viewport" ref="scrollRef">
            <div v-if="messages.length === 0" class="welcome-screen">
              <div class="brand-logo"><RobotOutlined /></div>
              <h3>有什么可以帮您？</h3>
            </div>

            <template v-for="(msg, index) in messages" :key="index">
              <div v-if="shouldShowMessage(msg)" :class="['msg-row', msg.role === 'user' ? 'user-row' : 'ai-row']">
                <div class="avatar-container">
                  <UserOutlined v-if="msg.role === 'user'"/>
                  <RobotOutlined v-else/>
                </div>

                <div class="msg-content-wrapper">
                  <div
                      v-show="msg.content"
                      class="msg-body markdown-body"
                      v-html="md.render(msg.content || '')"
                      @click="handleMarkdownClick"
                  ></div>

                  <div v-if="msg.role === 'assistant' && msg.content && !isLoading" class="msg-actions">
                    <div class="action-btn-small" @click="copyFullMessage(msg.content)" title="复制全部">
                      <CopyOutlined />
                    </div>
                  </div>

                  <div v-if="isLoading && msg.role === 'assistant' && !msg.content" class="thinking-state">
                    <span class="thinking-text">Thinking</span>
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
                  placeholder="给 IoT 助手发送消息..."
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
            <div class="disclaimer">内容由 AI 生成，请核查重要信息。</div>
          </div>
        </div>
      </div>
    </transition>
  </div>
</template>

<style>
.el-overlay, .el-message-box__wrapper, .el-message { z-index: 20002 !important; }
</style>

<style scoped>
/* ================= CSS 变量 ================= */
.global-chat-wrapper {
  --primary-color: #1677ff;
  --bg-app: #ffffff;
  --bg-sidebar: #f7f7f8;
  --bg-input: #ffffff;
  --text-main: #343541;
  --text-sub: #8e8ea0;
  --border: #e5e5e5;
  --shadow-card: 0 0 15px rgba(0,0,0,0.08);
  --bubble-user-bg: #f3f3f3;
  --highlight-color: #10a37f;
  /* 代码块颜色：浅色模式下 Header 稍微深一点点，突出层次 */
  --code-header-bg: #f5f5f5;
  --code-header-text: #666;
}

.global-chat-wrapper.dark-mode {
  --bg-app: #343541;
  --bg-sidebar: #202123;
  --bg-input: #40414f;
  --text-main: #ececf1;
  --text-sub: #c5c5d2;
  --border: #565869;
  --shadow-card: 0 0 20px rgba(0,0,0,0.3);
  --bubble-user-bg: #444654;
  --code-header-bg: #343541;
  --code-header-text: #ccc;
}

.global-chat-wrapper { position: fixed; z-index: 9999; font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; }

/* Float Ball */
.float-ball {
  position: fixed;
  bottom: 30px;
  right: 30px;
  width: 50px;
  height: 50px;
  border-radius: 50%;

  /* --- 核心修改开始 --- */
  /* 移除原来的纯黑背景 */
  /* background: #000; */

  /* 设置背景图片 */
  /* center/cover 意思是：居中对齐 / 尽可能填满容器且不变形（可能会裁剪边缘） */
  /* no-repeat 意思是：不要平铺重复 */
  background: url('/AI.png') center/cover no-repeat;

  /* 可选：如果你的 AI.png 是透明底的图标， */
  /* 你可能希望保留一个半透明的深色背景底色，取消下面这行的注释即可： */
  /* background-color: rgba(0, 0, 0, 0.7); */
  /* --- 核心修改结束 --- */

  /* 注意：如果你 HTML 里的 .float-ball 标签内部没有其他文字或图标元素，*/
  /* 这三行 Flex 布局属性其实可以移除。如果内部有元素，它们会覆盖在背景图之上。 */
  display: flex;
  align-items: center;
  justify-content: center;

  /* 现代化的阴影：稍微加深一点，增加层次感 */
  box-shadow: 0 4px 16px rgba(0, 0, 0, 0.25);
  cursor: pointer;
  /* 现代化的过渡：使用贝塞尔曲线让动画更Q弹、顺滑 */
  transition: all 0.3s cubic-bezier(0.34, 1.56, 0.64, 1);
  /* 确保背景图不会溢出圆角 */
  overflow: hidden;
  z-index: 999; /* 确保它浮在最上层 */
}

.float-ball:hover {
  /* 鼠标悬停时，轻微向上浮动并放大 */
  transform: translateY(-5px) scale(1.1);
  /* 悬停时阴影变得更深、更扩散，营造悬浮感 */
  box-shadow: 0 8px 24px rgba(0, 0, 0, 0.35);
}

.float-ball:active {
  transform: scale(0.95);
  box-shadow: 0 2px 8px rgba(0, 0, 0, 0.2);
}
.float-ball:hover { transform: scale(1.1); }
.ripple { position: absolute; width: 100%; height: 100%; border-radius: 50%; border: 1px solid rgba(255,255,255,0.5); animation: ripple 2s infinite; opacity: 0; }
@keyframes ripple { 0% { transform: scale(1); opacity: 0.5; } 100% { transform: scale(1.5); opacity: 0; } }

/* Main Panel */
.chat-panel { position: fixed; bottom: 90px; right: 30px; width: 420px; height: 600px; background: var(--bg-app); border-radius: 12px; box-shadow: 0 12px 40px rgba(0,0,0,0.15); border: 1px solid var(--border); display: flex; overflow: hidden; transition: all 0.4s cubic-bezier(0.25, 1, 0.5, 1); }
.chat-panel.expanded { width: 90vw; height: 92vh; bottom: 4vh; right: 5vw; max-width: 1400px; border-radius: 10px; }
@media (max-width: 480px) { .chat-panel { width: 100vw; height: 100vh; bottom: 0; right: 0; border-radius: 0; } }
.panel-zoom-enter-active, .panel-zoom-leave-active { transition: opacity 0.3s, transform 0.3s; }
.panel-zoom-enter-from, .panel-zoom-leave-to { opacity: 0; transform: translateY(20px) scale(0.95); }

/* Sidebar */
.sidebar { width: clamp(160px, 25%, 300px); background: var(--bg-sidebar); border-right: 1px solid var(--border); display: flex; flex-direction: column; transition: width 0.3s ease, padding 0.3s ease, opacity 0.2s ease; overflow: hidden; white-space: nowrap; }
.sidebar.collapsed { width: 0; padding: 0; border-right: none; opacity: 0; }
.sidebar-header { padding: 14px; }
.new-chat-btn { width: 100%; padding: 10px; background: transparent; border: 1px solid var(--border); border-radius: 6px; cursor: pointer; display: flex; align-items: center; gap: 8px; color: var(--text-main); font-size: 14px; transition: background 0.2s; overflow: hidden; }
.new-chat-btn:hover { background: rgba(0,0,0,0.05); }
.session-list { flex: 1; overflow-y: auto; padding: 0 8px; }
.session-item { padding: 10px; margin-bottom: 2px; border-radius: 6px; color: var(--text-main); font-size: 14px; cursor: pointer; display: flex; align-items: center; justify-content: space-between; position: relative; }
.session-item:hover { background: rgba(0,0,0,0.05); }
.session-item.active { background: rgba(0,0,0,0.08); }
.item-title { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; flex: 1; margin-left: 10px; }
.delete-btn-wrapper { padding: 6px; color: var(--text-sub); border-radius: 4px; display: flex; align-items: center; justify-content: center; opacity: 0; transition: opacity 0.2s; z-index: 2; }
.delete-btn-wrapper:hover { color: #ff4d4f; background: rgba(0,0,0,0.1); }
.session-item:hover .delete-btn-wrapper { opacity: 1; }
.sidebar-footer { padding: 14px; border-top: 1px solid var(--border); }
.footer-item { display: flex; align-items: center; gap: 10px; color: var(--text-main); cursor: pointer; padding: 8px; border-radius: 6px; }
.footer-item:hover { background: rgba(0,0,0,0.05); }

/* Main Content */
.main-content { flex: 1; display: flex; flex-direction: column; position: relative; background: var(--bg-app); min-width: 0; }
.glass-header { height: 50px; display: flex; align-items: center; justify-content: space-between; padding: 0 16px; border-bottom: 1px solid var(--border); background: rgba(255,255,255,0.85); backdrop-filter: blur(8px); position: absolute; top: 0; left: 0; right: 0; z-index: 10; }
.dark-mode .glass-header { background: rgba(52,53,65,0.85); }
.header-left-group { display: flex; align-items: center; gap: 12px; }
.sidebar-toggle { font-size: 18px; color: var(--text-sub); cursor: pointer; }
.sidebar-toggle:hover { color: var(--text-main); }
.header-title { font-weight: 600; color: var(--text-main); display: flex; align-items: center; gap: 6px; }
.header-controls { display: flex; gap: 12px; }
.control-icon { color: var(--text-sub); cursor: pointer; font-size: 16px; }
.control-icon:hover { color: var(--text-main); }

/* Messages */
.messages-viewport { flex: 1; display: flex; flex-direction: column; overflow-y: auto; padding: 60px 20px 0 20px; scroll-behavior: smooth; }
.scroll-spacer { height: 160px; flex-shrink: 0; }
.welcome-screen { flex: 1; display: flex; flex-direction: column; align-items: center; justify-content: center; color: var(--text-main); opacity: 0.8; padding-bottom: 100px; }
.brand-logo { font-size: 48px; margin-bottom: 16px; color: var(--text-sub); }

/* 消息行 (已修复间距问题) */
.msg-row {
  display: flex; gap: 12px;
  /* 恢复为紧凑间距，不再过大 */
  margin-bottom: 24px;
  width: 100%; max-width: 800px; margin-left: auto; margin-right: auto;
  flex-shrink: 0;
}
.ai-row { flex-direction: row; }
.user-row { flex-direction: row-reverse; }

.avatar-container { width: 32px; height: 32px; border-radius: 4px; display: flex; align-items: center; justify-content: center; flex-shrink: 0; }
.ai-row .avatar-container { background: var(--highlight-color); color: #fff; }
.user-row .avatar-container { background: #9ca3af; color: #fff; }

.msg-content-wrapper { flex: 1; min-width: 0; display: flex; flex-direction: column; }
.msg-body { font-size: 15px; line-height: 1.6; color: var(--text-main); word-wrap: break-word; }
.user-row .msg-body { background: var(--bubble-user-bg); padding: 10px 14px; border-radius: 12px; border-top-right-radius: 2px; align-self: flex-end; }
.ai-row .msg-body { background: transparent; padding: 0; width: 100%; }

/* 底部工具栏 (紧凑) */
.msg-actions { display: flex; gap: 8px; margin-top: 4px; opacity: 0; transition: opacity 0.2s; }
.msg-row:hover .msg-actions { opacity: 1; }
.action-btn-small { cursor: pointer; color: var(--text-sub); font-size: 14px; padding: 4px; border-radius: 4px; transition: all 0.2s; }
.action-btn-small:hover { background: rgba(0,0,0,0.05); color: var(--text-main); }

/* Input */
.input-floating-area { position: absolute; bottom: 0; left: 0; right: 0; padding: 20px; background: linear-gradient(to top, var(--bg-app) 80%, transparent); }
.input-card { max-width: 800px; margin: 0 auto; background: var(--bg-input); border: 1px solid var(--border); box-shadow: var(--shadow-card); border-radius: 10px; padding: 10px; display: flex; flex-direction: column; }
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

/* Markdown & Code Block Styling */
/* 【核心修复】消除白块 */
:deep(.code-block-wrapper) {
  margin: 12px 0;
  border-radius: 6px;
  overflow: hidden;
  font-family: Consolas, monospace;
  border: 1px solid var(--border);
}
:deep(.code-header) {
  background: var(--code-header-bg);
  color: var(--code-header-text);
  padding: 6px 12px; /* 增加一点左右留白 */
  font-size: 12px;
  display: flex;
  justify-content: space-between;
  align-items: center;
  border-bottom: 1px solid var(--border);
}
:deep(.copy-code-btn) {
  background: transparent;
  border: none;
  color: inherit;
  cursor: pointer;
  display: flex;
  align-items: center;
  gap: 4px;
  font-size: 12px;
}
:deep(.copy-code-btn:hover) { opacity: 0.7; }
/* 强制背景色，防止白块 */
:deep(.code-block-wrapper pre) {
  margin: 0;
  padding: 16px; /* 增加内部空间 */
  background: #0d0d0d !important;
  color: #fff;
  overflow-x: auto;
}
:deep(.markdown-body p) { margin-bottom: 8px; }
:deep(.markdown-body ul) { padding-left: 20px; margin-bottom: 8px; }

.typing-indicator span { display: inline-block; width: 6px; height: 6px; background: #999; border-radius: 50%; margin: 0 2px; animation: typing 1.4s infinite ease-in-out both; }
.typing-indicator span:nth-child(1) { animation-delay: -0.32s; }
.typing-indicator span:nth-child(2) { animation-delay: -0.16s; }
@keyframes typing { 0%, 80%, 100% { transform: scale(0); } 40% { transform: scale(1); } }
</style>
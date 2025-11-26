<!-- src/components/ChatbotBall.vue -->
<script setup lang="ts">
import { SuspendedBallChat } from 'ai-suspended-ball-chat'

const chatbotApiUrl = 'http://localhost:8080/api/ai/chat'

const chatbotAppName = 'My AI Assistant'
const chatbotDomainName = 'user'
const chatbotStorageKey = 'my-chat-history'

const presetTasks = [
  {
    id: '1',
    icon: '💡',
    title: '创意写作',
    description: '帮助您进行创意写作和内容创作'
  },
  {
    id: '2',
    icon: '📊',
    title: '数据分析',
    description: '协助您进行数据分析和可视化'
  },
  {
    id: '3',
    icon: '🔧',
    title: '技术支持',
    description: '提供技术问题和编程帮助'
  }
]


// 这里可以根据需要做一些简单的回调，例如埋点、打印日志等
const callbacks = {
  // 每次用户发送消息
  onUserMessage(message: any) {
    console.log('[Chatbot] 用户消息：', message)
  },

  // 每次 AI 回复一条（在流式模式下可能会多次触发）
  onAssistantMessage(message: any) {
    console.log('[Chatbot] AI 回复：', message)
  },

  // 请求出错（网络错误 / 后端报错等）
  onError(error: unknown) {
    console.error('[Chatbot] 出错：', error)
  }
}
</script>

<template>
  <!-- 悬浮球 + 弹出聊天面板 -->
  <SuspendedBallChat
      :url="chatbotApiUrl"
      :app-name="chatbotAppName"
      :domain-name="chatbotDomainName"
      :enable-streaming="true"
      :enable-context="true"
      :enable-local-storage="true"
      :enable-voice-input="true"
      :storage-key="chatbotStorageKey"
      :preset-tasks="presetTasks"
      :callbacks="callbacks"
      :show-theme-toggle="true"
      :enable-image-upload="false"
  />

</template>

<script setup lang="ts">
import { computed, ref, onMounted } from 'vue'
import { useI18n } from 'vue-i18n'

const { locale } = useI18n()

// 语言切换
const isZh = computed({
  get: () => locale.value === 'zh-CN',
  set: (val: boolean) => {
    locale.value = val ? 'zh-CN' : 'en'
    localStorage.setItem('locale', locale.value)
  }
})

const toggleLang = () => {
  isZh.value = !isZh.value
}

// 主题切换：dark / light
const theme = ref<'dark' | 'light'>(
    (localStorage.getItem('theme') as 'dark' | 'light') || 'dark'
)

const isDark = computed({
  get: () => theme.value === 'dark',
  set: (val: boolean) => {
    theme.value = val ? 'dark' : 'light'
    document.documentElement.setAttribute('data-theme', theme.value)
    localStorage.setItem('theme', theme.value)
  }
})

const toggleTheme = () => {
  isDark.value = !isDark.value
}

onMounted(() => {
  // 初始化时应用主题
  document.documentElement.setAttribute('data-theme', theme.value)
})
</script>

<template>
  <el-header class="custom-header" height="60px">
    <el-row :gutter="10" align="middle" style="width: 100%; height: 100%;">
      <el-col :span="5" class="header-left">
        <div class="brand-container">
          <img
              src="/IoT-Verify.png"
              alt="IoT-Verify Logo"
              class="brand-logo"
          />
          <h1 class="brand-text">IoT-Verify</h1>
        </div>
      </el-col>

      <el-col :span="4" :offset="15" class="header-right">
        <el-button
            size="small"
            round
            class="lang-btn"
            style="margin-right: 8px"
            @click="toggleTheme"
        >
          <span v-if="isDark">🌙</span>
          <span v-else>☀️</span>
        </el-button>

        <el-button
            size="small"
            round
            class="lang-btn"
            @click="toggleLang"
        >
          <span v-if="isZh">中</span>
          <span v-else>EN</span>
        </el-button>
      </el-col>
    </el-row>
  </el-header>
</template>


<style scoped>
.custom-header {
  background: var(--iot-header-bg);
  border-bottom: 1px solid var(--iot-header-border);
  box-shadow: var(--iot-header-shadow);
  padding: 0 24px; /* 稍微增加两侧内边距 */
  /* 确保 header 内部元素垂直居中 */
  display: flex;
  align-items: center;
}

/* --- 左侧品牌区样式 --- */
.header-left {
  height: 100%;
  display: flex;
  align-items: center;
}

/* 品牌容器：核心布局 */
.brand-container {
  display: flex;
  align-items: center; /* 垂直居中对齐图标和文字 */
  gap: 12px; /* 图标和文字之间的间距 */
  transition: opacity 0.2s ease;
}

.brand-container:hover {
  opacity: 0.9;
}

/* Logo 图片样式 */
.brand-logo {
  height: 48px; /* 设置一个合适的高度，通常比 header 高度小一些 */
  width: auto;  /* 保持宽高比 */
  object-fit: contain;
}

/* 文字样式 */
.brand-text {
  color: var(--iot-color-title);
  font-size: 1.4rem; /* 稍微加大一点字体 */
  font-weight: 700;  /* 加粗 */
  letter-spacing: 0.04em;
  line-height: 1;    /* 紧凑的行高，便于与图标对齐 */
  /* 移除原有的 margin，依靠 flex 容器居中 */
  margin: 0;
  min-width: max-content;
  /* 可选：给文字加一点渐变效果，显得更现代（如果你的主题支持） */
  /* background: linear-gradient(90deg, var(--iot-color-title) 0%, var(--iot-primary-color, #6366f1) 100%); */
  /* -webkit-background-clip: text; */
  /* -webkit-text-fill-color: transparent; */
}

/* --- 右侧操作区样式 --- */
.header-right {
  display: flex;
  justify-content: flex-end;
  align-items: center;
  height: 100%;
}

/* 按钮样式保持不变 */
.lang-btn {
  font-weight: 600;
  letter-spacing: 1px;
  padding: 4px 12px;
  border-radius: 999px;
  border: 1px solid var(--iot-lang-btn-border);
  background: var(--iot-lang-btn-bg);
  color: var(--iot-lang-btn-text);
  box-shadow: var(--iot-lang-btn-shadow);
  transition:
      background 0.18s ease-out,
      box-shadow 0.18s ease-out,
      transform 0.12s ease-out;
}

.lang-btn:hover {
  background: var(--iot-lang-btn-hover-bg);
  box-shadow: 0 0.4rem 1.1rem rgba(15, 23, 42, 0.3);
  transform: translateY(-1px);
}

.lang-btn:active {
  transform: translateY(0);
  box-shadow: 0 0.1rem 0.6rem rgba(15, 23, 42, 0.3);
}
</style>
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
  <el-header class="custom-header" height="12">
    <el-row :gutter="10" align="middle" style="width: 100%">
      <el-col :span="3" class="header-icon">
        <h1 class="header-text">IoT-Verify</h1>
      </el-col>

      <el-col :span="3" :offset="18" class="header-lang">
        <!-- 主题切换按钮 -->
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

        <!-- 语言切换按钮 -->
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
  display: flex;
  flex-direction: column;
  padding: 0 16px;
}

/* 标题：用主题的 title 颜色 */
.header-text {
  color: var(--iot-color-title);
  font-size: 1.4rem;
  font-weight: 600;
  letter-spacing: 0.06em;
  min-width: max-content;
  margin-top: 12px;
  margin-bottom: 12px;
}

.header-icon {
  display: flex;
  flex-direction: column;
  align-items: flex-start;
  justify-content: center;
}

.header-lang {
  display: flex;
  justify-content: flex-end;
  align-items: center;
}

/* 语言按钮：全部改用变量 */
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


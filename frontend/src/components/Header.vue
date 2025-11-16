<script setup lang="ts">
import { computed } from 'vue'
import { useI18n } from 'vue-i18n'

const { locale } = useI18n()

// 用一个 computed 来表示“当前是不是中文”
const isZh = computed({
  get: () => locale.value === 'zh-CN',
  set: (val: boolean) => {
    locale.value = val ? 'zh-CN' : 'en'
    localStorage.setItem('locale', locale.value)  // 持久化一下，下次刷新保持语言
  }
})

const toggleLang = () => {
  isZh.value = !isZh.value
}
</script>

<template>
  <el-header class="custom-header" height="10">
    <el-row :gutter="10" align="middle" style="width: 100%">
      <el-col :span="3" class="header-icon">
        <h1 class="header-text">IoT-Verify</h1>
      </el-col>

      <!-- 右侧语言切换按钮 -->
      <el-col :span="3" :offset="18" class="header-lang">
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
  background: radial-gradient(circle at top left,
  rgba(15, 23, 42, 0.98),
  rgba(15, 23, 42, 0.96));
  border-bottom: 1px solid rgba(56, 189, 248, 0.55); /* 和卡片同色高光 */
  box-shadow: 0 10px 26px rgba(15, 23, 42, 0.9);
  display: flex;
  flex-direction: column;
  padding: 0 16px;
}

/* 标题：稍微亮一点，和浮动卡片标题统一 */
.header-text {
  color: var(--iot-color-title, #f9fafb);
  font-size: 1.4rem;
  font-weight: 600;
  letter-spacing: 0.06em;
  min-width: max-content;
  margin-top: 12px;
  margin-bottom: 12px;
}

/* 左侧 Logo 区 */
.header-icon {
  display: flex;
  flex-direction: column;
  align-items: flex-start;
  justify-content: center;
}

/* 右侧语言按钮区域靠右对齐 */
.header-lang {
  display: flex;
  justify-content: flex-end;
  align-items: center;
}

/* 语言按钮：青色描边 + 轻微渐变，悬停时填充高光 */
.lang-btn {
  font-weight: 600;
  letter-spacing: 1px;
  padding: 4px 12px;
  border-radius: 999px;
  border: 1px solid rgba(56, 189, 248, 0.9);
  background: radial-gradient(circle at top,
  rgba(15, 23, 42, 0.9),
  rgba(15, 23, 42, 0.98));
  color: #e0f2fe;
  box-shadow: 0 0 0 1px rgba(15, 23, 42, 0.8);
  transition: background 0.18s ease-out,
  box-shadow 0.18s ease-out,
  transform 0.12s ease-out;
}

.lang-btn:hover {
  background: linear-gradient(135deg,
  rgba(56, 189, 248, 0.28),
  rgba(37, 99, 235, 0.45));
  box-shadow: 0 0.4rem 1.1rem rgba(15, 23, 42, 0.9);
  transform: translateY(-1px);
}

.lang-btn:active {
  transform: translateY(0);
  box-shadow: 0 0.1rem 0.6rem rgba(15, 23, 42, 0.9);
}
</style>


<script setup lang="ts">
import { computed, ref, onMounted } from 'vue';
import { useRouter } from 'vue-router';
import { ElMessageBox } from 'element-plus';
import { useI18n } from 'vue-i18n';
import { useAuth } from '@/stores/auth';
import { authApi } from '@/api/auth';

const { locale } = useI18n();
const router = useRouter();
const { state, logout, getUser } = useAuth();

// 语言切换
const isZh = computed({
  get: () => locale.value === 'zh-CN',
  set: (val: boolean) => {
    locale.value = val ? 'zh-CN' : 'en';
    localStorage.setItem('locale', locale.value);
  }
});

const toggleLang = () => {
  isZh.value = !isZh.value;
};

// 主题切换：dark / light
const theme = ref<'dark' | 'light'>(
  (localStorage.getItem('theme') as 'dark' | 'light') || 'dark'
);

const isDark = computed({
  get: () => theme.value === 'dark',
  set: (val: boolean) => {
    theme.value = val ? 'dark' : 'light';
    document.documentElement.setAttribute('data-theme', theme.value);
    localStorage.setItem('theme', theme.value);
  }
});

const toggleTheme = () => {
  isDark.value = !isDark.value;
};

onMounted(() => {
  document.documentElement.setAttribute('data-theme', theme.value);
});

// 用户相关
const currentUser = computed(() => getUser());
const isLoggedIn = computed(() => state.isLoggedIn);

const handleLogout = async () => {
  try {
    await ElMessageBox.confirm(
      isZh.value ? '确定要退出登录吗？' : 'Are you sure you want to log out?',
      isZh.value ? '提示' : 'Confirm',
      { type: 'warning' }
    );
    
    // 调用登出API（可选，失败也清除本地状态）
    try {
      await authApi.logout();
    } catch {
      // API失败不影响本地登出
    }
    
    logout();
    ElMessageBox.close();
    router.push('/login');
  } catch {
    // 用户取消
  }
};

const goToLogin = () => {
  router.push('/login');
};

const goToRegister = () => {
  router.push('/register');
};
</script>

<template>
  <el-header class="custom-header" height="60px">
    <el-row :gutter="10" align="middle" style="width: 100%; height: 100%;">
      <el-col :span="4" class="header-left">
        <div class="brand-container" @click="router.push('/board')">
          <img
            src="/IoT-Verify.png"
            alt="IoT-Verify Logo"
            class="brand-logo"
          />
          <h1 class="brand-text">IoT-Verify</h1>
        </div>
      </el-col>

      <el-col :span="20" class="header-right">
        <!-- 登录状态显示 -->
        <template v-if="isLoggedIn">
          <div class="user-info">
            <el-avatar :size="32" class="user-avatar">
              {{ currentUser?.username?.charAt(0)?.toUpperCase() }}
            </el-avatar>
            <span class="username">{{ currentUser?.username }}</span>
          </div>
          
          <el-button
            size="small"
            round
            class="header-btn"
            @click="handleLogout"
          >
            {{ isZh ? '退出登录' : 'Logout' }}
          </el-button>
        </template>
        
        <!-- 未登录状态显示 -->
        <template v-else>
          <el-button
            size="small"
            round
            class="header-btn"
            @click="goToLogin"
          >
            {{ isZh ? '登录' : 'Login' }}
          </el-button>
          
          <el-button
            size="small"
            round
            type="primary"
            class="header-btn"
            @click="goToRegister"
          >
            {{ isZh ? '注册' : 'Register' }}
          </el-button>
        </template>

        <el-button
          size="small"
          round
          class="theme-btn"
          style="margin-left: 12px"
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

<script lang="ts">
export default {
  name: 'Header'
};
</script>

<style scoped>
.custom-header {
  background: var(--iot-header-bg);
  border-bottom: 1px solid var(--iot-header-border);
  box-shadow: var(--iot-header-shadow);
  padding: 0 24px;
  display: flex;
  align-items: center;
}

.header-left {
  height: 100%;
  display: flex;
  align-items: center;
}

.brand-container {
  display: flex;
  align-items: center;
  gap: 12px;
  cursor: pointer;
  transition: opacity 0.2s ease;
}

.brand-container:hover {
  opacity: 0.9;
}

.brand-logo {
  height: 40px;
  width: auto;
  object-fit: contain;
  border-radius: 8px;
}

.brand-text {
  color: var(--iot-color-title);
  font-size: 1.2rem;
  font-weight: 700;
  letter-spacing: 0.04em;
  line-height: 1;
  margin: 0;
}

.header-right {
  display: flex;
  justify-content: flex-end;
  align-items: center;
  height: 100%;
  gap: 8px;
}

.user-info {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-right: 8px;
  padding-right: 16px;
  border-right: 1px solid var(--iot-header-border);
}

.user-avatar {
  background: linear-gradient(135deg, #6366f1, #8b5cf6);
  color: white;
  font-weight: 600;
}

.username {
  color: var(--iot-color-title);
  font-size: 14px;
  font-weight: 500;
  max-width: 100px;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.header-btn {
  font-weight: 600;
  letter-spacing: 1px;
  transition: all 0.2s ease;
}

.theme-btn,
.lang-btn {
  font-weight: 600;
  letter-spacing: 1px;
  padding: 4px 12px;
  border-radius: 999px;
  border: 1px solid var(--iot-lang-btn-border);
  background: var(--iot-lang-btn-bg);
  color: var(--iot-lang-btn-text);
  box-shadow: var(--iot-lang-btn-shadow);
  transition: all 0.18s ease-out;
}

.theme-btn:hover,
.lang-btn:hover {
  background: var(--iot-lang-btn-hover-bg);
  box-shadow: 0 0.4rem 1.1rem rgba(15, 23, 42, 0.3);
  transform: translateY(-1px);
}

.theme-btn:active,
.lang-btn:active {
  transform: translateY(0);
}
</style>

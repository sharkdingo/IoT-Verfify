<script setup lang="ts">
import { computed, ref, onMounted } from 'vue';
import { useRouter } from 'vue-router';
import { useAuth } from '@/stores/auth';
import { authApi } from '@/api/auth';
import LogoutConfirm from './LogoutConfirm.vue';

const router = useRouter();
const { state, logout, getUser } = useAuth();
const showLogoutConfirm = ref(false);

// 移除主题切换功能，固定使用亮色主题
onMounted(() => {
  document.documentElement.setAttribute('data-theme', 'light');
});

// 用户相关
const currentUser = computed(() => getUser());
const isLoggedIn = computed(() => state.isLoggedIn);

const handleLogout = async () => {
  showLogoutConfirm.value = true;
};

const confirmLogout = async () => {
  // 调用登出API（可选，失败也清除本地状态）
  try {
    await authApi.logout();
  } catch {
    // API失败不影响本地登出
  }

  logout();
  router.push('/login');
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
            <div class="user-avatar-container">
              <el-avatar :size="36" class="user-avatar">
                {{ currentUser?.username?.charAt(0)?.toUpperCase() }}
              </el-avatar>
              <div class="online-indicator"></div>
            </div>
            <div class="user-details">
              <span class="username">{{ currentUser?.username }}</span>
              <span class="user-role">User</span>
            </div>
          </div>
          
          <el-button
            size="default"
            round
            class="logout-btn"
            @click="handleLogout"
          >
            <span class="material-symbols-outlined text-lg">logout</span>
            <span>Logout</span>
          </el-button>
        </template>
        
        <!-- 未登录状态显示 -->
        <template v-else>
          <el-button
            size="default"
            round
            class="login-btn"
            @click="goToLogin"
          >
            <span class="material-symbols-outlined text-lg">login</span>
            <span>Login</span>
          </el-button>

          <el-button
            size="default"
            round
            type="primary"
            class="register-btn"
            @click="goToRegister"
          >
            <span class="material-symbols-outlined text-lg">person_add</span>
            <span>Register</span>
          </el-button>
        </template>


      </el-col>
    </el-row>
    
    <!-- Logout Confirmation Modal -->
    <LogoutConfirm 
      v-model:visible="showLogoutConfirm" 
      @confirm="confirmLogout" 
    />
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
  transition: all 0.2s ease;
}

.brand-container:hover {
  opacity: 0.9;
  transform: scale(1.02);
}

.brand-logo {
  height: 40px;
  width: auto;
  object-fit: contain;
  border-radius: 10px;
  box-shadow: 0 2px 8px rgba(99, 102, 241, 0.2);
}

.brand-text {
  color: var(--iot-color-title);
  font-size: 1.25rem;
  font-weight: 700;
  letter-spacing: 0.04em;
  line-height: 1;
  margin: 0;
  background: linear-gradient(135deg, #6366f1, #8b5cf6);
  -webkit-background-clip: text;
  -webkit-text-fill-color: transparent;
  background-clip: text;
}

.header-right {
  display: flex;
  justify-content: flex-end;
  align-items: center;
  height: 100%;
  gap: 12px;
}

.user-info {
  display: flex;
  align-items: center;
  gap: 12px;
  margin-right: 8px;
  padding: 6px 16px 6px 6px;
  background: linear-gradient(to right, rgba(99, 102, 241, 0.08), transparent);
  border-radius: 50px;
  border: 1px solid rgba(99, 102, 241, 0.1);
}

.user-avatar-container {
  position: relative;
}

.user-avatar {
  background: linear-gradient(135deg, #6366f1, #8b5cf6);
  color: white;
  font-weight: 600;
  border: 2px solid white;
  box-shadow: 0 2px 8px rgba(99, 102, 241, 0.3);
}

.online-indicator {
  position: absolute;
  bottom: 0;
  right: 0;
  width: 10px;
  height: 10px;
  background: #22c55e;
  border: 2px solid white;
  border-radius: 50%;
}

.user-details {
  display: flex;
  flex-direction: column;
  gap: 0;
}

.username {
  color: var(--iot-color-title);
  font-size: 14px;
  font-weight: 600;
  line-height: 1.2;
}

.user-role {
  color: #9ca3af;
  font-size: 11px;
  font-weight: 500;
  text-transform: uppercase;
  letter-spacing: 0.05em;
}

.logout-btn {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 16px;
  background: white;
  border: 1px solid #e5e7eb;
  color: #6b7280;
  font-weight: 500;
  transition: all 0.2s;
}

.logout-btn:hover {
  background: #f9fafb;
  border-color: #d1d5db;
  color: #374151;
  transform: translateY(-1px);
  box-shadow: 0 2px 8px rgba(0, 0, 0, 0.08);
}

.login-btn {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 20px;
  background: white;
  border: 1px solid #e5e7eb;
  color: #374151;
  font-weight: 500;
  transition: all 0.2s;
}

.login-btn:hover {
  background: #f9fafb;
  border-color: #6366f1;
  color: #6366f1;
  transform: translateY(-1px);
  box-shadow: 0 2px 8px rgba(99, 102, 241, 0.15);
}

.register-btn {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 20px;
  background: linear-gradient(135deg, #6366f1, #8b5cf6);
  border: none;
  color: white;
  font-weight: 500;
  transition: all 0.2s;
}

.register-btn:hover {
  background: linear-gradient(135deg, #4f46e5, #7c3aed);
  transform: translateY(-1px);
  box-shadow: 0 4px 12px rgba(99, 102, 241, 0.4);
}

.header-btn {
  font-weight: 600;
  letter-spacing: 1px;
  transition: all 0.2s ease;
}

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

.lang-btn:hover {
  background: var(--iot-lang-btn-hover-bg);
  box-shadow: 0 0.4rem 1.1rem rgba(15, 23, 42, 0.3);
  transform: translateY(-1px);
}

.lang-btn:active {
  transform: translateY(0);
}
</style>

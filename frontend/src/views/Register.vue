<script setup lang="ts">
import { ref, reactive } from 'vue';
import { useRouter } from 'vue-router';
import { ElMessage } from 'element-plus';
import { authApi } from '@/api/auth';
import { useI18n } from 'vue-i18n';

const { t } = useI18n();
const router = useRouter();

const loading = ref(false);
const formRef = ref();

const form = reactive({
  phone: '',
  username: '',
  password: '',
  confirmPassword: ''
});

const rules = {
  phone: [
    { required: true, message: t('auth.phoneRequired'), trigger: 'blur' },
    { pattern: /^1[3-9]\d{9}$/, message: t('auth.phoneInvalid'), trigger: 'blur' }
  ],
  username: [
    { required: true, message: t('auth.usernameRequired'), trigger: 'blur' },
    { min: 3, max: 20, message: t('auth.usernameLength'), trigger: 'blur' }
  ],
  password: [
    { required: true, message: t('auth.passwordRequired'), trigger: 'blur' },
    { min: 6, max: 20, message: t('auth.passwordLength'), trigger: 'blur' }
  ],
  confirmPassword: [
    { required: true, message: t('auth.confirmPasswordRequired'), trigger: 'blur' },
    {
      validator: (_rule: unknown, value: string, callback: Function) => {
        if (value !== form.password) {
          callback(new Error(t('auth.passwordMismatch')));
        } else {
          callback();
        }
      },
      trigger: 'blur'
    }
  ]
};

const handleRegister = async () => {
  if (!formRef.value) return;
  
  await formRef.value.validate(async (valid: boolean) => {
    if (!valid) return;
    
    loading.value = true;
    try {
      const res = await authApi.register({
        phone: form.phone,
        username: form.username,
        password: form.password
      });
      
      if (res.code === 200) {
        ElMessage.success(t('auth.registerSuccess'));
        router.push('/login');
      } else {
        ElMessage.error(res.message || t('auth.registerFailed'));
      }
    } catch (error: unknown) {
      console.error('Register error:', error);
      let errorMsg = t('auth.registerFailed');
      if (error && typeof error === 'object' && 'response' in error) {
        const err = error as { response?: { data?: { message?: string } } };
        if (err.response?.data?.message) {
          errorMsg = err.response.data.message;
        }
      } else if (error instanceof Error) {
        errorMsg = error.message;
      }
      ElMessage.error(errorMsg);
    } finally {
      loading.value = false;
    }
  });
};

const goToLogin = () => {
  router.push('/login');
};
</script>

<template>
  <div class="auth-container">
    <div class="auth-card">
      <!-- Logo区域 -->
      <div class="auth-header">
        <img src="/IoT-Verify.png" alt="Logo" class="auth-logo" />
        <h1 class="auth-title">IoT-Verify</h1>
        <p class="auth-subtitle">{{ t('auth.createAccount') }}</p>
      </div>
      
      <!-- 表单区域 -->
      <el-form
        ref="formRef"
        :model="form"
        :rules="rules"
        class="auth-form"
        size="large"
      >
        <el-form-item prop="phone">
          <el-input
            v-model="form.phone"
            :placeholder="t('auth.phonePlaceholder')"
            prefix-icon="Phone"
            clearable
          />
        </el-form-item>
        
        <el-form-item prop="username">
          <el-input
            v-model="form.username"
            :placeholder="t('auth.usernamePlaceholder')"
            prefix-icon="User"
            clearable
          />
        </el-form-item>
        
        <el-form-item prop="password">
          <el-input
            v-model="form.password"
            :placeholder="t('auth.passwordPlaceholder')"
            type="password"
            prefix-icon="Lock"
            show-password
          />
        </el-form-item>
        
        <el-form-item prop="confirmPassword">
          <el-input
            v-model="form.confirmPassword"
            :placeholder="t('auth.confirmPasswordPlaceholder')"
            type="password"
            prefix-icon="Lock"
            show-password
            @keyup.enter="handleRegister"
          />
        </el-form-item>
        
        <el-form-item>
          <el-button
            type="primary"
            :loading="loading"
            class="auth-btn"
            @click="handleRegister"
          >
            {{ t('auth.register') }}
          </el-button>
        </el-form-item>
      </el-form>
      
      <!-- 底部链接 -->
      <div class="auth-footer">
        <span class="auth-link-text">{{ t('auth.haveAccount') }}</span>
        <el-link type="primary" @click="goToLogin">
          {{ t('auth.loginNow') }}
        </el-link>
      </div>
    </div>
    
    <!-- 装饰背景 -->
    <div class="auth-decoration">
      <div class="decoration-circle circle-1"></div>
      <div class="decoration-circle circle-2"></div>
      <div class="decoration-circle circle-3"></div>
    </div>
  </div>
</template>

<style scoped>
.auth-container {
  min-height: 100vh;
  display: flex;
  align-items: center;
  justify-content: center;
  background: var(--iot-color-bg-body);
  position: relative;
  overflow: hidden;
  transition: background-color 0.3s ease;
}

.auth-card {
  width: 440px;
  padding: 48px 40px;
  background: var(--iot-color-card-bg);
  border: 1px solid var(--iot-color-card-border);
  border-radius: var(--iot-radius-card);
  box-shadow: var(--iot-color-card-shadow);
  position: relative;
  z-index: 10;
  backdrop-filter: blur(10px);
  transition: all 0.3s ease;
}

.auth-header {
  text-align: center;
  margin-bottom: 32px;
}

.auth-logo {
  width: 72px;
  height: 72px;
  margin-bottom: 16px;
  border-radius: 16px;
  box-shadow: var(--iot-node-shadow);
}

.auth-title {
  font-size: 28px;
  font-weight: 700;
  color: var(--iot-color-title);
  margin: 0 0 8px;
  letter-spacing: -0.5px;
}

.auth-subtitle {
  font-size: 15px;
  color: var(--iot-color-text-muted);
  margin: 0;
}

.auth-form {
  margin-bottom: 24px;
}

.auth-btn {
  width: 100%;
  height: 48px;
  font-size: 16px;
  font-weight: 600;
  border-radius: var(--iot-radius-input);
  background: linear-gradient(135deg, #6366f1 0%, #8b5cf6 100%);
  border: none;
  transition: all 0.3s ease;
}

.auth-btn:hover {
  transform: translateY(-2px);
  box-shadow: 0 8px 25px rgba(99, 102, 241, 0.4);
}

.auth-footer {
  text-align: center;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 8px;
}

.auth-link-text {
  font-size: 14px;
  color: var(--iot-color-text-muted);
}

/* 装饰背景 */
.auth-decoration {
  position: absolute;
  inset: 0;
  pointer-events: none;
}

.decoration-circle {
  position: absolute;
  border-radius: 50%;
  background: linear-gradient(135deg, rgba(99, 102, 241, 0.15), rgba(139, 92, 246, 0.08));
  backdrop-filter: blur(60px);
}

.circle-1 {
  width: 400px;
  height: 400px;
  top: -100px;
  left: -100px;
}

.circle-2 {
  width: 300px;
  height: 300px;
  bottom: -50px;
  right: -50px;
}

.circle-3 {
  width: 200px;
  height: 200px;
  top: 50%;
  left: 50%;
  transform: translate(-50%, -50%);
}

/* Element Plus 覆盖样式 - 使用主题变量 */
:deep(.el-input__wrapper) {
  border-radius: var(--iot-radius-input);
  padding: 4px 16px;
  background: var(--iot-color-input-bg);
  box-shadow: 0 0 0 1px var(--iot-color-input-border);
  transition: all 0.3s ease;
}

:deep(.el-input__wrapper:hover) {
  box-shadow: 0 0 0 2px rgba(99, 102, 241, 0.2);
}

:deep(.el-input__wrapper.is-focus) {
  box-shadow: 0 0 0 2px rgba(99, 102, 241, 0.4);
}

:deep(.el-form-item) {
  margin-bottom: 20px;
}

:deep(.el-input__prefix) {
  color: var(--iot-color-text-muted);
}

:deep(.el-input__inner) {
  height: 48px;
  font-size: 15px;
  color: var(--iot-color-text);
  background: transparent;
}

:deep(.el-input__inner::placeholder) {
  color: var(--iot-color-text-muted);
}

:deep(.el-form-item__error) {
  color: #ef4444;
}

/* 亮色主题下的卡片样式 */
:root[data-theme='light'] .auth-card {
  background: rgba(255, 255, 255, 0.9);
  border-color: rgba(148, 163, 184, 0.55);
}
</style>

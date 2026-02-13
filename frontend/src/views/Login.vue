<script setup lang="ts">
import { ref, reactive } from 'vue';
import { useRouter, useRoute } from 'vue-router';
import { ElMessage } from 'element-plus';
import { authApi } from '@/api/auth';
import { useAuth } from '@/stores/auth';
import { useI18n } from 'vue-i18n';

const { t } = useI18n();
const router = useRouter();
const route = useRoute();
const { login } = useAuth();

const loading = ref(false);
const formRef = ref();

const form = reactive({
  phone: '',
  password: ''
});

const rules = {
  phone: [
    { required: true, message: t('auth.phoneRequired'), trigger: 'blur' },
    { pattern: /^1[3-9]\d{9}$/, message: t('auth.phoneInvalid'), trigger: 'blur' }
  ],
  password: [
    { required: true, message: t('auth.passwordRequired'), trigger: 'blur' }
  ]
};

const handleLogin = async () => {
  if (!formRef.value) return;
  
  await formRef.value.validate(async (valid: boolean) => {
    if (!valid) return;
    
    loading.value = true;
    try {
      const res = await authApi.login({
        phone: form.phone,
        password: form.password
      });
      
      if (res.code === 200) {
        login(res.data.token, {
          userId: res.data.userId,
          phone: res.data.phone,
          username: res.data.username
        });
        
        ElMessage.success(t('auth.loginSuccess'));
        
        const redirect = route.query.redirect as string;
        router.push(redirect || '/board');
      } else {
        ElMessage.error(res.message || t('auth.loginFailed'));
      }
    } catch (error: any) {
      console.error('Login error:', error);
      let errorMsg = t('auth.loginFailed');
      if (error.response?.data?.message) {
        errorMsg = error.response.data.message;
      } else if (error.response?.status === 401) {
        errorMsg = t('auth.loginFailed');
      } else if (error.message) {
        errorMsg = error.message;
      }
      ElMessage.error(errorMsg);
    } finally {
      loading.value = false;
    }
  });
};

const goToRegister = () => {
  router.push('/register');
};
</script>

<template>
  <div class="auth-wrapper">
    <!-- Left Side - Branding -->
    <div class="brand-panel">
      <div class="bg-effects">
        <div class="grid-pattern"></div>
        <div class="gradient-overlay"></div>
        <div class="glow-blue top-left"></div>
        <div class="glow-indigo bottom-right"></div>
      </div>

      <div class="brand-content">
        <div class="brand-header">
          <div class="brand-logo">
            <svg fill="none" viewBox="0 0 48 48" xmlns="http://www.w3.org/2000/svg">
              <path clip-rule="evenodd" d="M24 18.4228L42 11.475V34.3663C42 34.7796 41.7457 35.1504 41.3601 35.2992L24 42V18.4228Z" fill="currentColor" fill-rule="evenodd"></path>
              <path clip-rule="evenodd" d="M24 8.18819L33.4123 11.574L24 15.2071L14.5877 11.574L24 8.18819ZM9 15.8487L21 20.4805V37.6263L9 32.9945V15.8487ZM27 37.6263V20.4805L39 15.8487V32.9945L27 37.6263ZM25.354 2.29885C24.4788 1.98402 23.5212 1.98402 22.646 2.29885L4.98454 8.65208C3.7939 9.08038 3 10.2097 3 11.475V34.3663C3 36.0196 4.01719 37.5026 5.55962 38.098L22.9197 44.7987C23.6149 45.0671 24.3851 45.0671 25.0803 44.7987L42.4404 38.098C43.9828 37.5026 45 36.0196 45 34.3663V11.475C45 10.2097 44.2061 9.08038 43.0155 8.65208L25.354 2.29885Z" fill="currentColor" fill-rule="evenodd"></path>
            </svg>
          </div>
          <span class="brand-name">IoT Verify</span>
        </div>

        <div class="hero-text">
          <h2>Orchestrate Your <br/><span>Environment</span></h2>
          <p>Advanced canvas-based logic for the modern smart home. Connect, automate, and visualize your entire device network in real-time.</p>
        </div>

        <div class="hero-image-placeholder">
          <img src="/IoT-Verify.png" alt="IoT-Verify Logo" class="hero-logo">
        </div>

        <div class="stats-row">
          <div class="stat-card">
            <div class="stat-icon"><span class="material-symbols-outlined">speed</span></div>
            <div class="stat-label">Uptime</div>
            <div class="stat-value">99.9<span>%</span></div>
          </div>
          <div class="stat-card">
            <div class="stat-icon"><span class="material-symbols-outlined">devices</span></div>
            <div class="stat-label">Devices</div>
            <div class="stat-value">1.2k<span>+</span></div>
          </div>
        </div>
      </div>
    </div>

    <!-- Right Side - Login Form -->
    <div class="form-panel">
      <div class="mobile-header">
        <div class="brand-logo">
          <svg fill="none" viewBox="0 0 48 48" xmlns="http://www.w3.org/2000/svg">
            <path clip-rule="evenodd" d="M24 18.4228L42 11.475V34.3663C42 34.7796 41.7457 35.1504 41.3601 35.2992L24 42V18.4228Z" fill="currentColor" fill-rule="evenodd"></path>
            <path clip-rule="evenodd" d="M24 8.18819L33.4123 11.574L24 15.2071L14.5877 11.574L24 8.18819ZM9 15.8487L21 20.4805V37.6263L9 32.9945V15.8487ZM27 37.6263V20.4805L39 15.8487V32.9945L27 37.6263ZM25.354 2.29885C24.4788 1.98402 23.5212 1.98402 22.646 2.29885L4.98454 8.65208C3.7939 9.08038 3 10.2097 3 11.475V34.3663C3 36.0196 4.01719 37.5026 5.55962 38.098L22.9197 44.7987C23.6149 45.0671 24.3851 45.0671 25.0803 44.7987L42.4404 38.098C43.9828 37.5026 45 36.0196 45 34.3663V11.475C45 10.2097 44.2061 9.08038 43.0155 8.65208L25.354 2.29885Z" fill="currentColor" fill-rule="evenodd"></path>
          </svg>
        </div>
        <span class="brand-name">IoT Verify</span>
      </div>

      <div class="form-container">
        <div class="form-header">
          <h3>Welcome Back</h3>
          <p>Please enter your account details below.</p>
        </div>

        <el-form
          ref="formRef"
          :model="form"
          :rules="rules"
          class="auth-form"
        >
          <div class="form-group">
            <label>Phone Number</label>
            <div class="input-wrapper">
              <div class="input-icon">
                <span class="material-symbols-outlined">phone</span>
              </div>
              <el-input
                v-model="form.phone"
                placeholder="Please enter your phone number"
                class="custom-input"
                @keyup.enter="handleLogin"
              />
            </div>
          </div>

          <div class="form-group">
            <div class="label-row">
              <label>Password</label>
              <a href="#" class="forgot-link">Forgot password?</a>
            </div>
            <div class="input-wrapper">
              <div class="input-icon">
                <span class="material-symbols-outlined">lock_open</span>
              </div>
              <el-input
                v-model="form.password"
                type="password"
                placeholder="Enter password"
                class="custom-input"
                show-password
                @keyup.enter="handleLogin"
              />
            </div>
          </div>

          <div class="form-group">
            <button
              type="button"
              class="submit-btn"
              :loading="loading"
              @click="handleLogin"
            >
              Sign In to Console
            </button>
          </div>
        </el-form>

        <!-- Login Link -->
        <div class="register-link">
          <span>Don't have an account?</span>
          <button @click="goToRegister">Sign up</button>
        </div>
      </div>
    </div>
  </div>
</template>

<style>
/* Component-specific overrides for Login page */
.auth-wrapper {
  display: flex;
  width: 100%;
  height: 100%;
  background-color: var(--bg-page);
  overflow: hidden;
}

/* --- Left Panel (Branding) --- */
.brand-panel {
  display: none; /* Hidden on mobile by default */
  width: var(--brand-panel-width);
  position: relative;
  background-color: var(--bg-brand-panel);
  flex-direction: column;
  justify-content: space-between;
  padding: 3rem;
  overflow: hidden;
  border-right: 1px solid #f1f5f9;
}

@media (min-width: 1024px) {
  .brand-panel {
    display: flex;
  }
}

.bg-effects {
  position: absolute;
  inset: 0;
  z-index: 0;
  pointer-events: none;
}

.grid-pattern {
  position: absolute;
  inset: 0;
  background-image: radial-gradient(circle, #cbd5e1 1px, transparent 1px);
  background-size: 30px 30px;
  opacity: 0.4;
}

.gradient-overlay {
  position: absolute;
  inset: 0;
  background: linear-gradient(to bottom right, rgba(219, 234, 254, 0.5), rgba(255, 255, 255, 0.5));
}

.glow-blue {
  position: absolute;
  width: 50%;
  height: 50%;
  background: #bfdbfe;
  filter: blur(100px);
  border-radius: 50%;
  top: -10%;
  left: -10%;
}

.brand-content {
  position: relative;
  z-index: 10;
  display: flex;
  flex-direction: column;
  height: 100%;
  justify-content: space-between;
}

.brand-header {
  display: flex;
  align-items: center;
  gap: 0.75rem;
  color: var(--text-primary);
  margin-bottom: 3rem;
}

.brand-logo svg {
  width: 36px;
  height: 36px;
  color: var(--color-primary);
}

.brand-logo {
  background: white;
  padding: 4px;
  border-radius: 8px;
  box-shadow: 0 1px 3px rgba(0,0,0,0.1);
  display: flex;
  align-items: center;
  justify-content: center;
}

.brand-name {
  font-size: 1.5rem;
  font-weight: 700;
  letter-spacing: -0.025em;
}

.hero-text h2 {
  font-size: 3rem; /* Keeping close to Register's 3rem but slightly adjusted if needed via variable */
  line-height: 1.1;
  font-weight: 700;
  color: var(--text-primary);
  margin-bottom: 1rem;
}

.hero-text h2 span {
  color: var(--color-primary);
}

.hero-text p {
  font-size: 1.125rem;
  color: var(--text-secondary);
  max-width: 36rem;
  line-height: 1.6;
}

.hero-image-placeholder {
  position: relative;
  width: 100%;
  height: 300px; /* Adjusted to match Register */
  display: flex;
  align-items: center;
  justify-content: center;
  margin: 2rem 0;
}

.hero-logo {
  max-width: 80%;
  max-height: 120%;
  object-fit: contain;
  filter: drop-shadow(0 20px 50px rgba(0,0,0,0.1));
  transition: transform 0.3s ease;
}

.hero-logo:hover {
  transform: scale(1.02);
}

.stats-row {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 1.5rem;
}

.stat-card {
  background: rgba(255, 255, 255, 0.6);
  backdrop-filter: blur(12px);
  padding: 1.25rem;
  border-radius: 16px;
  border: 1px solid #bfdbfe;
  box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05);
}

.stat-icon {
  color: var(--color-primary);
  margin-bottom: 0.5rem;
}

.stat-icon .material-symbols-outlined {
  font-size: 24px;
}

.stat-label {
  font-size: 0.75rem;
  font-weight: 700;
  text-transform: uppercase;
  letter-spacing: 0.05em;
  color: var(--text-secondary);
  margin-bottom: 0.25rem;
}

.stat-value {
  font-size: 2rem;
  font-weight: 700;
  color: var(--text-primary);
}

.stat-value span {
  font-size: 1.25rem;
  color: var(--color-primary);
}

/* --- Right Panel (Form) --- */
.form-panel {
  width: 100%;
  display: flex;
  flex-direction: column;
  background-color: var(--bg-form-panel);
  position: relative;
  z-index: 10;
}

@media (min-width: 1024px) {
  .form-panel {
    width: var(--form-panel-width);
  }
}

.mobile-header {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 0.5rem;
  padding-top: 3rem;
  padding-bottom: 2rem;
}

@media (min-width: 1024px) {
  .mobile-header {
    display: none;
  }
}

.mobile-header .brand-logo {
  width: 32px;
  height: 32px;
}

.mobile-header .brand-logo svg {
  width: 20px;
  height: 20px;
}

.mobile-header .brand-name {
  font-size: 1.25rem;
  color: var(--text-primary);
}

.form-container {
  flex: 1;
  display: flex;
  flex-direction: column;
  justify-content: center;
  padding: 2rem 3rem;
  max-width: 36rem;
  margin: 0 auto;
  width: 100%;
}

.form-header {
  margin-bottom: 2rem;
}

.form-header h3 {
  font-size: 1.5rem;
  font-weight: 700;
  color: var(--text-primary);
  letter-spacing: -0.025em;
  margin-bottom: 0.5rem;
}

.form-header p {
  font-size: 1rem;
  color: var(--text-secondary);
  font-weight: 500;
}

.form-group {
  margin-bottom: 1.5rem;
}

.form-group label {
  display: block;
  font-size: 0.875rem;
  font-weight: 700;
  color: var(--text-label);
  margin-bottom: 0.5rem;
}

.label-row {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: 0.5rem;
}

.forgot-link {
  font-size: 0.75rem;
  font-weight: 700;
  color: var(--color-primary);
  text-decoration: none;
}

.forgot-link:hover {
  color: var(--color-primary-hover);
}

.input-wrapper {
  position: relative;
  display: flex;
  align-items: center;
}

.input-icon {
  position: absolute;
  left: 1rem;
  display: flex;
  align-items: center;
  justify-content: center;
  color: #94a3b8;
  z-index: 10;
  pointer-events: none;
  transition: color 0.2s;
}

.input-wrapper:focus-within .input-icon {
  color: var(--color-primary);
}

.custom-input {
  width: 100%;
  height: 3rem;
  background-color: var(--bg-input);
  border: 1px solid var(--border-color);
  border-radius: var(--radius-md);
  color: var(--text-primary);
  font-size: 0.875rem;
  padding-left: 3rem !important; /* pl-12 */
  padding-right: 1rem;
  transition: all 0.2s;
}

.custom-input:hover {
  background-color: var(--bg-input-hover);
  border-color: var(--border-color-hover);
}

.custom-input:focus {
  background-color: var(--bg-input-hover);
  border-color: var(--border-focus);
  box-shadow: 0 0 0 4px rgba(59, 130, 246, 0.1) !important;
  outline: none;
}

.custom-input input {
  background-color: transparent;
  border: none;
  height: 100%;
  width: 100%;
  padding: 0;
  color: var(--text-primary);
  font-size: 0.875rem;
}

.custom-input input:focus {
  outline: none;
  box-shadow: none;
}

.submit-btn {
  width: 100%;
  padding-top: 1rem;
  padding-bottom: 1rem;
  background-color: var(--color-primary);
  color: white;
  font-size: 0.875rem;
  font-weight: 700;
  border: none;
  border-radius: var(--radius-md);
  cursor: pointer;
  box-shadow: 0 10px 15px -3px rgba(37, 99, 235, 0.2);
  transition: all 0.2s;
  margin-top: 1rem;
  display: flex;
  justify-content: center;
  align-items: center;
}

.submit-btn:hover {
  background-color: var(--color-primary-hover);
  transform: translateY(-1px);
  box-shadow: 0 20px 25px -5px rgba(37, 99, 235, 0.2);
}

.submit-btn:active {
  transform: translateY(0);
}

.register-link {
  text-align: center;
  display: flex;
  justify-content: center;
  gap: 0.5rem;
  align-items: center;
}

.register-link span {
  font-size: 0.875rem;
  font-weight: 500;
  color: var(--text-secondary);
}

.register-link button {
  background: none;
  border: none;
  color: var(--color-primary);
  font-size: 0.875rem;
  font-weight: 700;
  cursor: pointer;
}

.register-link button:hover {
  color: var(--color-primary-hover);
  text-decoration: underline;
}

@keyframes pulse {
  0% { opacity: 1; }
  50% { opacity: 0.5; }
  100% { opacity: 1; }
}
</style>

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
  <div class="auth-wrapper">
    <!-- Left Panel (Branding) -->
    <div class="brand-panel">
      <!-- Video Background -->
      <video
        class="brand-video-bg"
        autoplay
        loop
        muted
        playsinline
      >
        <source src="https://cdn.pixabay.com/video/2019/10/10/27725-365890983_large.mp4" type="video/mp4">
      </video>
      
      <div class="video-overlay"></div>
      
      <div class="bg-effects">
        <div class="grid-pattern"></div>
        <div class="gradient-overlay"></div>
        <div class="glow-blue"></div>
      </div>

      <div class="brand-content">
        <!-- Logo -->
        <div class="logo">
          IoT-Verify<sup class="logo-sup">®</sup>
        </div>

        <!-- Hero Text -->
        <div class="hero-text">
          <h2>Master Your <br/><span>Smart Ecosystem</span></h2>
          <p>Join the world's most advanced IoT management platform. Connect, automate, and scale your network with ease.</p>
        </div>

        <!-- Hero Image Placeholder -->
        <div class="hero-image-placeholder">
             <img src="/IoT-Verify.png" alt="IoT-Verify Logo" class="hero-logo">
        </div>

        <!-- Stats -->
        <div class="stats-row">
          <div class="stat-card">
            <div class="stat-icon"><span class="material-symbols-outlined">hub</span></div>
            <div class="stat-label">GLOBAL NETWORK</div>
            <div class="stat-value">124 Nodes</div>
          </div>
          <div class="stat-card">
            <div class="stat-icon"><span class="material-symbols-outlined">shield</span></div>
            <div class="stat-label">SECURE PROTOCOL</div>
            <div class="stat-value">AES-256</div>
          </div>
        </div>
      </div>
    </div>

    <!-- Right Panel (Form) -->
    <div class="form-panel">
      <!-- Mobile Header -->
      <div class="mobile-header">
        <div class="brand-logo">
          <svg fill="none" viewBox="0 0 48 48" xmlns="http://www.w3.org/2000/svg">
            <path clip-rule="evenodd" d="M24 18.4228L42 11.475V34.3663C42 34.7796 41.7457 35.1504 41.3601 35.2992L24 42V18.4228Z" fill="currentColor" fill-rule="evenodd"></path>
          </svg>
        </div>
        <span class="brand-name">IoT Nexus</span>
      </div>

      <div class="form-container">
        <div class="form-header">
          <h3>Get Started</h3>
          <p>Create your management account in minutes.</p>
        </div>

        <el-form
          ref="formRef"
          :model="form"
          :rules="rules"
          class="auth-form"
        >
          <!-- Phone -->
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
              />
            </div>
          </div>

          <!-- Username -->
          <div class="form-group">
            <label>Full Name</label>
            <div class="input-wrapper">
              <div class="input-icon">
                <span class="material-symbols-outlined">person</span>
              </div>
              <el-input
                v-model="form.username"
                placeholder="John Doe"
                class="custom-input"
              />
            </div>
          </div>

          <!-- Password -->
          <div class="form-group">
            <label>Password</label>
            <div class="input-wrapper">
              <div class="input-icon">
                <span class="material-symbols-outlined">lock</span>
              </div>
              <el-input
                v-model="form.password"
                type="password"
                placeholder="Enter password"
                class="custom-input"
                show-password
              />
            </div>
          </div>

          <!-- Confirm Password -->
          <div class="form-group">
            <label>Confirm Password</label>
            <div class="input-wrapper">
              <div class="input-icon">
                <span class="material-symbols-outlined">verified_user</span>
              </div>
              <el-input
                v-model="form.confirmPassword"
                type="password"
                placeholder="Confirm password"
                class="custom-input"
                show-password
                @keyup.enter="handleRegister"
              />
            </div>
          </div>

          <button
            type="button"
            class="submit-btn"
            :loading="loading"
            @click="handleRegister"
          >
            Register Now
          </button>
        </el-form>


        <!-- Login Link -->
        <div class="footer-link">
          <span>Already have an account?</span>
          <button @click="goToLogin">Login here</button>
        </div>
      </div>
      
    </div>
  </div>
</template>

<style>
@import '@/assets/auth-styles.css';

/* Component-specific overrides for Register page */
.auth-wrapper {
  display: flex;
  width: 100%;
  height: 100%;
  background-color: var(--bg-page);
  overflow: hidden;
}

/* Brand Panel */
.brand-panel {
  display: none;
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

/* Video Background */
.brand-video-bg {
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  object-fit: cover;
  z-index: 0;
}

.video-overlay {
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  background: linear-gradient(
    135deg,
    rgba(10, 20, 35, 0.85) 0%,
    rgba(20, 30, 50, 0.7) 50%,
    rgba(10, 20, 35, 0.85) 100%
  );
  z-index: 1;
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
  color: #ffffff;
}

/* Logo Styles for Register Page */
.logo {
  font-family: var(--font-display);
  font-size: 1.5rem;
  letter-spacing: -0.025em;
  color: #ffffff;
  text-shadow: 0 2px 10px rgba(0, 0, 0, 0.5);
}

.logo-sup {
  font-size: 0.75rem;
  vertical-align: super;
}

.brand-logo {
  background: white;
  padding: 4px;
  border-radius: 8px;
  box-shadow: 0 1px 3px rgba(0,0,0,0.1);
  display: flex;
  align-items: center;
  justify-content: center;
  width: 32px;
  height: 32px;
}

.brand-logo svg {
  width: 20px;
  height: 20px;
  color: var(--color-primary);
}

.brand-name {
  font-size: 1.5rem;
  font-weight: 700;
  letter-spacing: -0.025em;
  color: #ffffff;
}

.hero-text h2 {
  font-size: 3rem;
  line-height: 1.1;
  font-weight: 700;
  color: #ffffff;
  margin-bottom: 1rem;
  text-shadow: 0 2px 10px rgba(0, 0, 0, 0.5);
}

.hero-text h2 span {
  color: #64b5f6;
}

.hero-text p {
  font-size: 1.125rem;
  color: #e0e0e0;
  line-height: 1.6;
  text-shadow: 0 2px 8px rgba(0, 0, 0, 0.5);
}

.hero-image-placeholder {
  position: relative;
  width: 100%;
  height: 300px;
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
  background: rgba(255, 255, 255, 0.1);
  backdrop-filter: blur(12px);
  padding: 1.25rem;
  border-radius: 16px;
  border: 1px solid rgba(255, 255, 255, 0.2);
  box-shadow: 0 4px 20px rgba(0, 0, 0, 0.3);
}

.stat-icon {
  color: #64b5f6;
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
  color: #e0e0e0;
  margin-bottom: 0.25rem;
}

.stat-value {
  font-size: 2rem;
  font-weight: 700;
  color: #ffffff;
}

.stat-value span {
  font-size: 1.25rem;
  color: var(--color-primary);
}

/* Form Panel */
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
  margin-bottom: 0.25rem;
}

.form-header p {
  font-size: 0.875rem;
  color: var(--text-secondary);
  font-weight: 500;
}

.form-group {
  margin-bottom: 1.25rem;
}

.form-group label {
  display: block;
  font-size: 0.875rem;
  font-weight: 500;
  color: var(--text-label);
  margin-bottom: 0.25rem;
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
}

.custom-input {
  width: 100%;
  height: 3rem; /* py-2.5 approx 40px + padding */
  background-color: var(--bg-input);
  border: 1px solid var(--border-color);
  border-radius: var(--radius-md);
  color: var(--text-primary);
  font-size: 0.875rem;
  padding-left: 2.5rem !important;
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
  box-shadow: 0 0 0 2px var(--color-primary-light) !important;
  outline: none;
}

.submit-btn {
  width: 100%;
  padding-top: 0.75rem;
  padding-bottom: 0.75rem;
  background-color: var(--color-primary);
  color: white;
  font-size: 0.875rem;
  font-weight: 700;
  border: none;
  border-radius: var(--radius-md);
  cursor: pointer;
  box-shadow: 0 10px 15px -3px rgba(53, 158, 255, 0.2);
  transition: all 0.2s;
  margin-top: 1rem;
}

.submit-btn:hover {
  background-color: var(--color-primary-hover);
}


.footer-link {
  margin-top: 2rem;
  text-align: center;
  font-size: 0.875rem;
  color: var(--text-secondary);
}

.footer-link button {
  color: var(--color-primary);
  font-weight: 700;
  margin-left: 0.25rem;
  background: none;
  border: none;
  cursor: pointer;
}

</style>

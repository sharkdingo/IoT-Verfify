<script setup lang="ts">
import { computed, onMounted, onUnmounted, reactive, ref, watch } from 'vue'
import { useRoute, useRouter } from 'vue-router'
import { ElMessage } from 'element-plus'
import { useI18n } from 'vue-i18n'
import PublicHeader from '@/components/common/PublicHeader.vue'
import { authApi } from '@/api/auth'
import { useAuth } from '@/stores/auth'
import { localizedErrorMessage, localizedTextOrFallback } from '@/utils/userMessage'

type AuthMode = 'login' | 'register'

const router = useRouter()
const route = useRoute()
const { t, locale } = useI18n()
const { login } = useAuth()

const loading = ref(false)
const mouseX = ref(0)
const mouseY = ref(0)
const authMode = ref<AuthMode>(route.query.mode === 'register' ? 'register' : 'login')
const showAuthPanel = ref(Boolean(route.query.mode || route.query.redirect))

const loginForm = reactive({
  identifier: '',
  password: ''
})

const registerForm = reactive({
  phone: '',
  username: '',
  password: '',
  confirmPassword: ''
})

const formErrors = reactive<Record<string, string>>({})

const isRegisterMode = computed(() => authMode.value === 'register')
const panelTitle = computed(() => isRegisterMode.value ? t('auth.getStarted') : t('auth.welcomeBack'))
const panelSubtitle = computed(() => isRegisterMode.value ? t('auth.getStartedSubtitle') : t('auth.welcomeBackSubtitle'))
const redirectTarget = computed(() => {
  const redirect = route.query.redirect
  if (typeof redirect !== 'string') return '/board'
  return redirect.startsWith('/') && !redirect.startsWith('//') ? redirect : '/board'
})

watch(
  () => [route.query.mode, route.query.redirect],
  ([mode, redirect]) => {
    authMode.value = mode === 'register' ? 'register' : 'login'
    showAuthPanel.value = Boolean(mode || redirect)
    clearErrors()
  }
)

const clearErrors = () => {
  for (const key of Object.keys(formErrors)) {
    delete formErrors[key]
  }
}

const setAuthMode = (mode: AuthMode) => {
  showAuthPanel.value = true
  if (authMode.value === mode && route.query.mode === mode) return
  const query = { ...route.query, mode }
  authMode.value = mode
  clearErrors()
  router.replace({ path: '/', query })
}

const openAuthPanel = () => {
  setAuthMode('login')
}

const validatePhone = (phone: string, key: string) => {
  if (!phone.trim()) {
    formErrors[key] = t('auth.phoneRequired')
    return false
  }
  if (!/^1[3-9]\d{9}$/.test(phone.trim())) {
    formErrors[key] = t('auth.phoneInvalid')
    return false
  }
  return true
}

const validateLogin = () => {
  clearErrors()
  if (!loginForm.identifier.trim()) {
    formErrors.loginIdentifier = t('auth.accountRequired')
  }
  if (!loginForm.password) {
    formErrors.loginPassword = t('auth.passwordRequired')
  }
  return !formErrors.loginIdentifier && !formErrors.loginPassword
}

const validateRegister = () => {
  clearErrors()
  const validPhone = validatePhone(registerForm.phone, 'registerPhone')
  const username = registerForm.username.trim()

  if (!username) {
    formErrors.registerUsername = t('auth.usernameRequired')
  } else if (username.length < 3 || username.length > 20) {
    formErrors.registerUsername = t('auth.usernameLength')
  }

  if (!registerForm.password) {
    formErrors.registerPassword = t('auth.passwordRequired')
  } else if (registerForm.password.length < 6 || registerForm.password.length > 20) {
    formErrors.registerPassword = t('auth.passwordLength')
  }

  if (!registerForm.confirmPassword) {
    formErrors.confirmPassword = t('auth.confirmPasswordRequired')
  } else if (registerForm.confirmPassword !== registerForm.password) {
    formErrors.confirmPassword = t('auth.passwordMismatch')
  }

  return validPhone &&
    !formErrors.registerUsername &&
    !formErrors.registerPassword &&
    !formErrors.confirmPassword
}

const handleLogin = async () => {
  if (!validateLogin()) return

  loading.value = true
  try {
    const res = await authApi.login({
      identifier: loginForm.identifier.trim(),
      password: loginForm.password
    })

    if (res.code === 200) {
      if (!res.data) {
        throw new Error(t('auth.loginFailed'))
      }
      login(res.data.token, {
        userId: res.data.userId,
        phone: res.data.phone,
        username: res.data.username
      })
      ElMessage.success(t('auth.loginSuccess'))
      router.push(redirectTarget.value)
    } else {
      ElMessage.error(localizedTextOrFallback(res.message, t('auth.loginFailed'), locale.value))
    }
  } catch (error: any) {
    ElMessage.error(localizedErrorMessage(error, t('auth.loginFailed'), locale.value))
  } finally {
    loading.value = false
  }
}

const handleRegister = async () => {
  if (!validateRegister()) return

  loading.value = true
  try {
    const res = await authApi.register({
      phone: registerForm.phone.trim(),
      username: registerForm.username.trim(),
      password: registerForm.password
    })

    if (res.code === 200) {
      if (!res.data) {
        throw new Error(t('auth.registerFailed'))
      }
      ElMessage.success(t('auth.registerSuccess'))
      loginForm.identifier = registerForm.username.trim()
      loginForm.password = ''
      setAuthMode('login')
    } else {
      ElMessage.error(localizedTextOrFallback(res.message, t('auth.registerFailed'), locale.value))
    }
  } catch (error: any) {
    ElMessage.error(localizedErrorMessage(error, t('auth.registerFailed'), locale.value))
  } finally {
    loading.value = false
  }
}

const handleMouseMove = (e: MouseEvent) => {
  const x = (e.clientX / window.innerWidth - 0.5) * 2
  const y = (e.clientY / window.innerHeight - 0.5) * 2
  mouseX.value = x
  mouseY.value = y
}

onMounted(() => {
  window.addEventListener('mousemove', handleMouseMove)
})

onUnmounted(() => {
  window.removeEventListener('mousemove', handleMouseMove)
})
</script>

<template>
  <div
    class="landing-wrapper"
    :style="{
      '--mouse-x': mouseX,
      '--mouse-y': mouseY
    }"
  >
    <video
      class="video-bg"
      autoplay
      loop
      muted
      playsinline
      poster="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 1920 1080'%3E%3Crect fill='%230b1722' width='1920' height='1080'/%3E%3C/svg%3E"
    >
      <source src="https://cdn.pixabay.com/video/2025/05/06/277096_large.mp4" type="video/mp4">
    </video>

    <div class="video-overlay"></div>

    <PublicHeader
      variant="transparent"
      :show-theme="false"
    />

    <section
      class="hero-section"
      :class="{ 'hero-section--with-auth': showAuthPanel }"
      aria-labelledby="landing-title"
    >
      <h1 id="landing-title" class="hero-title animate-fade-rise">
        {{ t('app.landingHeroLead') }}
        <em class="emphasis">{{ t('app.landingHeroEmphasis') }}</em>
        {{ t('app.landingHeroTail') }}
      </h1>

      <p class="hero-subtext animate-fade-rise-delay">
        {{ t('app.landingHeroSubtext') }}
      </p>

      <button
        v-if="!showAuthPanel"
        class="hero-cta liquid-glass animate-fade-rise-delay-2"
        type="button"
        @click="openAuthPanel"
      >
        {{ t('app.getStarted') }}
      </button>

      <section
        v-show="showAuthPanel"
        class="auth-panel"
        :aria-labelledby="isRegisterMode ? 'register-title' : 'login-title'"
      >
        <div class="auth-tabs" role="tablist" :aria-label="t('auth.getStarted')">
          <button
            type="button"
            role="tab"
            :aria-selected="!isRegisterMode"
            :class="{ active: !isRegisterMode }"
            @click="setAuthMode('login')"
          >
            {{ t('auth.login') }}
          </button>
          <button
            type="button"
            role="tab"
            :aria-selected="isRegisterMode"
            :class="{ active: isRegisterMode }"
            @click="setAuthMode('register')"
          >
            {{ t('auth.register') }}
          </button>
        </div>

        <div class="auth-heading">
          <h2 :id="isRegisterMode ? 'register-title' : 'login-title'">{{ panelTitle }}</h2>
          <p>{{ panelSubtitle }}</p>
        </div>

        <form v-if="!isRegisterMode" class="auth-form" @submit.prevent="handleLogin">
          <label>
            <span>{{ t('auth.account') }}</span>
            <input
              v-model="loginForm.identifier"
              type="text"
              autocomplete="username"
              :placeholder="t('auth.accountPlaceholder')"
              :aria-invalid="Boolean(formErrors.loginIdentifier)"
            />
            <small :class="{ 'auth-form__hint--error': formErrors.loginIdentifier }">
              {{ formErrors.loginIdentifier || t('auth.accountHint') }}
            </small>
          </label>

          <label>
            <span>{{ t('auth.password') }}</span>
            <input
              v-model="loginForm.password"
              type="password"
              autocomplete="current-password"
              :placeholder="t('auth.passwordPlaceholder')"
              :aria-invalid="Boolean(formErrors.loginPassword)"
            />
            <small :class="{ 'auth-form__hint--error': formErrors.loginPassword }">
              {{ formErrors.loginPassword || t('auth.loginPasswordHint') }}
            </small>
          </label>

          <button class="auth-submit" type="submit" :disabled="loading">
            {{ loading ? t('app.loading') : t('auth.signInToConsole') }}
          </button>
        </form>

        <form v-else class="auth-form" @submit.prevent="handleRegister">
          <label>
            <span>{{ t('auth.phoneNumber') }}</span>
            <input
              v-model="registerForm.phone"
              type="tel"
              inputmode="numeric"
              autocomplete="tel"
              :placeholder="t('auth.phonePlaceholder')"
              :aria-invalid="Boolean(formErrors.registerPhone)"
            />
            <small :class="{ 'auth-form__hint--error': formErrors.registerPhone }">
              {{ formErrors.registerPhone || t('auth.phoneHint') }}
            </small>
          </label>

          <label>
            <span>{{ t('auth.username') }}</span>
            <input
              v-model="registerForm.username"
              type="text"
              autocomplete="username"
              :placeholder="t('auth.usernamePlaceholder')"
              :aria-invalid="Boolean(formErrors.registerUsername)"
            />
            <small :class="{ 'auth-form__hint--error': formErrors.registerUsername }">
              {{ formErrors.registerUsername || t('auth.usernameHint') }}
            </small>
          </label>

          <label>
            <span>{{ t('auth.password') }}</span>
            <input
              v-model="registerForm.password"
              type="password"
              autocomplete="new-password"
              :placeholder="t('auth.passwordPlaceholder')"
              :aria-invalid="Boolean(formErrors.registerPassword)"
            />
            <small :class="{ 'auth-form__hint--error': formErrors.registerPassword }">
              {{ formErrors.registerPassword || t('auth.passwordHint') }}
            </small>
          </label>

          <label>
            <span>{{ t('auth.confirmPassword') }}</span>
            <input
              v-model="registerForm.confirmPassword"
              type="password"
              autocomplete="new-password"
              :placeholder="t('auth.confirmPasswordPlaceholder')"
              :aria-invalid="Boolean(formErrors.confirmPassword)"
            />
            <small :class="{ 'auth-form__hint--error': formErrors.confirmPassword }">
              {{ formErrors.confirmPassword || t('auth.confirmPasswordHint') }}
            </small>
          </label>

          <button class="auth-submit" type="submit" :disabled="loading">
            {{ loading ? t('app.loading') : t('auth.registerNow') }}
          </button>
        </form>
      </section>
    </section>
  </div>
</template>

<style scoped>
@import url('https://fonts.googleapis.com/css2?family=Instrument+Serif:ital@0;1&family=Inter:wght@400;500;700;800&display=swap');

.landing-wrapper {
  position: relative;
  width: 100%;
  min-height: 100vh;
  overflow-x: hidden;
  overflow-y: auto;
  background-color: hsl(201, 100%, 13%);
  font-family: 'Inter', sans-serif;
  color: hsl(0, 0%, 100%);
}

.video-bg {
  position: fixed;
  top: calc(var(--mouse-y) * 10px);
  left: calc(var(--mouse-x) * 10px);
  width: calc(100% + 20px);
  height: calc(100% + 20px);
  object-fit: cover;
  z-index: 0;
  transition: transform 0.1s ease-out;
}

.video-overlay {
  position: fixed;
  inset: 0;
  background: linear-gradient(
    135deg,
    rgba(10, 20, 35, 0.7) 0%,
    rgba(20, 30, 50, 0.5) 50%,
    rgba(10, 20, 35, 0.7) 100%
  );
  z-index: 1;
}

.liquid-glass {
  position: relative;
  overflow: hidden;
  border: none;
  border-radius: 9999px;
  background: rgba(255, 255, 255, 0.01);
  background-blend-mode: luminosity;
  backdrop-filter: blur(4px);
  -webkit-backdrop-filter: blur(4px);
  box-shadow: inset 0 1px 1px rgba(255, 255, 255, 0.1);
  color: hsl(0, 0%, 100%);
  cursor: pointer;
  transition: transform 0.2s;
}

.liquid-glass:hover {
  transform: scale(1.03);
}

.liquid-glass::before,
.auth-panel::before {
  content: '';
  position: absolute;
  inset: 0;
  border-radius: inherit;
  padding: 1.4px;
  background: linear-gradient(180deg, rgba(255,255,255,0.45) 0%, rgba(255,255,255,0.15) 20%, rgba(255,255,255,0) 40%, rgba(255,255,255,0) 60%, rgba(255,255,255,0.15) 80%, rgba(255,255,255,0.45) 100%);
  -webkit-mask: linear-gradient(#fff 0 0) content-box, linear-gradient(#fff 0 0);
  -webkit-mask-composite: xor;
  mask-composite: exclude;
  pointer-events: none;
}

.hero-section {
  position: relative;
  z-index: 10;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  min-height: 100vh;
  padding: 8rem 1.5rem 4.5rem;
  text-align: center;
}

.hero-section--with-auth {
  align-items: flex-start;
  padding-right: min(36rem, 38vw);
  padding-left: clamp(2rem, 7vw, 7rem);
  text-align: left;
}

.hero-section--with-auth .hero-title,
.hero-section--with-auth .hero-subtext {
  max-width: 46rem;
}

.hero-title {
  max-width: 56rem;
  margin: 0;
  font-family: 'Instrument Serif', serif;
  font-size: 3rem;
  font-weight: 400;
  line-height: 0.95;
  letter-spacing: 0;
  color: hsl(0, 0%, 100%);
  text-shadow: 0 4px 20px rgba(0, 0, 0, 0.6);
}

.emphasis {
  color: hsl(210, 100%, 70%);
  font-style: normal;
  text-shadow: 0 0 30px rgba(100, 200, 255, 0.4);
}

.hero-subtext {
  max-width: 42rem;
  margin-top: 2rem;
  font-size: 1rem;
  line-height: 1.625;
  color: hsl(0, 0%, 85%);
  text-shadow: 0 2px 10px rgba(0, 0, 0, 0.5);
}

.hero-cta {
  margin-top: 3rem;
  padding: 1.25rem 3.5rem;
  font-size: 1rem;
}

.auth-panel {
  position: relative;
  width: min(100%, 430px);
  margin-top: 2.25rem;
  border-radius: 18px;
  background: rgba(8, 16, 24, 0.58);
  background-blend-mode: luminosity;
  backdrop-filter: blur(18px);
  -webkit-backdrop-filter: blur(18px);
  box-shadow: inset 0 1px 1px rgba(255, 255, 255, 0.12), 0 24px 80px rgba(0, 0, 0, 0.34);
  padding: 1rem;
  text-align: left;
}

@media (min-width: 1101px) {
  .auth-panel {
    position: absolute;
    top: 50%;
    right: clamp(1.5rem, 5.5vw, 6rem);
    width: min(31vw, 420px);
    min-width: 360px;
    margin-top: 0;
    transform: translateY(-50%);
    animation: auth-panel-rise 0.45s ease-out both;
  }
}

.auth-tabs {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 6px;
  border-radius: 9999px;
  background: rgba(255, 255, 255, 0.08);
  padding: 4px;
}

.auth-tabs button {
  min-height: 38px;
  border: 0;
  border-radius: 9999px;
  background: transparent;
  color: rgba(255, 255, 255, 0.72);
  cursor: pointer;
  font-weight: 800;
}

.auth-tabs button.active {
  background: rgba(255, 255, 255, 0.9);
  color: hsl(0, 0%, 4%);
}

.auth-heading {
  margin: 1rem 0;
  text-align: center;
}

.auth-heading h2 {
  margin: 0;
  font-size: 1.25rem;
  letter-spacing: 0;
}

.auth-heading p {
  margin: 0.35rem 0 0;
  color: rgba(255, 255, 255, 0.72);
  font-size: 0.86rem;
  line-height: 1.5;
}

.auth-form {
  display: grid;
  gap: 0.78rem;
}

.auth-form label {
  display: grid;
  gap: 0.35rem;
}

.auth-form label span {
  font-size: 0.76rem;
  font-weight: 800;
  color: rgba(255, 255, 255, 0.78);
}

.auth-form input {
  width: 100%;
  min-height: 40px;
  border: 1px solid rgba(255, 255, 255, 0.18);
  border-radius: 10px;
  background: rgba(255, 255, 255, 0.10);
  color: #ffffff;
  padding: 0 0.75rem;
  outline: none;
}

.auth-form input::placeholder {
  color: rgba(255, 255, 255, 0.42);
}

.auth-form input:focus {
  border-color: rgba(125, 211, 252, 0.9);
  box-shadow: 0 0 0 3px rgba(125, 211, 252, 0.18);
}

.auth-form input[aria-invalid="true"] {
  border-color: #fca5a5;
}

.auth-form small {
  color: rgba(255, 255, 255, 0.58);
  font-size: 0.74rem;
  line-height: 1.35;
}

.auth-form__hint--error {
  color: #fecaca !important;
}

.auth-submit {
  min-height: 42px;
  margin-top: 0.1rem;
  border: 0;
  border-radius: 9999px;
  background: rgba(255, 255, 255, 0.9);
  color: hsl(0, 0%, 4%);
  cursor: pointer;
  font-weight: 900;
}

.auth-submit:disabled {
  cursor: wait;
  opacity: 0.72;
}

.auth-submit:not(:disabled):hover {
  background: #ffffff;
}

@keyframes fade-rise {
  from {
    opacity: 0;
    transform: translateY(24px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

@keyframes auth-panel-rise {
  from {
    opacity: 0;
    transform: translateY(-46%);
  }
  to {
    opacity: 1;
    transform: translateY(-50%);
  }
}

.animate-fade-rise {
  animation: fade-rise 0.8s ease-out both;
}

.animate-fade-rise-delay {
  animation: fade-rise 0.8s ease-out 0.2s both;
}

.animate-fade-rise-delay-2 {
  animation: fade-rise 0.8s ease-out 0.4s both;
}

@media (min-width: 640px) {
  .hero-title {
    font-size: 4.5rem;
  }

  .hero-subtext {
    font-size: 1.125rem;
  }
}

@media (min-width: 768px) {
  .hero-title {
    font-size: 5rem;
  }
}

@media (max-width: 767px) {
  .hero-section {
    padding-top: 7rem;
    padding-bottom: 3rem;
    justify-content: flex-start;
  }

  .hero-title {
    font-size: 2.5rem;
  }

  .hero-subtext {
    margin-top: 1.25rem;
  }

  .hero-cta {
    margin-top: 2rem;
    padding: 1rem 2rem;
  }

  .auth-panel {
    margin-top: 1.5rem;
    padding: 0.85rem;
  }
}

@media (max-width: 1100px) {
  .hero-section--with-auth {
    align-items: center;
    padding-right: 1.5rem;
    padding-left: 1.5rem;
    text-align: center;
  }

  .auth-panel {
    width: min(100%, 430px);
    min-width: 0;
    animation: fade-rise 0.5s ease-out both;
  }
}
</style>

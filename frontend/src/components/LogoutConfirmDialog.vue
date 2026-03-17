<script setup lang="ts">
import { ref } from 'vue'

const props = defineProps<{
  visible: boolean
}>()

const emit = defineEmits<{
  'update:visible': [value: boolean]
  'confirm': []
  'cancel': []
}>()

const loading = ref(false)

const handleConfirm = async () => {
  loading.value = true
  emit('confirm')
  loading.value = false
}

const handleCancel = () => {
  emit('cancel')
  emit('update:visible', false)
}
</script>

<template>
  <Teleport to="body">
    <Transition name="logout-dialog">
      <div v-if="visible" class="logout-overlay" @click.self="handleCancel">
        <div class="logout-dialog">
          <!-- Icon -->
          <div class="logout-icon-wrapper">
            <div class="logout-icon-bg"></div>
            <span class="material-symbols-outlined logout-icon">logout</span>
          </div>

          <!-- Content -->
          <div class="logout-content">
            <h2 class="logout-title">Log Out</h2>
            <p class="logout-message">Are you sure you want to log out? You'll need to sign in again to access your account.</p>
          </div>

          <!-- Actions -->
          <div class="logout-actions">
            <button class="logout-btn logout-btn-cancel" @click="handleCancel" :disabled="loading">
              Cancel
            </button>
            <button class="logout-btn logout-btn-confirm" @click="handleConfirm" :disabled="loading">
              <span v-if="loading" class="loading-spinner"></span>
              <span v-else>Log Out</span>
            </button>
          </div>
        </div>
      </div>
    </Transition>
  </Teleport>
</template>

<style scoped>
.logout-overlay {
  position: fixed;
  inset: 0;
  z-index: 9999;
  display: flex;
  align-items: center;
  justify-content: center;
  background: rgba(0, 0, 0, 0.6);
  backdrop-filter: blur(4px);
}

.logout-dialog {
  width: 100%;
  max-width: 380px;
  padding: 2rem;
  background: linear-gradient(145deg, #1e293b, #0f172a);
  border-radius: 20px;
  border: 1px solid rgba(148, 163, 184, 0.15);
  box-shadow: 
    0 25px 50px -12px rgba(0, 0, 0, 0.5),
    0 0 0 1px rgba(255, 255, 255, 0.05);
  text-align: center;
  transform: scale(1);
}

.logout-icon-wrapper {
  position: relative;
  width: 72px;
  height: 72px;
  margin: 0 auto 1.5rem;
}

.logout-icon-bg {
  position: absolute;
  inset: 0;
  background: linear-gradient(135deg, #ef4444, #dc2626);
  border-radius: 50%;
  animation: pulse-bg 2s ease-in-out infinite;
}

@keyframes pulse-bg {
  0%, 100% {
    transform: scale(1);
    opacity: 1;
  }
  50% {
    transform: scale(1.05);
    opacity: 0.8;
  }
}

.logout-icon {
  position: absolute;
  top: 50%;
  left: 50%;
  transform: translate(-50%, -50%);
  font-size: 32px;
  color: white;
}

.logout-content {
  margin-bottom: 2rem;
}

.logout-title {
  font-size: 1.5rem;
  font-weight: 600;
  color: #f8fafc;
  margin-bottom: 0.75rem;
  letter-spacing: -0.025em;
}

.logout-message {
  font-size: 0.9375rem;
  color: rgba(148, 163, 184, 0.85);
  line-height: 1.6;
}

.logout-actions {
  display: flex;
  gap: 1rem;
}

.logout-btn {
  flex: 1;
  padding: 0.875rem 1.5rem;
  font-size: 0.9375rem;
  font-weight: 600;
  border-radius: 12px;
  cursor: pointer;
  transition: all 0.2s ease;
  border: none;
}

.logout-btn-cancel {
  background: rgba(148, 163, 184, 0.1);
  color: #94a3b8;
  border: 1px solid rgba(148, 163, 184, 0.2);
}

.logout-btn-cancel:hover:not(:disabled) {
  background: rgba(148, 163, 184, 0.15);
  color: #cbd5e1;
}

.logout-btn-confirm {
  background: linear-gradient(135deg, #ef4444, #dc2626);
  color: white;
  box-shadow: 0 4px 12px rgba(239, 68, 68, 0.3);
}

.logout-btn-confirm:hover:not(:disabled) {
  background: linear-gradient(135deg, #f87171, #ef4444);
  transform: translateY(-1px);
  box-shadow: 0 6px 16px rgba(239, 68, 68, 0.4);
}

.logout-btn:disabled {
  opacity: 0.6;
  cursor: not-allowed;
}

.loading-spinner {
  display: inline-block;
  width: 18px;
  height: 18px;
  border: 2px solid rgba(255, 255, 255, 0.3);
  border-top-color: white;
  border-radius: 50%;
  animation: spin 0.8s linear infinite;
}

@keyframes spin {
  to {
    transform: rotate(360deg);
  }
}

/* Transition */
.logout-dialog-enter-active,
.logout-dialog-leave-active {
  transition: all 0.3s ease;
}

.logout-dialog-enter-from,
.logout-dialog-leave-to {
  opacity: 0;
}

.logout-dialog-enter-from .logout-dialog,
.logout-dialog-leave-to .logout-dialog {
  transform: scale(0.9);
}
</style>

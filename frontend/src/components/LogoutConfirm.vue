<script setup lang="ts">
import { defineEmits, defineProps } from 'vue';

const props = defineProps<{
  visible: boolean;
}>();

const emit = defineEmits<{
  (e: 'update:visible', value: boolean): void;
  (e: 'confirm'): void;
}>();

const close = () => {
  emit('update:visible', false);
};

const confirm = () => {
  emit('confirm');
  close();
};
</script>

<template>
  <teleport to="body">
    <transition name="modal-fade">
      <div v-if="props.visible" class="fixed inset-0 z-50 flex items-center justify-center p-4 bg-black/50 backdrop-blur-sm" @click.self="close">
        <div class="bg-white w-full max-w-md rounded-2xl shadow-2xl overflow-hidden transform transition-all">
          
          <!-- Header -->
          <div class="px-8 py-6 border-b border-slate-100 flex items-center justify-center relative">
            <div class="absolute right-4 top-4">
              <button @click="close" class="text-slate-400 hover:text-slate-600 p-1 rounded-full hover:bg-slate-50 transition-colors">
                <span class="material-symbols-outlined text-xl">close</span>
              </button>
            </div>
            <div class="text-center">
              <div class="w-16 h-16 bg-red-50 rounded-full flex items-center justify-center mx-auto mb-4">
                <span class="material-symbols-outlined text-4xl text-red-500">logout</span>
              </div>
              <h3 class="text-xl font-bold text-slate-800">Log Out</h3>
            </div>
          </div>

          <!-- Body -->
          <div class="px-8 py-6 text-center">
            <p class="text-slate-600 leading-relaxed">
              Are you sure you want to log out? 
            </p>
          </div>

          <!-- Footer -->
          <div class="px-8 py-4 bg-slate-50 flex justify-end items-center gap-3">
            <button 
              @click="close"
              class="px-5 py-2.5 text-sm font-semibold text-slate-700 bg-white border border-slate-200 hover:bg-slate-50 rounded-xl transition-all shadow-sm hover:shadow"
            >
              Cancel
            </button>
            <button 
              @click="confirm"
              class="px-5 py-2.5 text-sm font-semibold text-white bg-red-500 hover:bg-red-600 rounded-xl transition-all shadow-lg hover:shadow-red-500/30 flex items-center gap-2"
            >
              <span class="material-symbols-outlined text-lg">logout</span>
              Log Out
            </button>
          </div>
        </div>
      </div>
    </transition>
  </teleport>
</template>

<style scoped>
.modal-fade-enter-active,
.modal-fade-leave-active {
  transition: opacity 0.3s ease;
}

.modal-fade-enter-from,
.modal-fade-leave-to {
  opacity: 0;
}
</style>



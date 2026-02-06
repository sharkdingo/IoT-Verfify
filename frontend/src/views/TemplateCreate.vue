<template>
  <div class="min-h-[calc(100vh)] flex flex-col items-center justify-start">
    <!-- Back Button -->
    <div class="w-full max-w-4xl mt-6 mb-6 flex justify-start z-10 relative px-4 sm:px-0">
      <button
        @click="goBack"
        class="group flex items-center gap-2 text-slate-500 hover:text-slate-800 dark:text-slate-400 dark:hover:text-white transition-colors bg-white/80 dark:bg-slate-800/80 backdrop-blur-sm px-3 py-1.5 rounded-full shadow-sm hover:shadow border border-slate-200 dark:border-slate-700"
      >
        <span class="material-symbols-outlined bg-white dark:bg-slate-700 rounded-full p-0.5 shadow-sm group-hover:shadow transition-shadow text-sm">arrow_back</span>
        <span class="text-sm font-medium">Back to Board</span>
      </button>
    </div>

    <!-- Main Content Card -->
    <div class="w-full max-w-4xl bg-white dark:bg-slate-800 rounded-2xl shadow-xl overflow-hidden border border-slate-100 dark:border-slate-700 mb-12 mx-4">
      <!-- Header Section -->
      <div class="bg-gradient-to-r from-orange-500 to-orange-600 px-1 py-2 text-white shrink-0">
        <div class="flex items-center gap-3 mb-2">
          <div class="bg-white/20 p-2 rounded-lg backdrop-blur-sm">
            <span class="material-symbols-outlined text-2xl text-white">construction</span>
          </div>
          <div>
            <h1 class="text-2xl font-bold text-black">Create New Template</h1>
            <p class="text-orange-100 text-sm mt-1">Design a powerful template for your IoT devices</p>
          </div>
        </div>
      </div>

      <!-- Content Section -->
      <div class="p-1 sm:p-1">
        <CustomTemplateCreator @refresh-templates="onRefresh" />
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { useRouter } from 'vue-router'
import CustomTemplateCreator from '@/components/CustomTemplateCreator.vue'

const router = useRouter()

const goBack = () => {
  router.push('/')
}

const onRefresh = () => {
  console.log('Template created/refreshed')
}
</script>

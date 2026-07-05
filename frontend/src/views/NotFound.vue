<script setup lang="ts">
import { useI18n } from 'vue-i18n'

const { t } = useI18n()
</script>


<template>
  <el-main class="main-frame">
    <el-result
        icon="error"
        :title="t('app.notFound.title')"
        :sub-title="t('app.notFound.subtitle')"
    >
      <template #extra>
        <router-link to="/home">
          <el-button type="primary">{{ t('app.notFound.home') }}</el-button>
        </router-link>
      </template>
    </el-result>
  </el-main>
</template>


<style scoped>
.main-frame {
  width: 100%;
  height: 100%;

  display: flex;
  align-items: center;
  justify-content: center;
}
</style>

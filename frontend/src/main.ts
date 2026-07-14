import { createApp } from 'vue'
import 'element-plus/theme-chalk/el-message-box.css'
import './style.css'
import './styles/base.css'
import './styles/tailwind.css'
import './styles/board.css'
import './assets/auth-styles.css'
import App from './App.vue'
import {router} from './router';
import { i18n } from './assets/i18n.ts'
import { initializeTheme } from '@/composables/useTheme';

initializeTheme();
createApp(App).use(router).use(i18n).mount('#app');

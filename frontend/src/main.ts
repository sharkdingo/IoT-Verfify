import { createApp } from 'vue'
import './style.css'
import './styles/base.css'
import './styles/board.css'
import App from './App.vue'
import {router} from './router';
import ElementPlus from 'element-plus';
import { i18n } from './assets/i18n.ts'

createApp(App).use(ElementPlus).use(router).use(i18n).mount('#app');

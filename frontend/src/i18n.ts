// src/i18n.ts
import { createI18n } from 'vue-i18n'

/**
 * 所有文案统一放在 messages 里
 * 后续有新页面就继续往 app / xxx 下加 key 即可
 */
const messages = {
    'zh-CN': {
        app: {
            /* 通用 */
            title: 'IoT-Verify',
            warning: '警告',
            delete: '删除',
            cancel: '取消',
            save: '保存',

            /* Board 页标题 */
            input: '输入',
            status: '状态',

            /* 左侧：设备列表 & 规则 */
            devices: '设备列表',
            searchDevice: '搜索设备',
            rules: 'IFTTT 规则',
            sourceDevice: '源设备',
            sourceApi: '源 API',
            targetDevice: '目标设备',
            targetApi: '目标 API',
            addRule: '添加规则',

            /* 左侧：规约 */
            specifications: '规约',
            specTemplate: '规约模板',
            selectTemplate: '选择模板',
            naturalLanguage: '自然语言描述',
            specPlaceholder: '请输入规约的自然语言描述，例如：空调开启后最终必须关闭。',
            addSpec: '添加规约',
            specTemplateShort: '模板',
            specText: '规约',
            noSpecYet: '暂无规约，请先添加。',
            fillAllSpecFields: '请选择模板并填写规约描述',
            addACondition: '添加条件',
            addIfCondition: '添加 IF 条件',
            addThenCondition: '添加 THEN 条件',
            value: '值',
            thenHappens: '',
            currentSpecs: '当前规约',
            selectAttrOrApi: '选择属性或 API',

            /* 右侧：状态面板 */
            currentDevices: '当前设备',
            currentRules: '当前规则',
            device: '设备',
            state: '状态',
            actions: '操作',

            /* 校验 & 弹窗提示 */
            nameExists: '该名称已存在，请换一个',
            fillAllRuleFields: '请完整选择源/目标设备及 API',
            deleteNodeWithEdgesConfirm:
                '该设备存在与其他设备的规则（连线），删除设备将同时删除这些规则，是否继续？',

            /* 右键弹窗 */
            deviceInfo: '设备信息',
            description: '描述',
            name: '名称',
            deleteDevice: '删除设备'
        }
    },

    en: {
        app: {
            /* common */
            title: 'IoT-Verify',
            warning: 'Warning',
            delete: 'Delete',
            cancel: 'Cancel',
            save: 'Save',

            /* Board titles */
            input: 'Inputs',
            status: 'Status',

            /* left panel: devices & rules */
            devices: 'Devices',
            searchDevice: 'Search devices',
            rules: 'IFTTT Rules',
            sourceDevice: 'Source Device',
            sourceApi: 'Source API',
            targetDevice: 'Target Device',
            targetApi: 'Target API',
            addRule: 'Add Rule',

            /* left panel: specifications */
            specifications: 'Specifications',
            specTemplate: 'Specification Template',
            selectTemplate: 'Select Template',
            naturalLanguage: 'Natural Language',
            specPlaceholder:
                'Please enter the natural-language description of the specification, e.g., "After the AC is turned on, it must eventually be turned off."',
            addSpec: 'Add Specification',
            specTemplateShort: 'Template',
            specText: 'Specification',
            noSpecYet: 'No specification yet. Please add one.',
            fillAllSpecFields: 'Please select a template and enter the specification description',
            addACondition: 'Add Condition',
            addIfCondition: 'Add IF Condition',
            addThenCondition: 'Add THEN Condition',
            value: 'Value',
            thenHappens: '',
            currentSpecs: 'Current Specifications',
            selectAttrOrApi: 'Select attribute or API',

            /* right panel */
            currentDevices: 'Current Devices',
            currentRules: 'Current Rules',
            device: 'Device',
            state: 'State',
            actions: 'Actions',

            /* validations / messages */
            nameExists: 'Name already exists, please choose another one',
            fillAllRuleFields: 'Please select source/target device and API completely',
            deleteNodeWithEdgesConfirm:
                'This device has rules (edges) with other devices. Deleting it will also delete those rules. Continue?',

            /* dialog */
            deviceInfo: 'Device Info',
            description: 'Description',
            name: 'Name',
            deleteDevice: 'Delete Device'
        }
    }
}

/**
 * 创建 i18n 实例
 * - legacy: false 使用 Composition API 模式（useI18n）
 * - locale 从 localStorage 读取，默认中文
 */
export const i18n = createI18n({
    legacy: false,
    locale: localStorage.getItem('locale') || 'zh-CN',
    fallbackLocale: 'en',
    messages
})

export default i18n

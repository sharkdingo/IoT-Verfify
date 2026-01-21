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
            select: '请选择',
            null: '空',
            type: '类型',

            /* Board 页标题 */
            input: '输入',
            status: '状态',
            restoreInput: '点击恢复输入面板',
            restoreStatus: '点击恢复状态面板',

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
            addSpec: '添加规约',
            specTemplateShort: '模板',
            specText: '规约',
            noSpecYet: '暂无规约，请先添加。',
            fillAllSpecFields: '请选择模板并填写规约描述',
            addACondition: '添加条件',
            addIfCondition: '添加 IF 条件',
            addThenCondition: '添加 THEN 条件',
            value: '值',
            specRowIncomplete: '存在未填完整的条件，请删除该行或补全所有字段。',
            selectAttrOrApi: '选择属性或 API',
            specNeedA: '请至少配置一个事件 A 条件',
            specNeedIf: '请先完成 IF 部分（事件 A 的条件）',
            specNeedThen: '请先完成 THEN 部分（事件 B 的条件）',
            specDuplicate: '已经存在一条内容完全相同的规约',

            /* 右侧：状态面板 */
            currentDevices: '当前设备',
            currentRules: '当前规则',
            currentSpecs: '当前规约',
            specContent: '规约内容',
            device: '设备',
            state: '状态',
            actions: '操作',

            /* 校验 & 弹窗提示 */
            nameExists: '该名称已存在，请换一个',
            fillAllRuleFields: '请完整选择源/目标设备及 API',
            deleteNodeWithRelationsConfirm: '该设备存在与其他设备的规则（连线）或已参与规约，删除设备将同时删除这些规则和相关规约，是否继续？',
            specsDeletedWithNode: '已同时删除与该设备相关的规约。',
            saveLayoutFailed: '保存画布布局失败',
            saveNodesFailed: '保存设备节点失败',
            saveEdgesFailed: '保存规则连线失败',
            saveSpecsFailed: '保存规约失败',
            saveActiveFailed: '保存折叠面板状态失败',
            loadTemplatesFailed: '加载设备模板失败',
            addTemplateSuccess: '添加设备模板成功',
            addTemplateFailed: '添加设备模板失败',

            /* 右键弹窗 */
            name: '名称',
            description: '描述',
            deleteDevice: '删除设备',

            deviceInfo: '设备信息',
            deviceBasic: '基本信息',
            deviceVariables: '变量',
            deviceStates: '状态',
            deviceApis: 'APIs',

            instanceName: '实例名称',
            initState: '初始状态',
            impactedVariables: '受影响变量',
            modes: '模式',
            invariant: '不变量',
            range: '范围',
            trust: '可信度',
            privacy: '隐私度',
            from: '起始状态',
            to: '结束状态',
            signal: '信号',
            transition: '转变',

            relatedRules: '相关 IFTTT 规则',
            relatedSpecs: '相关规约',
            renameDevice: '重命名设备',

            // AddTemplateDialog
            jsonParseError: 'JSON 格式错误，无法切换回表单',
            inputVarName: "变量名称是必需的",
            inputDeviceName: "设备名称是必需的",
            addDeviceTemplate: "添加设备模板",
            basicMode: "引导模式",
            jsonMode: "JSON 模式",
            basicInfo: "基本信息",
            deviceName: "设备名称",
            variables: "变量",
            internalVariables: "内部变量",
            add: "添加",
            noInternalVars: "未定义内部变量",
            workingStates: "工作状态",
            addState: "添加状态",
            addApi: "添加 API",
            editInternalVar: "编辑内部变量",
            varName: "变量名称",
            isInside: "是否在内部",
            publicVisible: "公开可见"
        },

        auth: {
            welcomeBack: '欢迎回来',
            phoneRequired: '请输入手机号',
            phoneInvalid: '手机号格式不正确',
            phonePlaceholder: '请输入手机号',
            passwordRequired: '请输入密码',
            passwordPlaceholder: '请输入密码',
            usernameRequired: '请输入用户名',
            usernamePlaceholder: '请输入用户名（3-20字符）',
            usernameLength: '用户名需为3-20个字符',
            passwordLength: '密码需为6-20个字符',
            confirmPasswordRequired: '请确认密码',
            confirmPasswordPlaceholder: '请再次输入密码',
            passwordMismatch: '两次输入的密码不一致',
            login: '登 录',
            register: '注 册',
            loginSuccess: '登录成功',
            loginFailed: '登录失败，请检查手机号和密码',
            registerSuccess: '注册成功，请登录',
            registerFailed: '注册失败',
            noAccount: '还没有账号？',
            registerNow: '立即注册',
            haveAccount: '已有账号？',
            loginNow: '立即登录'
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
            select: 'Please select',
            null: 'Null',
            type: 'Type',

            /* Board titles */
            input: 'Input',
            status: 'Status',
            restoreInput: 'Restore Input Panel',
            restoreStatus: 'Restore Status Panel',

            /* left panel: devices & rules */
            devices: 'Devices',
            searchDevice: 'Search devices',
            rules: 'IFTTT Rules',
            sourceDevice: 'Source Device',
            sourceApi: 'Source API',
            targetDevice: 'Target Device',
            targetApi: 'Target API',
            addRule: 'Add Rule',
            specNeedA: 'Please configure at least one condition for event A.',
            specNeedIf: 'Please complete the IF part (conditions for event A).',
            specNeedThen: 'Please complete the THEN part (conditions for event B).',

            /* left panel: specifications */
            specifications: 'Specifications',
            specTemplate: 'Specification Template',
            selectTemplate: 'Select Template',
            naturalLanguage: 'Natural Language',
            addSpec: 'Add Specification',
            specTemplateShort: 'Template',
            specContent: 'Specification',
            noSpecYet: 'No specification yet. Please add one.',
            fillAllSpecFields: 'Please select a template and enter the specification description',
            addACondition: 'Add Condition',
            addIfCondition: 'Add IF Condition',
            addThenCondition: 'Add THEN Condition',
            value: 'Value',
            currentSpecs: 'Current Specifications',
            selectAttrOrApi: 'Select attribute or API',
            specRowIncomplete: 'There is an incomplete condition row. Please either delete it or fill in all fields.',
            specDuplicate: 'An identical specification already exists',

            /* right panel */
            currentDevices: 'Current Devices',
            currentRules: 'Current Rules',
            device: 'Device',
            state: 'State',
            actions: 'Actions',

            /* validations / messages */
            nameExists: 'Name already exists, please choose another one',
            fillAllRuleFields: 'Please select source/target device and API completely',
            deleteNodeWithRelationsConfirm: 'This device has rules (edges) or is involved in specifications. Deleting it will also remove those rules and related specifications. Continue?',
            specsDeletedWithNode: 'Specifications related to this device have been removed as well.',
            saveLayoutFailed: 'Failed to retrieve layout',
            saveNodesFailed: 'Failed to retrieve nodes',
            saveEdgesFailed: 'Failed to retrieve edges',
            saveSpecsFailed: 'Failed to retrieve specs',
            saveActiveFailed: 'Failed to retrieve panel active status',
            loadTemplatesFailed: 'Failed to retrieve device templates',
            addTemplateSuccess: 'Successfully added a device template',
            addTemplateFailed: 'Failed to retrieve device template',

            /* dialog */
            name: 'Name',
            description: 'Description',
            deleteDevice: 'Delete Device',

            deviceInfo: 'Device Info',
            deviceBasic: 'Basic',
            deviceVariables: 'Variables',
            deviceStates: 'States',
            deviceApis: 'APIs',

            instanceName: 'Instance',
            initState: 'Initial State',
            impactedVariables: 'Impacted Variables',
            modes: 'Modes',
            invariant: 'Invariant',
            range: 'Range / Enum',
            trust: 'Trust',
            privacy: 'Privacy',
            from: 'From',
            to: 'To',
            signal: 'Signal',
            transition: 'Transition',

            relatedRules: 'Related IFTTT Rules',
            relatedSpecs: 'Related Specifications',
            renameDevice: 'Rename Device',

            // AddTemplateDialog
            jsonParseError: 'JSON Syntax Error',
            inputVarName: 'Variable Name is required',
            inputDeviceName: 'Device Name is required',
            addDeviceTemplate: 'Add Device Template',
            basicMode: 'Guided Mode',
            jsonMode: 'JSON Mode',
            basicInfo: 'Basic Info',
            deviceName: 'Device Name',
            variables: 'Variables',
            internalVariables: 'Internal Variables',
            add: 'Add',
            noInternalVars: 'No internal variables defined',
            workingStates: 'Working States',
            addState: 'Add State',
            addApi: 'Add API',
            editInternalVar: 'Edit Internal Variable',
            varName: 'Variable Name',
            isInside: 'Is Inside',
            publicVisible: 'Public Visible',

            auth: {
                welcomeBack: 'Welcome Back',
                phoneRequired: 'Please enter your phone number',
                phoneInvalid: 'Invalid phone number format',
                phonePlaceholder: 'Enter phone number',
                passwordRequired: 'Please enter your password',
                passwordPlaceholder: 'Enter password',
                usernameRequired: 'Please enter your username',
                usernamePlaceholder: 'Username (3-20 characters)',
                usernameLength: 'Username must be 3-20 characters',
                passwordLength: 'Password must be 6-20 characters',
                confirmPasswordRequired: 'Please confirm your password',
                confirmPasswordPlaceholder: 'Confirm password',
                passwordMismatch: 'Passwords do not match',
                login: 'Login',
                register: 'Register',
                loginSuccess: 'Login successful',
                loginFailed: 'Login failed. Please check your phone number and password.',
                registerSuccess: 'Registration successful. Please login.',
                registerFailed: 'Registration failed',
                noAccount: "Don't have an account?",
                registerNow: 'Register Now',
                haveAccount: 'Already have an account?',
                loginNow: 'Login Now'
            }
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

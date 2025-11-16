// src/utils/device.ts
import type { DeviceTemplate } from '../types/device'

/** 拼出 /src/assets/{folder}/{state}.png 的路径 */
export const getDeviceIconPath = (folder: string, state: string) => {
    return new URL(`../assets/${folder}/${state}.png`, import.meta.url).href
}

/** 给定模板数组和设备模板名，查出某个 API 的 EndState */
export const getEndStateByApi = (
    templates: DeviceTemplate[],
    templateName: string,
    apiName: string
): string | null => {
    const tpl = templates.find(t => t.name === templateName)
    if (!tpl) return null
    const api = tpl.manifest.APIs.find(a => a.Name === apiName)
    return api ? api.EndState : null
}

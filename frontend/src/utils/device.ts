// src/utils/device.ts
import type {
    BasicDeviceInfo,
    DeviceApiView,
    DeviceManifest,
    DeviceStateView,
    DeviceTemplate,
    DeviceVariableView
} from '../types/device'
import {DeviceNode} from "../types/board.ts";

/** 拼出 /src/assets/{folder}/{state}.png 的路径 */
export const getDeviceIconPath = (folder: string, state: string) => {
    return new URL(`../assets/${folder}/${state}.png`, import.meta.url).href
}

export const getNodeIcon = (node: DeviceNode) => {
    const folder = node.templateName
    const state = node.state || 'Working'
    return getDeviceIconPath(folder, state)
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

/**
 * 从 manifest + 兜底的 props 信息中，整理出基本信息
 */
export const extractBasicDeviceInfo = (
    manifest: DeviceManifest | null | undefined,
    fallbackName: string,
    instanceLabel: string,
    fallbackDescription: string
): BasicDeviceInfo => {
    const name =
        manifest?.Name ??
        fallbackName

    const description =
        manifest?.Description ??
        fallbackDescription

    const initState = manifest?.InitState ?? ''

    const impacted =
        Array.isArray(manifest?.ImpactedVariables)
            ? manifest!.ImpactedVariables
            : []

    return {
        name,
        instanceLabel,
        description,
        initState,
        impactedVariables: impacted
    }
}

/**
 * Variables 区：
 * - 优先使用 InternalVariables
 * - 如果没有 InternalVariables，就用 ImpactedVariables 填占位
 */
export const extractDeviceVariables = (
    manifest: DeviceManifest | null | undefined
): DeviceVariableView[] => {
    if (!manifest) return []

    const internal = manifest.InternalVariables
    if (Array.isArray(internal) && internal.length) {
        return internal
            .map((v: any) => ({
                name: v.Name ?? v.VariableName ?? '',
                value:
                    v.InitialValue ??
                    v.Value ??
                    '',
                trust: v.Trust ?? ''
            }))
            .filter(v => v.name)
    }

    if (Array.isArray(manifest.ImpactedVariables) && manifest.ImpactedVariables.length) {
        return manifest.ImpactedVariables.map(name => ({
            name,
            value: '',
            trust: ''
        }))
    }

    return []
}

/**
 * States 区：来自 WorkingStates
 */
export const extractDeviceStates = (
    manifest: DeviceManifest | null | undefined
): DeviceStateView[] => {
    if (!manifest || !Array.isArray(manifest.WorkingStates)) return []
    return manifest.WorkingStates.map(ws => ({
        name: ws.Name,
        description: ws.Description,
        trust: ws.Trust
    }))
}

/**
 * APIs 区：来自 APIs
 */
export const extractDeviceApis = (
    manifest: DeviceManifest | null | undefined
): DeviceApiView[] => {
    if (!manifest || !Array.isArray(manifest.APIs)) return []
    return manifest.APIs.map(api => ({
        name: api.Name,
        from: api.StartState,
        to: api.EndState,
        description: api.Description ?? ''
    }))
}
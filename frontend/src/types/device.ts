// src/types/device.ts

import {Specification} from "./spec.ts";
import {DeviceEdge} from "./board.ts";

export interface DeviceAPI {
    Name: string
    StartState: string
    EndState: string
    Trigger?: string | null
    Assignments?: any[]
    Signal?: boolean
    Description?: string
}

export interface DeviceWorkingState {
    Name: string
    Dynamics: Array<{
        VariableName: string
        ChangeRate: string
    }>
    Invariant: string
    Description: string
    Trust: string
}

export interface DeviceManifest {
    Name: string
    Description: string
    InternalVariables: any[]
    ImpactedVariables: string[]
    InitState: string
    WorkingStates: DeviceWorkingState[]
    Transitions?: any[]
    APIs: DeviceAPI[]
}

export interface DeviceTemplate {
    id: string
    name: string           // 用来对应 assets/{name}/
    manifest: DeviceManifest
}

/* ======================================================
 *  以下是给 DeviceDialog.vue 用的“展示数据整理”工具函数
 *  只负责把 manifest / props 里的原始结构，整理成扁平数据
 * ====================================================== */

/** 基本信息区的数据结构 */
export interface BasicDeviceInfo {
    name: string
    instanceLabel: string
    description: string
    initState: string
    impactedVariables: string[]   // 保留为数组，展示时你可以 join
}

/** Variables 区展示结构 */
export interface DeviceVariableView {
    name: string
    value: string
    trust: string
}

/** States 区展示结构 */
export interface DeviceStateView {
    name: string
    description: string
    trust: string
}

/** APIs 区展示结构 */
export interface DeviceApiView {
    name: string
    from: string
    to: string
    description: string
}

// 对话框元数据类型
export interface DeviceDialogMeta {
    nodeId: string
    deviceName: string
    description: string
    label: string
    manifest: DeviceManifest | null
    rules: DeviceEdge[]
    specs: Specification[]
}
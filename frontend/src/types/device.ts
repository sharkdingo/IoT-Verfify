// src/types/device.ts

import type { DeviceEdge } from "./edge"
import type { Specification } from "./spec"

// ==== 核心 Manifest 结构 ====

export interface InternalVariable {
    Name: string
    Description?: string
    IsInside?: boolean
    PublicVisible?: boolean
    Trust?: string          // "trusted" | "untrusted"
    Privacy?: string        // "public" | "private"
    // 数值型属性
    LowerBound?: number
    UpperBound?: number
    NaturalChangeRate?: string
    // 枚举型属性
    Values?: string[]
}

export interface Dynamic {
    VariableName: string
    ChangeRate: string
}

export interface WorkingState {
    Name: string
    Dynamics: Dynamic[]
    Invariant: string
    Description: string
    Trust: string           // "trusted" | "untrusted"
    Privacy?: string        // "public" | "private"
}

export interface DeviceAPI {
    Name: string
    StartState: string
    EndState: string
    Trigger?: string | null
    Assignments?: any[]
    Signal?: boolean
    Description?: string
}

export interface DeviceManifest {
    Name: string
    Description: string
    Modes?: string[]
    InternalVariables: InternalVariable[]
    ImpactedVariables: string[]
    InitState: string
    WorkingStates: WorkingState[]
    Transitions?: any[]
    APIs: DeviceAPI[]
}

export interface DeviceTemplate {
    id: string
    name: string
    manifest: DeviceManifest
}

// ==== 视图辅助类型 (View Models) ====

export interface BasicDeviceInfo {
    name: string
    instanceLabel: string
    description: string
    initState: string
    impactedVariables: string[]
}

export interface DeviceVariableView {
    name: string
    value: string
    trust: string
}

export interface DeviceStateView {
    name: string
    description: string
    trust: string
}

export interface DeviceApiView {
    name: string
    from: string
    to: string
    description: string
}

export interface DeviceDialogMeta {
    nodeId: string
    deviceName: string
    description: string
    label: string
    manifest: DeviceManifest | null
    rules: DeviceEdge[]
    specs: Specification[]
}
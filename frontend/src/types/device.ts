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
    // Backend Dynamic requires exactly one of Value XOR ChangeRate (both optional here).
    ChangeRate?: string
    Value?: string
}

export interface WorkingState {
    Name: string
    Dynamics: Dynamic[]
    Invariant: string
    Description: string
    Trust: string           // "trusted" | "untrusted"
    Privacy?: string        // "public" | "private"
}

// Matches backend device-template-schema.json Transition.Trigger.
export interface DeviceTrigger {
    Attribute: string
    Relation: string
    Value: string
}

// Matches backend DeviceTemplateDto.DeviceManifest.Assignment { Attribute, Value }.
export interface DeviceAssignment {
    Attribute: string
    Value: string
}

export interface DeviceAPI {
    Name: string
    StartState: string
    EndState: string
    // backend/device-template-schema.json is authoritative: API Trigger is always null.
    Trigger?: null
    Assignments?: DeviceAssignment[]
    Signal?: boolean
    Description?: string
}

// Matches backend DeviceTemplateDto.DeviceManifest.Content { Name, Privacy, IsChangeable }.
export interface DeviceContent {
    Name: string
    Privacy?: string        // "public" | "private"
    IsChangeable?: boolean
}

export interface DeviceManifest {
    Name: string
    Description: string
    Modes?: string[]
    InternalVariables: InternalVariable[]
    ImpactedVariables: string[]
    InitState: string
    WorkingStates: WorkingState[]
    // Transition.Trigger uses DeviceTrigger; custom form creation is API-only, JSON import may include transitions.
    Transitions?: any[]
    APIs: DeviceAPI[]
    Contents?: DeviceContent[]
}

export interface DeviceTemplate {
    id?: number      // 后端 Long；创建时无 id，响应中才有
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

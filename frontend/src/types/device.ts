// src/types/device.ts

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

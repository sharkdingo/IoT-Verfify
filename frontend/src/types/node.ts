// Match backend VariableStateDto / PrivacyStateDto (persisted on a canvas node and
// reused when converting canvas data into a verification request).
export interface NodeVariableState {
    name: string
    value: string
    trust?: string | null   // "trusted" | "untrusted"; board responses may serialize an inherited value as null
}

export interface NodePrivacyState {
    name: string
    privacy: string         // "public" | "private"
}

export interface DeviceNode {
    id: string
    templateName: string
    label: string
    position: { x: number; y: number }
    // Required for templates with Modes. No-mode templates may carry the canvas
    // placeholder "Working"; model request builders omit it for stateless devices.
    state: string
    width: number
    height: number
    // Runtime state persisted with the node (backend DeviceNodeDto). Optional because
    // not every node carries overrides; used when building a verification request.
    currentStateTrust?: string | null      // "trusted" | "untrusted"
    currentStatePrivacy?: string | null    // "public" | "private"
    variables?: NodeVariableState[]
    privacies?: NodePrivacyState[]
}

// src/types/panel.ts
//
// The old collapsible-panel / dock system was removed; its DockSide / DockState /
// PanelPosition types lived here but are no longer referenced (canvas.ts owns the
// layout DTO types used by /board/layout). Only PanelActive remains in use.

// Matches backend BoardActiveDto: both `input` and `status` are required (@NotNull)
// lists of active tab ids.
export interface PanelActive {
    input: string[]
    status: string[]
}

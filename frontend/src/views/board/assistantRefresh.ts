import { STREAM_REFRESH_TARGETS } from '@/types/chat'

/**
 * Which board state an assistant `REFRESH_DATA` command invalidates.
 *
 * The assistant mutates the board through the same service methods the UI uses, so its edits carry
 * the same consequences — including undo availability, because its rule and specification tools go
 * through the journal-recording write path. Routing every target through one table keeps that
 * parity explicit instead of leaving it to remember-to-call discipline at each handler.
 *
 * The target names themselves come from `types/chat.ts`, which is the wire contract; keeping a second
 * copy here let the two drift.
 */
export const ASSISTANT_REFRESH_TARGETS = STREAM_REFRESH_TARGETS

export type AssistantRefreshTarget = typeof ASSISTANT_REFRESH_TARGETS[number]

export const isAssistantRefreshTarget = (value: unknown): value is AssistantRefreshTarget =>
  typeof value === 'string' && (ASSISTANT_REFRESH_TARGETS as readonly string[]).includes(value)

/**
 * What a target requires beyond reloading its own collection.
 *
 * `invalidatesOtherTabs` marks the targets that changed persisted board state, as opposed to merely
 * re-reading a list the server already owns.
 */
export interface AssistantRefreshEffects {
  /** The `defineExpose` method on the board view that reloads this target. */
  method: string
  /**
   * Whether the assistant changed persisted board state, as opposed to re-reading a result list.
   *
   * True publishes a board invalidation, which *other* open tabs answer with a full semantic
   * snapshot reload. `BroadcastChannel` does not deliver to the tab that posted, so this tab's own
   * undo availability is restored by the reload path it runs directly — not by its own broadcast.
   */
  invalidatesOtherTabs: boolean
}

const EFFECTS: Record<AssistantRefreshTarget, AssistantRefreshEffects> = {
  rule_list: { method: 'refreshRules', invalidatesOtherTabs: true },
  spec_list: { method: 'refreshSpecifications', invalidatesOtherTabs: true },
  board_state: { method: 'refreshAllBoardState', invalidatesOtherTabs: true },
  device_list: { method: 'refreshDevices', invalidatesOtherTabs: true },
  environment_list: { method: 'refreshEnvironmentVariables', invalidatesOtherTabs: true },
  template_list: { method: 'refreshDeviceTemplates', invalidatesOtherTabs: true },

  // Run history is result-oriented: nothing about the board model changed, so no tab needs
  // invalidating and nothing became reversible.
  run_history: { method: 'refreshRunHistory', invalidatesOtherTabs: false }
}

export const assistantRefreshEffects = (
  target: AssistantRefreshTarget
): AssistantRefreshEffects => EFFECTS[target]

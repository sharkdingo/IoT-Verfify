import type { RuleForm } from '@/types/rule'
import type { Specification } from '@/types/spec'

/**
 * The follow-ups every rule/specification mutation owes the rest of the board.
 *
 * These four were previously hand-assembled at each of ~10 call sites, in slightly different
 * orders and with slightly different omissions — rule reorder never reported undo availability,
 * and undo/redo never rebuilt the canvas edges. Nothing detected either gap, because a later
 * unrelated refresh usually repaired the state, which made the omissions look harmless.
 *
 * Centralising them turns "remember four things" into one call, so a new mutation cannot forget
 * one and a missing dependency is a type error rather than a silent staleness bug.
 */
export interface BoardSemanticScene {
  /** Authoritative rule list, when the mutation returned one. */
  rules?: RuleForm[]
  /** Authoritative specification list, when the mutation returned one. */
  specs?: Specification[]
  /** Undo availability the server reported, when this mutation is reversible. */
  availability?: { canUndo?: boolean; canRedo?: boolean }
}

export interface BoardSemanticCommitPorts {
  setRules: (rules: RuleForm[]) => void
  setSpecs: (specs: Specification[]) => void
  /** Canvas connection lines are derived from rules, so they are rebuilt whenever rules change. */
  syncRuleDerivedEdges: () => void
  /**
   * A semantic change invalidates any displayed verdict; it described the previous model.
   *
   * Mutations that run inside the board mutation queue are already marked stale by its
   * fingerprint comparison, so for them this is a harmless second call. It is load-bearing for
   * undo/redo, which applies an authoritative result *outside* the queue.
   */
  markVerificationResultStale: () => void
  /** Mirrors server-reported undo availability. Omitted availability must not clear real history. */
  syncUndoAvailability: (availability: { canUndo?: boolean; canRedo?: boolean }) => void
  /** Drops an inspector focus whose target no longer exists in the authoritative collections. */
  clearDanglingFocus: (scene: { rules?: RuleForm[]; specs?: Specification[] }) => void
}

/**
 * Applies one semantic board mutation's authoritative result.
 *
 * Order matters and is fixed here rather than per call site: collections first, then everything
 * derived from them, so no derived value is ever computed from a stale collection.
 */
export const createBoardSemanticCommit = (ports: BoardSemanticCommitPorts) =>
  (scene: BoardSemanticScene): void => {
    if (scene.rules) ports.setRules(scene.rules)
    if (scene.specs) ports.setSpecs(scene.specs)

    // Edges are a projection of rules, so they must be rebuilt in the same step. Relying on a
    // later refresh to do it is correct only by accident.
    if (scene.rules) ports.syncRuleDerivedEdges()

    ports.clearDanglingFocus(scene)

    // Callers pass the whole mutation DTO, so the real protection is inside `syncUndoAvailability`:
    // it copies `canUndo`/`canRedo` only when each is actually a boolean, so a non-reversible
    // mutation that omits them cannot clear real server history.
    if (scene.availability) ports.syncUndoAvailability(scene.availability)

    ports.markVerificationResultStale()
  }

export type BoardSemanticCommit = ReturnType<typeof createBoardSemanticCommit>

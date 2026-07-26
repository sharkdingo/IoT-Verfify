/**
 * Shared recommendation-response accounting types.
 *
 * The rule / device / specification recommenders all report why candidates were dropped or
 * altered before the user sees them, using the same two shapes. They were previously declared
 * independently in `api/board.ts` and `api/rules.ts`; keeping one definition here means a
 * contract change cannot land in one copy only.
 */

/** A candidate the server rejected, with the reason code the UI maps to explanatory copy. */
export interface RecommendationFilteredItem {
  type: string
  index: number
  reasonCode: string
  reason: string
  label?: string
}

/** A candidate the server kept but modified, carrying the values it actually applied. */
export interface RecommendationAdjustmentItem {
  type: string
  index?: number
  reasonCode: string
  reason: string
  label?: string
  appliedValues: Record<string, unknown>
}

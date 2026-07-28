/**
 * Encoding and validation for the board's deep-link query params.
 *
 * Kept pure so the URL contract can be tested without a router or a mounted board.
 * Which state is allowed in the URL — and which is deliberately excluded — is recorded in
 * docs/guides/frontend-ui-conventions.md.
 */

export const BOARD_RUN_KINDS = ['verification', 'simulation', 'exploration'] as const
export type BoardRunKind = typeof BOARD_RUN_KINDS[number]

export type BoardRunTarget = {
  kind: BoardRunKind
  runId: number
  /** Counterexample trace under a verification run. */
  traceId?: number
  /** Candidate finding under an exploration run. */
  findingId?: number
}

/** `?run=` uses `kind:id` so one param carries the whole "what am I looking at" answer. */
const RUN_PATTERN = /^([a-z]+):(\d+)$/

const isRunKind = (value: string): value is BoardRunKind =>
  (BOARD_RUN_KINDS as readonly string[]).includes(value)

const parsePositiveInt = (value: unknown): number | null => {
  if (typeof value !== 'string' || !/^\d+$/.test(value)) return null
  const parsed = Number(value)
  return Number.isSafeInteger(parsed) && parsed > 0 ? parsed : null
}

const firstValue = (value: unknown): string | undefined => {
  if (typeof value === 'string') return value
  // vue-router yields an array when a param is repeated; a repeated param is ambiguous,
  // so treat only the first occurrence as meaningful.
  if (Array.isArray(value) && typeof value[0] === 'string') return value[0]
  return undefined
}

export type BoardRunQuery = Record<string, unknown>

/**
 * Reads a deep-link target out of a route query.
 *
 * Returns `null` for anything malformed, unknown, or internally inconsistent (a `trace` on a
 * simulation run, a `finding` on a verification run). Callers must treat `null` as "show the
 * plain board", never as an empty result.
 */
export const parseBoardRunTarget = (query: BoardRunQuery): BoardRunTarget | null => {
  const raw = firstValue(query.run)
  if (!raw) return null

  const match = RUN_PATTERN.exec(raw)
  if (!match) return null

  const [, kind, id] = match
  if (!isRunKind(kind)) return null

  const runId = parsePositiveInt(id)
  if (runId === null) return null

  const target: BoardRunTarget = { kind, runId }

  const traceId = parsePositiveInt(firstValue(query.trace))
  const findingId = parsePositiveInt(firstValue(query.finding))

  // Sub-artifact params only mean something for the run kind that owns them. Silently
  // dropping a mismatched one would restore a surface the link did not describe.
  if (kind === 'verification') {
    if (findingId !== null) return null
    if (traceId !== null) target.traceId = traceId
  } else if (kind === 'exploration') {
    if (traceId !== null) return null
    if (findingId !== null) target.findingId = findingId
  } else if (traceId !== null || findingId !== null) {
    return null
  }

  return target
}

/**
 * Builds the deep-link params for a target, preserving unrelated query params.
 * Passing `null` clears the deep link.
 */
export const applyBoardRunTarget = (
  query: BoardRunQuery,
  target: BoardRunTarget | null
): Record<string, string> => {
  const next: Record<string, string> = {}
  for (const [key, value] of Object.entries(query)) {
    if (key === 'run' || key === 'trace' || key === 'finding') continue
    const single = firstValue(value)
    if (single !== undefined) next[key] = single
  }

  if (!target) return next

  next.run = `${target.kind}:${target.runId}`
  if (target.kind === 'verification' && target.traceId !== undefined) {
    next.trace = String(target.traceId)
  }
  if (target.kind === 'exploration' && target.findingId !== undefined) {
    next.finding = String(target.findingId)
  }
  return next
}

/** True when both describe the same surface, so sync can skip redundant navigation. */
export const isSameBoardRunTarget = (
  a: BoardRunTarget | null,
  b: BoardRunTarget | null
): boolean => {
  if (a === null || b === null) return a === b
  return a.kind === b.kind
    && a.runId === b.runId
    && (a.traceId ?? null) === (b.traceId ?? null)
    && (a.findingId ?? null) === (b.findingId ?? null)
}

/** True when the route carries deep-link params that did not parse into a valid target. */
export const hasUnusableBoardRunParams = (query: BoardRunQuery): boolean => {
  const present = ['run', 'trace', 'finding'].some(key => firstValue(query[key]) !== undefined)
  return present && parseBoardRunTarget(query) === null
}

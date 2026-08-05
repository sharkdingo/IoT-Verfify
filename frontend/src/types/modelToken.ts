/**
 * Provenance boundary for user-visible model identifiers.
 *
 * The runtime list is derived from the same array as the type, so a fourth provenance value cannot be added
 * to one and forgotten in the other. Three boundary validators (`api/board.ts`, `utils/fixResponse.ts`,
 * `utils/traceStateResponse.ts`) each built their own `new Set(['BUNDLED', 'CUSTOM', 'UNKNOWN'])` while this
 * module already owned the vocabulary — so the type said one thing and three hand-maintained copies had to
 * agree with it by hand. The validators themselves stay separate: each throws its own typed contract error,
 * which the repo's typed-error rule requires.
 */
export const MODEL_TOKEN_SOURCES = ['BUNDLED', 'CUSTOM', 'UNKNOWN'] as const

export type ModelTokenSource = typeof MODEL_TOKEN_SOURCES[number]

export const MODEL_TOKEN_SOURCE_SET: ReadonlySet<string> = new Set(MODEL_TOKEN_SOURCES)

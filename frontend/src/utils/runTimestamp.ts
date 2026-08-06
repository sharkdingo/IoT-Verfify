/**
 * A run's timestamp, formatted for the locale — with one answer for "there isn't one".
 *
 * Three surfaces list the same runs and each had its own copy of this, agreeing on the locale tag and disagreeing
 * on the empty case: `FuzzingResultDialog` returned the raw value (blank for an empty string),
 * `TraceHistoryPanel` returned blank explicitly, and `SimulationTimeline` returned "unknown". So a run with no
 * timestamp read as blank in two places and 未知 in the third.
 *
 * "Unknown" is the answer worth keeping. A blank cell is indistinguishable from a rendering failure, and in a
 * verification tool the difference between "no timestamp recorded" and "the UI dropped it" is exactly the kind of
 * ambiguity that sends someone looking for a bug that is not there.
 *
 * An unparseable *non-empty* value is returned as-is rather than replaced. It is real data the server sent, and
 * showing it lets the reader see what arrived; replacing it with "unknown" would hide a contract problem behind a
 * tidy label.
 */
export const formatRunTimestamp = (
  value: string | null | undefined,
  locale: string,
  t: (key: string) => string
): string => {
  if (!value) return t('app.unknown')
  const date = new Date(value)
  if (Number.isNaN(date.getTime())) return value
  return date.toLocaleString(locale.toLowerCase().startsWith('zh') ? 'zh-CN' : 'en-US')
}

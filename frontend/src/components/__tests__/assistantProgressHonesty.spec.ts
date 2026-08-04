import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * The assistant's progress trace must not contradict itself.
 *
 * Two defects here shared a cause: a rendering derived from an event's *stage* alone, with no reference to
 * whether the turn had since ended or whether a count was actually non-zero. Both are invisible in a diff and
 * invisible to a unit test that only checks content — the text is present and correct, it just claims the wrong
 * thing.
 */

const chatView = () => readFileSync(join(__dirname, '../ChatView.vue'), 'utf8')
const i18n = () => readFileSync(join(__dirname, '../../assets/i18n.ts'), 'utf8')

describe('assistant progress honesty', () => {
  it('reads the final step in the past tense once the turn is over', () => {
    // `WRITING_RESPONSE` kept its present-progressive detail — "正在根据工具的实际结果说明…", *currently*
    // explaining — indefinitely after the answer landed. A settled panel measured as claiming both states at
    // once (`statesCompleted: true, statesStillRunning: true`), and a review reached the same conclusion from
    // the screen: the text "can read as still in progress, so completion is somewhat ambiguous".
    //
    // Only the terminal stage needs the distinction: every earlier stage is followed by another entry, so its
    // progressive reads naturally as a log of what was happening then.
    const source = chatView()
    expect(source).toMatch(/progressEventDetail\s*=\s*\(progress: StreamProgress,\s*streaming\s*=\s*false\)/)
    expect(source).toMatch(/streaming\s*\n?\s*\?\s*t\('app\.chat\.progressWritingDetail'\)\s*\n?\s*:\s*t\('app\.chat\.progressWritingDetailDone'\)/)
    // The template must actually pass the streaming flag, or the branch is dead.
    expect(source).toContain('progressEventDetail(progress, isActiveAssistantMessage(index))')

    // Both locales carry the finished variant.
    const strings = i18n()
    expect((strings.match(/progressWritingDetailDone:/g) || []).length).toBe(2)
  })

  it('colours an execution metric only when its count is non-zero', () => {
    // `is-success`, `is-error` and `is-warning` were applied unconditionally, so a clean turn rendered
    // "0 failed" in the error colour and "0 unconfirmed" in the warning colour. A measurement of the panel
    // read the error styling as a genuine failure — `showsError: true, errorText: "0 failed"` — which is the
    // same inference a user makes at a glance. Zero failures is the good outcome.
    const source = chatView()
    const metrics = source.slice(
      source.indexOf('class="chat-execution-metrics"'),
      source.indexOf('class="chat-execution-events"')
    )
    expect(metrics.length).toBeGreaterThan(0)

    // No static status class inside the metrics block.
    expect(metrics).not.toMatch(/class="is-(success|error|warning)"/)
    // Each of the three is conditional on its own count.
    for (const [role, field] of [['is-success', 'successful'], ['is-error', 'failed'], ['is-warning', 'unconfirmed']]) {
      expect(metrics, `${field} should only wear ${role} when positive`)
        .toMatch(new RegExp(`\\.${field} > 0 \\? '${role}' : ''`))
    }
  })
})

import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * A viewport resize must cancel a panel gesture *immediately*, and re-clamp lazily.
 *
 * `handleChatViewportResize` once did both inside one `throttle(..., 200)`. That throttle fires on the
 * TRAILING edge, so `stopPanelInteraction()` could run up to 200ms after the resize that scheduled it —
 * long enough to land on a drag the user had begun in between and cancel it. The panel then moves a few
 * pixels and stops.
 *
 * Found in CI, not by reading: `Full CI` failed "releases an interrupted panel gesture when the viewport
 * changes" with the panel 19px from its origin where the gesture asked for 100 — on a commit whose only
 * change was a documentation anchor. It passed on the commit before it and three times locally, which is
 * what a race looks like rather than a regression. The repo's E2E contract is explicit that a flake there
 * is a defect report rather than noise to retry away (`.github/scripts/run-e2e.sh`), so it is fixed here.
 *
 * Splitting the two is safe because `stopPanelInteraction` is idempotent and does no layout work — it
 * clears a ref, removes listeners and releases pointer capture. `clampExistingChatPosition` is the part
 * that reads geometry, and it keeps the throttle.
 *
 * Source-text assertions rather than a mounted render: the race is in *when* two calls happen relative to
 * a throttle, which a component mount cannot express without faking timers around a real resize.
 */
describe('chat panel viewport-resize race', () => {
  const source = readFileSync(
    join(process.cwd(), 'src/components/ChatView.vue'), 'utf8')

  /** The resize handler body, so an assertion cannot match a similarly-named helper elsewhere. */
  const handler = (() => {
    const at = source.indexOf('const handleChatViewportResize')
    expect(at, 'the resize handler should exist').toBeGreaterThan(-1)
    const end = source.indexOf('\n}', at)
    expect(end, 'the handler should be a block').toBeGreaterThan(at)
    return source.slice(at, end + 2)
  })()

  it('cancels the gesture outside any throttle', () => {
    // The handler itself must not BE a throttle: that is the shape that delayed the cancel.
    expect(handler, 'the resize handler must not be wrapped in a throttle')
      .not.toMatch(/const handleChatViewportResize\s*=\s*throttle\(/)
    // And it must still cancel, or an in-flight drag survives a resize that invalidated its geometry.
    expect(handler, 'a resize must stop the panel interaction')
      .toMatch(/stopPanelInteraction/)
  })

  it('keeps the geometry re-clamp throttled', () => {
    // The throttle is wanted for the clamp: a resize fires continuously while a window is dragged, and
    // `clampExistingChatPosition` reads layout. Dropping it would trade this race for a slower one.
    const clampAt = source.indexOf('const clampChatPositionAfterResize')
    expect(clampAt, 'the throttled clamp should exist').toBeGreaterThan(-1)
    const clamp = source.slice(clampAt, source.indexOf('\n', source.indexOf('}, 200)', clampAt)))
    expect(clamp, 'the clamp keeps its throttle').toMatch(/throttle\(/)
    expect(clamp, 'and still re-clamps').toContain('clampExistingChatPosition')
  })
})

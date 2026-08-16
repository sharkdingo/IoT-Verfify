/**
 * Click a control that sits under an Element Plus tooltip popper.
 *
 * The board annotates its action-dock buttons with `HintTooltip`, whose popper is teleported to
 * `body` at `z-index: 2009` and fades out over `hide-after: 80ms`. Clicking a dock button therefore
 * leaves a popper floating over the panel that button just opened — and a control inside that panel
 * can be underneath it.
 *
 * `click({ force: true })` does not fix this, and believing it did cost two CI failures. `force`
 * skips Playwright's *hit-target check*; it does not change where the browser delivers the event.
 * So the click still lands on whatever is topmost, and instead of retrying and timing out with
 * "intercepts pointer events" — which at least names the cause — it silently dispatches to the
 * popper and reports success. The test then fails several statements later on a field that never
 * appeared, which is what made this read as a product bug.
 *
 * Measured from the Full CI trace for run 31943156194 (fire-evacuation scenario): the popper for
 * `open-verification-panel` was at `translate(968px, -476px)` with `inset: auto auto 0 0`, i.e.
 * occupying x ≥ 968, y ≤ 244 in the 1280×720 viewport. The forced click on
 * `verification-attack-toggle` was delivered at (1004, 218) — inside it. The switch stayed
 * `aria-checked="false"`, the `v-if`-gated attack section never rendered, and the run failed 180s
 * later waiting for `verification-attack-budget`.
 *
 * Moving the pointer away first lets the popper close, so the click reaches the control. The move
 * target is the viewport origin: the top-left corner holds the "Reset workspace" heading, which
 * carries no tooltip of its own, so parking there cannot open a second popper.
 * `authority-model-audit.spec.ts` already uses `page.mouse.move(4, 4)` to retract a canvas hover
 * for the same reason.
 *
 * The wait is on the popper being gone rather than a fixed sleep, so it costs ~80ms in the normal
 * case and still holds under CI load. `aria-hidden` is the state Element Plus toggles while the
 * element itself stays in the DOM (`HintTooltipDisabled.spec.ts` records the same distinction), so
 * a plain visibility check is not enough.
 */
import { expect, type Locator, type Page } from '@playwright/test'

/** Element Plus keeps closed poppers mounted, so "gone" means hidden, not absent. */
const openPoppers = (page: Page): Locator =>
  page.locator('.iot-info-tooltip-popper:not([aria-hidden="true"])')

export const dismissHintTooltips = async (page: Page): Promise<void> => {
  await page.mouse.move(4, 4)
  await expect(openPoppers(page)).toHaveCount(0, { timeout: 5_000 })
}

/** Dismiss any open hint popper, then click normally — with the hit-target check intact. */
export const clickUnderTooltip = async (page: Page, target: Locator): Promise<void> => {
  await dismissHintTooltips(page)
  await target.click()
}

<script setup lang="ts">
/**
 * A themed tooltip for a control that already exists.
 *
 * The board carried **179 native `title=` attributes**, which the browser renders as an OS tooltip: grey,
 * unstyled, roughly a second of delay, no dark-theme awareness, and nothing at all on touch. That is what made
 * every hint in the product look unfinished.
 *
 * `InfoTooltip` could not be reused for them. It renders its own `ⓘ` badge, so it *adds* a help affordance; these
 * sites need to *annotate a button that is already there*. Same `el-tooltip` underneath and the same popper class,
 * so the two look identical — the only difference is who owns the trigger.
 *
 * Replacing `title` is safe here, and that was measured before starting: of those 179, **zero** were an icon-only
 * control relying on `title` as its accessible name. Every one either duplicated an `aria-label` (57 buttons did
 * so verbatim) or annotated an element that already had visible text. The accessible name stays on the wrapped
 * control; this adds only the visual hint.
 *
 * Two cases it is deliberately not for:
 * - **Truncated text.** `SystemInspector`'s `data-full-text` sets `title` only when the text is genuinely
 *   clipped, and that file already records why a tooltip is the wrong answer: it "answers one device at a time,
 *   on hover, and never helps a keyboard or touch user scanning a list".
 * - **A hint that repeats a visible label.** Five buttons had a `title` restating the words printed beside the
 *   icon; those were deleted rather than converted, per the same rule that keeps a toast off a result already on
 *   screen.
 */
import { ElTooltip } from 'element-plus'
import 'element-plus/theme-chalk/el-popper.css'
import 'element-plus/theme-chalk/el-tooltip.css'

withDefaults(defineProps<{
  /** The hint. Empty disables the tooltip, so a conditional hint needs no `v-if` at the call site. */
  content?: string | null
  placement?: 'top' | 'top-start' | 'top-end' | 'bottom' | 'bottom-start' | 'bottom-end' | 'left' | 'right'
}>(), {
  content: '',
  placement: 'top'
})
</script>

<template>
  <ElTooltip
    :content="content || ''"
    :disabled="!content"
    :placement="placement"
    :show-after="120"
    :hide-after="80"
    :teleported="true"
    popper-class="iot-info-tooltip-popper"
  >
    <slot />
  </ElTooltip>
</template>

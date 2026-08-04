import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * A collapsible group opens when it has something to show.
 *
 * The template repository rendered both of its groups with a bare `open` attribute, so on a dense board
 * "Custom Templates 0" appeared **expanded while holding nothing** — a heading, a border and vertical space spent
 * on an empty set, in the panel where space is scarcest. Measured on a 12-device board: 6 of 7 detail sections
 * expanded at once, one of them empty. After the fix: 5 of 7, and the empty group closed.
 *
 * The group is still *listed* rather than hidden. Removing it would leave a user wondering where custom templates
 * go, and "Custom Templates 0" is a truthful answer to that question — the count is information. Collapsed is the
 * honest middle: the fact stays available, the space does not. That distinction is why this is a disclosure fix
 * rather than a deletion.
 *
 * Pinned because `open` is the natural thing to type. It looks like a convenience, costs nothing at build time,
 * and its effect only shows once a user has enough content for space to matter — which is exactly when it hurts.
 */

const controlCenter = () => readFileSync(join(__dirname, '../ControlCenter.vue'), 'utf8')

describe('empty group disclosure', () => {
  const withoutComments = (text: string) => text.replace(/<!--[\s\S]*?-->/g, '')

  it('opens a template group only when it holds templates', () => {
    const source = withoutComments(controlCenter())
    const at = source.indexOf('template-group rounded-lg border')
    expect(at, 'the template group element should exist').toBeGreaterThan(-1)
    // The opening tag: from the element start to its closing bracket.
    // A fixed window from the element start, not indexOf('>'): that lands on the '>' inside
    // `templates.length > 0` and truncated the tag before the binding it was looking for.
    const tagStart = source.lastIndexOf('<details', at)
    const block = source.slice(tagStart, tagStart + 400)

    expect(block, 'the group should bind its open state to its content')
      .toMatch(/:open="group\.templates\.length > 0"/)
  })

  it('never leaves a collapsible unconditionally open', () => {
    // A bare `open` on any `<details>` is the shape of the defect, wherever it appears. Scanning the whole file
    // rather than the one element keeps a second instance from being added elsewhere and going unnoticed — there
    // are currently none, which is the state worth holding.
    const source = withoutComments(controlCenter())
    const offenders: string[] = []
    source.split('\n').forEach((line, index) => {
      if (/^\s*open\s*$/.test(line)) offenders.push(`ControlCenter.vue:${index + 1}`)
    })
    expect(offenders, 'a bare `open` attribute forces a section expanded regardless of content').toEqual([])
  })

  it('still renders the empty group, so its count remains visible', () => {
    // The failure mode on the other side: hiding an empty group entirely. Then a user with no custom templates has
    // no idea the category exists, and "0" — which is real information — is thrown away to save the same space
    // that collapsing already saves.
    const source = withoutComments(controlCenter())
    // Both groups come from one list, unconditionally, and are filtered only by the search box.
    expect(source, 'both groups are rendered from templateGroups without a per-group v-if')
      .toMatch(/v-for="group in templateGroups"/)
    const at = source.indexOf('v-for="group in templateGroups"')
    const tagStart = source.lastIndexOf('<details', at)
    const block = source.slice(tagStart, source.indexOf('>', at) + 1)
    expect(block, 'a group must not be removed for being empty').not.toMatch(/v-if="group\.templates\.length/)
  })
})

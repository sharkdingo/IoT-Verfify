import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * A suggestion card's title must not promise more than its prompt asks for.
 *
 * The assistant can genuinely edit the board — it calls tools, and `AiDestructiveActionGuard` gates the
 * destructive ones behind a two-turn confirmation. That makes the read/write distinction load-bearing: a user
 * deciding whether to click something needs to know whether it inspects or changes their design.
 *
 * Five cards were titled with imperative verbs — "Add missing rules", "Add key devices", "Generate specs",
 * "补齐规则", "补充关键设备", "生成规约" — while every one of their prompts only says *recommend*. Three
 * independent reviews of the panel, across both locales and three viewports, reported the same worry: the
 * labels "sound potentially mutating, but there is no preview, confirmation, or clear read-only versus write
 * distinction".
 *
 * The titles now name the request. This check keeps them honest, because the drift is invisible in a diff:
 * nothing breaks when a title gains a verb it cannot deliver.
 */

const i18nSource = () => readFileSync(join(__dirname, '../../assets/i18n.ts'), 'utf8')

/** Verbs that assert the assistant will change the board. */
const WRITE_VERBS = /^(Add|Create|Generate|Fix|Apply|Delete|Remove|补齐|补充|添加|生成|删除|修复|应用)/

/** Phrasing that shows the prompt only asks for advice. */
const ADVISORY = /recommend|review|explain|suggest|identify|推荐|请审查|请整理|请指出|请说明|请列/i

describe('assistant suggestion labels', () => {
  it('never titles an advisory prompt with a write verb', () => {
    const source = i18nSource()
    const pattern = /(\w+):\s*\{\s*\n\s*title:\s*'([^']+)',\s*\n\s*text:\s*'([^']{0,400})'/g

    const overstated: string[] = []
    for (const match of source.matchAll(pattern)) {
      const [, key, title, text] = match
      if (WRITE_VERBS.test(title) && ADVISORY.test(text)) {
        overstated.push(`${key}: "${title}" — prompt only asks: "${text.slice(0, 60)}…"`)
      }
    }

    expect(overstated).toEqual([])
  })

  it('keeps a card title and its prompt in the same locale block', () => {
    // A card whose title is translated but whose prompt is not would send an English request from a Chinese
    // interface, which is how a reviewer came to report "the English prompt inside an otherwise Chinese
    // interface" on this panel.
    const source = i18nSource()
    const hasChinese = (value: string) => /[一-鿿]/.test(value)

    const mixed: string[] = []
    const pattern = /(\w+):\s*\{\s*\n\s*title:\s*'([^']+)',\s*\n\s*text:\s*'([^']{0,400})'/g
    for (const match of source.matchAll(pattern)) {
      const [, key, title, text] = match
      if (hasChinese(title) !== hasChinese(text)) {
        mixed.push(`${key}: title and prompt are in different languages`)
      }
    }

    expect(mixed).toEqual([])
  })
})

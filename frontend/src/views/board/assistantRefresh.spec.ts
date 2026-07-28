import { readFileSync } from 'node:fs'
import { dirname, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { describe, expect, it } from 'vitest'

import {
  ASSISTANT_REFRESH_TARGETS,
  assistantRefreshEffects,
  isAssistantRefreshTarget
} from './assistantRefresh'

describe('assistant refresh targets', () => {
  it('rejects an unknown target rather than guessing', () => {
    expect(isAssistantRefreshTarget('rule_list')).toBe(true)
    expect(isAssistantRefreshTarget('rules')).toBe(false)
    expect(isAssistantRefreshTarget('')).toBe(false)
    expect(isAssistantRefreshTarget(undefined)).toBe(false)
  })

  it('treats run history as a result read, not a board change', () => {
    // Nothing about the model changed, so no tab needs invalidating and nothing became reversible.
    expect(assistantRefreshEffects('run_history')).toMatchObject({ invalidatesOtherTabs: false })
  })

  it('invalidates other tabs for every target that reloads board model state', () => {
    for (const target of ASSISTANT_REFRESH_TARGETS) {
      if (target === 'run_history') continue
      expect(assistantRefreshEffects(target).invalidatesOtherTabs, target).toBe(true)
    }
  })

  it('describes every declared target, so a new one cannot be silently unhandled', () => {
    for (const target of ASSISTANT_REFRESH_TARGETS) {
      expect(assistantRefreshEffects(target), target).toBeDefined()
    }
  })

  it('names methods the board view actually exposes', () => {
    // The method name is resolved by string at runtime, so a typo would make the assistant
    // silently report failure. Pin it against the board's real `defineExpose` block.
    const boardSource = readFileSync(
      resolve(dirname(fileURLToPath(import.meta.url)), '..', 'Board.vue'), 'utf8')
    const exposed = boardSource.slice(
      boardSource.indexOf('defineExpose({'),
      boardSource.indexOf('})', boardSource.indexOf('defineExpose({')))

    for (const target of ASSISTANT_REFRESH_TARGETS) {
      expect(exposed, target).toContain(`${assistantRefreshEffects(target).method}:`)
    }
  })
})

describe('parity with the backend', () => {
  it('declares exactly the targets ChatServiceImpl can emit', () => {
    // The backend decides which REFRESH_DATA target to send. A target it emits but we do not
    // declare is silently dropped as "unsupported", so the workspace would keep showing stale
    // data after a successful tool run.
    const chatService = readFileSync(resolve(
      dirname(fileURLToPath(import.meta.url)),
      '..', '..', '..', '..',
      'backend/src/main/java/cn/edu/nju/Iot_Verify/service/impl/ChatServiceImpl.java'
    ), 'utf8')

    const emitted = [...new Set(
      [...chatService.matchAll(/"target",\s*"([a-z_]+)"/g)].map(match => match[1])
    )].sort()

    expect(emitted.length).toBeGreaterThan(0)
    expect([...ASSISTANT_REFRESH_TARGETS].sort()).toEqual(emitted)
  })
})

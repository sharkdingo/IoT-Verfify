import { readFileSync } from 'node:fs'
import { dirname, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { describe, expect, it } from 'vitest'

const currentDirectory = dirname(fileURLToPath(import.meta.url))
const chatViewSource = readFileSync(resolve(currentDirectory, '../ChatView.vue'), 'utf8')

describe('ChatView execution-card layout', () => {
  it('keeps the active execution trace full width instead of overriding it with a narrow bubble', () => {
    const style = chatViewSource.slice(chatViewSource.indexOf('<style scoped>'))
    const executionTraceRules = style.match(/\.assistant-pending-body\.has-execution-trace\s*\{[^}]*\}/g) ?? []

    expect(executionTraceRules).toHaveLength(1)
    expect(executionTraceRules[0]).toContain('width: 100%')
    expect(executionTraceRules[0]).toContain('align-self: stretch')
    expect(executionTraceRules[0]).not.toContain('fit-content')
  })
})

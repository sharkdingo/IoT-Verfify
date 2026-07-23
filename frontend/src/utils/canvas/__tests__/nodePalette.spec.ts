import { describe, expect, it } from 'vitest'

import {
  getNodeAccentColor,
  getNodeBorderColor,
  getNodeColorIndex,
  getNodeSurfaceColor
} from '../nodePalette'

describe('canvas node palette', () => {
  it('assigns a stable theme token to every node id', () => {
    expect(getNodeColorIndex('living-room-light')).toBe(getNodeColorIndex('living-room-light'))
    expect(getNodeColorIndex('living-room-light')).toBeGreaterThanOrEqual(0)
    expect(getNodeColorIndex('living-room-light')).toBeLessThan(8)
    expect(getNodeAccentColor('living-room-light')).toMatch(/^var\(--iot-node-accent-[0-7]\)$/)
  })

  it('derives surfaces and borders from theme-aware semantic colors', () => {
    expect(getNodeSurfaceColor('door')).toContain('var(--surface-elevated)')
    expect(getNodeBorderColor('door')).toContain('var(--text)')
  })
})

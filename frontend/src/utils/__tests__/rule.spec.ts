import { describe, it, expect } from 'vitest'
import {
  assertRuleHasTrigger,
  duplicateRuleReasonKey,
  getNodeCenter,
  getLinkPoints,
  getSelfLoopPath,
  ruleSimilarityReasonKey,
  updateRulesForNodeRename
} from '../rule'

describe('rule utils', () => {
  it('getNodeCenter should compute center correctly', () => {
    const node = { position: { x: 10, y: 20 }, width: 100, height: 50 }
    const center = getNodeCenter(node as any)
    expect(center.x).toBe(10 + 100 / 2)
    expect(center.y).toBe(20 + 50 / 2)
  })

  it('getLinkPoints should produce endpoints between two nodes', () => {
    const from = { position: { x: 0, y: 0 }, width: 100, height: 50 }
    const to = { position: { x: 300, y: 100 }, width: 100, height: 50 }
    const { fromPoint, toPoint } = getLinkPoints(from as any, to as any)
    // fromPoint should be on boundary of from node and toPoint on boundary of to node
    expect(fromPoint.x).toBeGreaterThanOrEqual(from.position.x)
    expect(fromPoint.x).toBeLessThanOrEqual(from.position.x + from.width)
    expect(toPoint.x).toBeGreaterThanOrEqual(to.position.x)
    expect(toPoint.x).toBeLessThanOrEqual(to.position.x + to.width)
  })

  it('getSelfLoopPath should return a valid path string', () => {
    const node = { position: { x: 50, y: 50 }, width: 90, height: 60 }
    const path = getSelfLoopPath(node as any)
    expect(typeof path).toBe('string')
    expect(path.startsWith('M')).toBe(true)
    expect(path.includes('C')).toBe(true)
  })

  it('updateRulesForNodeRename updates labels and returns true when changed', () => {
    const rules: any[] = [
      { id: 'e1', from: 'n1', to: 'n2', fromLabel: 'old', toLabel: 't' },
      { id: 'e2', from: 'n3', to: 'n1', fromLabel: 'f', toLabel: 'old' }
    ]
    const changed = updateRulesForNodeRename(rules as any, 'n1', 'newLabel')
    expect(changed).toBe(true)
    expect(rules[0].fromLabel).toBe('newLabel')
    expect(rules[1].toLabel).toBe('newLabel')
  })

  it('allows full-state triggers without a UI attribute but still requires a value', () => {
    expect(() => assertRuleHasTrigger({
      sources: [
        { fromId: 'door-1', fromApi: '', itemType: 'state', relation: '=', value: 'closed;locked' }
      ],
      toId: 'alarm-1',
      toApi: 'siren'
    })).not.toThrow()

    expect(() => assertRuleHasTrigger({
      sources: [
        { fromId: 'door-1', fromApi: '', itemType: 'state', relation: '=', value: '   ' }
      ],
      toId: 'alarm-1',
      toApi: 'siren'
    })).toThrow('state trigger requires relation and value')
  })

  it('uses a one-based display position instead of exposing a persisted rule id', () => {
    expect(() => assertRuleHasTrigger({
      id: '4821',
      sources: [],
      toId: 'alarm-1',
      toApi: 'siren'
    }, 2)).toThrow('Rule 3: at least one trigger source is required')
  })

  it('maps deterministic and AI similarity reasons without displaying backend prose', () => {
    expect(duplicateRuleReasonKey('SAME_TRIGGER_SHAPE_DIFFERENT_VALUES'))
      .toBe('app.ruleCheckSameShape')
    expect(ruleSimilarityReasonKey('AI_HIGH_SCORE_REVIEW'))
      .toBe('app.ruleSimilarityHighScoreReview')
  })
})



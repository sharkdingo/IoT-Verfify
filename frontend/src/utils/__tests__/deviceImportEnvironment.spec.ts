import { describe, expect, it } from 'vitest'
import { mergeSourcedEnvironmentPatches } from '../deviceImportEnvironment'

describe('device-list shared environment patches', () => {
  it('merges complementary and identical declarations without changing their meaning', () => {
    expect(mergeSourcedEnvironmentPatches([
      { source: '#1', patches: [{ name: 'temperature', value: '21', trust: 'trusted' }] },
      { source: '#2', patches: [{ name: 'temperature', value: '21', privacy: 'private' }] }
    ])).toEqual({
      merged: [{ name: 'temperature', value: '21', trust: 'trusted', privacy: 'private' }],
      conflicts: []
    })
  })

  it('reports the exact rows and field instead of silently applying the later value', () => {
    const result = mergeSourcedEnvironmentPatches([
      { source: '#1', patches: [{ name: 'temperature', value: '21', trust: 'trusted' }] },
      { source: '#2', patches: [{ name: 'temperature', value: '26', trust: 'untrusted' }] }
    ])

    expect(result.merged).toEqual([{ name: 'temperature', value: '21', trust: 'trusted' }])
    expect(result.conflicts).toEqual([
      { name: 'temperature', field: 'value', firstSource: '#1', secondSource: '#2' },
      { name: 'temperature', field: 'trust', firstSource: '#1', secondSource: '#2' }
    ])
  })
})

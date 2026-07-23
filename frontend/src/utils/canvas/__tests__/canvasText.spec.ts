import { describe, expect, it } from 'vitest'
import { estimateCanvasTextWidth, truncateCanvasTextToWidth } from '@/utils/canvas/canvasText'

describe('canvasText', () => {
  it('budgets CJK and other wide glyphs more conservatively than narrow Latin text', () => {
    expect(estimateCanvasTextWidth('设备')).toBeGreaterThan(estimateCanvasTextWidth('ab'))
    expect(estimateCanvasTextWidth('WW')).toBeGreaterThan(estimateCanvasTextWidth('ii'))
  })

  it('truncates translated edge labels within the SVG background content budget', () => {
    const label = '客厅运动传感器.工作状态 = 已检测 -> 门口摄像头.拍照'.repeat(3)
    const rendered = truncateCanvasTextToWidth(label, 222)

    expect(rendered.endsWith('…')).toBe(true)
    expect(estimateCanvasTextWidth(rendered)).toBeLessThanOrEqual(222)
  })

  it('keeps short labels unchanged', () => {
    expect(truncateCanvasTextToWidth('Light.off -> Camera.on', 222))
      .toBe('Light.off -> Camera.on')
  })
})

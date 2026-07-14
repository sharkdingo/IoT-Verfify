import { describe, expect, it } from 'vitest'
import { deviceLabelKey, getUniqueLabel, reserveUniqueDeviceLabel } from '../nodeCreate'
import type { DeviceNode } from '@/types/node'

const node = (label: string): DeviceNode => ({
  id: `device_${label}`,
  templateName: 'Light',
  label,
  position: { x: 0, y: 0 },
  state: 'off',
  width: 176,
  height: 128
})

describe('device instance display-name allocation', () => {
  it('treats case and surrounding whitespace as the same user-facing name', () => {
    expect(deviceLabelKey('  Hall Light ')).toBe('hall light')
    expect(getUniqueLabel('hall light', [node('Hall Light')])).toBe('hall light_1')
  })

  it('reserves each previewed batch name using the same normalized key', () => {
    const reserved = new Set(['lamp'])

    expect(reserveUniqueDeviceLabel('Lamp', reserved)).toBe('Lamp_1')
    expect(reserveUniqueDeviceLabel('lamp', reserved)).toBe('lamp_2')
  })
})

// src/assets/config/specTemplates.ts
import type { SpecTemplate } from '../../types/board'

export const defaultSpecTemplates: SpecTemplate[] = [
    { id: '1', label: 'A holds forever' },
    { id: '2', label: 'A will happen later' },
    { id: '3', label: 'A never happens' },
    { id: '4', label: 'IF A happens, B should happen at the same time' },
    { id: '5', label: 'IF A happens, B should happen later' },
    { id: '6', label: 'IF A happens, B should happen later and last forever' },
    { id: '7', label: 'A will not happen because of something untrusted' }
]

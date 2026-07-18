export type AttackScenarioMode = 'NONE' | 'EXACT_POINTS' | 'ANY_UP_TO_BUDGET'

export type AttackPoint =
  | { kind: 'DEVICE'; deviceId: string; ruleId?: never }
  | { kind: 'AUTOMATION_LINK'; ruleId: number; deviceId?: never }

export type SelectedAttackPoint = AttackPoint & { displayLabel?: string | null }

export interface AttackScenario {
  mode: AttackScenarioMode
  budget?: number
  points?: AttackPoint[]
}

export const noAttackScenario = (): AttackScenario => ({
  mode: 'NONE',
  budget: 0,
  points: []
})

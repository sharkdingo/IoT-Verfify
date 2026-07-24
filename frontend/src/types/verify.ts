// src/types/verify.ts

import type { ModelDevice, ModelEnvironmentVariable, ModelRule, ModelSpecification } from './model'
import type { ModelRunSnapshot, ModelSemantics } from './modelSemantics'
import type { Specification } from './spec'
import type { AsyncTaskStatus, TaskProgressStage } from './task'
import type { RunPersistence } from './runPersistence'
import type { AttackScenario } from './attackScenario'
import type { ModelTokenSource } from './modelToken'

export interface VerificationRequest {
  devices: ModelDevice[];
  environmentVariables: ModelEnvironmentVariable[];
  rules: ModelRule[];
  specs: ModelSpecification[];
  attackScenario: AttackScenario;
  enablePrivacy: boolean;
}

export interface SpecResult {
  specId: string;
  templateId: string;
  specificationLabel: string;
  formulaPreview: string;
  formulaKind: 'CTL' | 'LTL';
  outcome: VerificationOutcome;
  expression: string;
}

export type VerificationOutcome = 'SATISFIED' | 'VIOLATED' | 'INCONCLUSIVE';

export type ModelGenerationIssueReasonCode =
  | 'RULE_NO_TRIGGER_CONDITIONS'
  | 'RULE_NULL_TRIGGER_CONDITION'
  | 'RULE_UNRESOLVABLE_TRIGGER_CONDITION'
  | 'RULE_NO_RESOLVABLE_TRIGGER_CONDITIONS'
  | 'RULE_PROPERTY_PROPAGATION_UNAVAILABLE'
  | 'SPEC_NO_CHECKABLE_CONDITIONS'
  | 'SPEC_PRIVACY_MODELING_DISABLED'
  | 'SPEC_UNSUPPORTED_RELATION'
  | 'SPEC_AMBIGUOUS_STATE'
  | 'SPEC_UNDECLARED_SECURITY_PROPERTY'
  | 'SPEC_UNKNOWN_DEVICE'
  | 'SPEC_TEMPLATE_SHAPE_MISMATCH'
  | 'SPEC_INVALID_VALUE'
  | 'SPEC_UNSUPPORTED_CONDITION'
  | 'UNCLASSIFIED_GENERATION_ISSUE';

export interface ModelGenerationIssue {
  issueType: 'RULE_DISABLED' | 'SPECIFICATION_SKIPPED' | string;
  itemLabel: string;
  reasonCode: ModelGenerationIssueReasonCode;
  reason: string;
}

export interface VerificationResult {
  isAttack: boolean;
  attackBudget: number;
  enablePrivacy: boolean;
  modelSemantics: ModelSemantics;
  modelSnapshot: ModelRunSnapshot;
  historyPersistence: RunPersistence;
  outcome: VerificationOutcome;
  modelComplete: boolean;
  traces: Trace[];
  specResults: SpecResult[];
  checkLogs: string[];
  nusmvOutput: string;
  disabledRuleCount: number;
  skippedSpecCount: number;
  generationIssues: ModelGenerationIssue[];
}

export interface TraceEvidence {
  violatedSpecId: string;
  violatedSpec?: Specification;
  checkedExpression: string;
  modelComplete: boolean;
  disabledRuleCount: number;
  skippedSpecCount: number;
  generationIssues: ModelGenerationIssue[];
  states: TraceState[];
  // Verification-context flags derived from the trace's stored request snapshot (backend TraceDto).
  isAttack?: boolean;
  attackBudget?: number;
  enablePrivacy?: boolean;
  modelSemantics?: ModelSemantics;
  modelSnapshot: ModelRunSnapshot;
  createdAt: string;
}

export interface ImmediateTrace extends TraceEvidence {
  id?: never;
  verificationTaskId?: never;
}

export interface PersistedTrace extends TraceEvidence {
  id: number;
  verificationTaskId: number;
}

export type Trace = ImmediateTrace | PersistedTrace;

export interface AvailableTraceSummary {
  id: number
  verificationTaskId: number
  violatedSpecId: string
  violatedSpec: Specification
  stateCount: number
  createdAt: string
  dataAvailable: true
}

export interface UnavailableTraceSummary {
  id: number
  verificationTaskId: number
  violatedSpecId?: string
  createdAt?: string
  dataAvailable: false
  unavailableReasonCode: 'PERSISTED_SEMANTIC_DATA_INVALID' | string
}

export type TraceSummary = AvailableTraceSummary | UnavailableTraceSummary

export interface TraceState {
  stateIndex: number;
  devices: TraceDevice[];
  triggeredRules: TraceTriggeredRule[]; // rule snapshots that drove the transition into this state
  compromisedAutomationLinks: TraceTriggeredRule[]; // rule delivery links selected as compromised
  trustPrivacies?: TraceTrustPrivacy[]; // state-level trust/privacy entries (backend List<TraceTrustPrivacyDto>)
  envVariables?: TraceVariable[];       // board environment variables using user-facing names (e.g. temperature)
  globalVariables?: TraceVariable[];    // NuSMV runtime/global variables, e.g. attack count
}

export interface TraceTriggeredRule {
  ruleIndex: number;
  ruleId?: string | null;
  ruleLabel?: string | null;
}

export interface TraceDevice {
  deviceId: string;
  deviceLabel: string;
  templateName: string;
  modelTokenSource: ModelTokenSource;
  state?: string;
  mode?: string;                       // 新增：状态机名称
  compromised?: boolean;
  variables: TraceVariable[];
  trustPrivacy?: TraceTrustPrivacy[];   // 改为可选
  privacies?: TraceTrustPrivacy[];      // 改为可选
}

export interface TraceVariable {
  name: string;
  value: string;
  trust?: string | null;    // 改为可选
  modelTokenSource: ModelTokenSource;
}

export interface TraceTrustPrivacy {
  name: string;
  propertyScope: 'state' | 'variable' | 'content';
  mode?: string | null;
  trust?: boolean | null;   // 后端 Boolean 包装类型，支持 true/false/null
  privacy?: string | null;
}

export interface VerificationTask {
  id: number;
  // userId 已删除 — 后端不返回，前端无使用处
  status: AsyncTaskStatus;
  createdAt: string;
  startedAt?: string;
  completedAt?: string;
  processingTimeMs?: number;
  progress?: number;       // 新增：0-100 进度
  progressStage?: TaskProgressStage;
  isAttack: boolean;
  attackBudget: number;
  enablePrivacy: boolean;
  modelSemantics: ModelSemantics;
  modelSnapshot: ModelRunSnapshot;
  outcome?: VerificationOutcome;
  modelComplete?: boolean;
  violatedSpecCount?: number;
  checkLogs?: string[];
  disabledRuleCount?: number;
  skippedSpecCount?: number;
  generationIssues?: ModelGenerationIssue[];
  specResults?: SpecResult[];
  nusmvOutput?: string;
  errorMessage?: string;
}

export type VerificationTaskSummary = Pick<
  VerificationTask,
  | 'id'
  | 'status'
  | 'createdAt'
  | 'startedAt'
  | 'completedAt'
  | 'processingTimeMs'
  | 'progress'
  | 'progressStage'
  | 'isAttack'
  | 'attackBudget'
  | 'enablePrivacy'
  | 'modelSemantics'
  | 'modelSnapshot'
  | 'outcome'
  | 'modelComplete'
  | 'violatedSpecCount'
  | 'disabledRuleCount'
  | 'skippedSpecCount'
  | 'generationIssues'
  | 'errorMessage'
>

export interface AvailableVerificationRunSummary {
  id: number
  createdAt: string
  startedAt: string
  completedAt: string
  processingTimeMs?: number
  isAttack: boolean
  attackBudget: number
  enablePrivacy: boolean
  modelSemantics: ModelSemantics
  modelSnapshot: ModelRunSnapshot
  outcome: VerificationOutcome
  modelComplete: boolean
  violatedSpecCount: number
  counterexampleCount: number
  disabledRuleCount: number
  skippedSpecCount: number
  generationIssues: ModelGenerationIssue[]
  counterexamples: TraceSummary[]
  dataAvailable: true
}

export interface UnavailableVerificationRunSummary {
  id: number
  createdAt?: string
  startedAt?: string
  completedAt?: string
  processingTimeMs?: number
  counterexampleCount: number
  counterexamples: TraceSummary[]
  dataAvailable: false
  unavailableReasonCode: 'PERSISTED_SEMANTIC_DATA_INVALID' | string
}

export type VerificationRunSummary = AvailableVerificationRunSummary | UnavailableVerificationRunSummary

export interface VerificationRun extends Omit<AvailableVerificationRunSummary, 'dataAvailable' | 'counterexamples'> {
  specResults: SpecResult[]
  checkLogs: string[]
  nusmvOutput: string
}

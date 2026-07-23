// src/api/board.ts - Board API（自动解包Result<T>）
import api from './http';

// 引入类型
import type { DeviceNode } from '../types/node'
import type { Specification } from '../types/spec'
import type { BoardLayoutDto } from '../types/canvas'
import type {
    DuplicateRuleReasonCode,
    RuleForm,
    RuleSimilarityReasonCode,
    RuleSourceItemType
} from '../types/rule'
import type { DeviceTemplate } from '@/types/device'
import type { ModelEnvironmentVariable } from '@/types/model'
import type { ModelTokenSource } from '@/types/modelToken'
import type { InteractiveOperationStatus, TaskCancellationResult } from '@/types/task'
import type { PortableSceneFile } from '@/types/scene'
import type {
    Trace,
    VerificationRequest,
    VerificationResult,
    VerificationRun,
    VerificationRunSummary,
    VerificationTask,
    VerificationTaskSummary
} from '@/types/verify'
import type {
    FaultLocalizationResult,
    FixApplyRequest,
    FixApplyResult,
    FixRequest,
    FixResult,
    FixSuggestion,
    FixStrategyName,
    PreferredRangeSelection
} from '@/types/fix'
import {
    validateFaultLocalizationResult,
    validateFixResult,
    validateFixSuggestion
} from '@/utils/fixResponse'
import { assertRuleHasTrigger } from '../utils/rule'
import { normalizeModelRelation } from '@/utils/modelRequest'
import {
    validateScenarioRecommendationResponse,
    validateStandaloneRecommendationResponse
} from '@/utils/recommendationResponse'
import {
    validateDeviceRecommendationCandidate,
    validateSpecificationRecommendationCandidate
} from '@/utils/recommendationMaterialization'
import {
    validateTaskCancellationResult,
    validateInteractiveOperationStatus,
    validateTaskProgress,
    validateVerificationTask,
    validateVerificationTaskSummaryList,
    validateVerificationRun,
    validateVerificationRunSummaryList,
    validateVerificationResult,
    validateVerificationTrace,
    validateVerificationTraceList
} from '@/utils/runResponse'

export interface RecommendationFilteredItem {
    type: string
    index: number
    reasonCode: string
    reason: string
    label?: string
}

export interface RecommendationAdjustmentItem {
    type: string
    index?: number
    reasonCode: string
    reason: string
    label?: string
    appliedValues: Record<string, unknown>
}

export interface DeviceRecommendation {
    templateName: string
    suggestedLabel: string
    /** Advisory recommendation context; not persisted as a device/model field. */
    intendedUse?: string
    /** Advisory recommendation context; not persisted as a device/model field. */
    suggestedPlacement?: string
    description?: string
    reason?: string
    initialState?: string
    currentStateTrust?: 'trusted' | 'untrusted'
    currentStatePrivacy?: 'public' | 'private'
    initialVariables?: Array<{
        name: string
        value: string
        trust?: 'trusted' | 'untrusted'
    }>
    initialPrivacies?: Array<{
        name: string
        privacy: 'public' | 'private'
    }>
}

interface RecommendationResponse<T = any> {
    message: string
    count: number
    requestedCount: number
    validatedCount: number
    filteredCount: number
    filteredItems: RecommendationFilteredItem[]
    adjustedCount?: number
    adjustedItems?: RecommendationAdjustmentItem[]
    rawCandidateCount: number
    inspectedCount: number
    truncatedCount: number
    recommendations: T[]
}

interface DeviceRecommendationResponse<T = any> extends RecommendationResponse<T> {
    adjustedCount: number
    adjustedItems: RecommendationAdjustmentItem[]
}

export interface ScenarioRecommendationResponse {
    message: string
    count: number
    requestedCount: number
    validatedCount: number
    filteredCount: number
    filteredItems: RecommendationFilteredItem[]
    adjustedCount: number
    adjustedItems: RecommendationAdjustmentItem[]
    rawCandidateCount: number
    inspectedCount: number
    truncatedCount: number
    scenarioName: string
    rationale: string
    objectiveStatus: 'COMPLETE' | 'PARTIAL'
    objectiveIssues: ScenarioObjectiveIssue[]
    verificationReady: boolean
    readinessIssues: ScenarioReadinessIssue[]
    semanticWarnings: ScenarioSemanticWarning[]
    scene: PortableSceneFile
}

export interface ScenarioObjectiveIssue {
    code: 'NO_DEVICES' | 'NO_AUTOMATION_RULES' | 'NO_SPECIFICATIONS'
    message: string
}

export interface ScenarioReadinessIssue {
    code: 'NO_DEVICES' | 'NO_SPECIFICATIONS'
    message: string
}

export interface ScenarioSemanticWarning {
    code: 'FILTERED_CANDIDATES' | 'NO_AUTOMATION_RULES' | 'UNREFERENCED_DEVICES'
    message: string
}

export interface SpecificationRecommendation {
    category?: string
    /** Advisory explanation; applying persists only templateId and structured conditions. */
    rationale: string
    templateId: string
    aConditions: Specification['aConditions']
    ifConditions: Specification['ifConditions']
    thenConditions: Specification['thenConditions']
}

// These synchronous operations are bounded by the server's NuSMV/LLM/fix deadlines.
// Do not let Axios' shorter CRUD timeout report a false failure while the server is still working.
const SERVER_BOUNDED_REQUEST = { timeout: 0 } as const

// 辅助函数：解包Result（后端返回 { code, message, data }）
const unpack = <T>(response: any): T => {
  return response.data.data;
};

const VALUE_BASED_RULE_SOURCE_TYPES = new Set<RuleSourceItemType>(['variable', 'mode', 'state'])

const normalizeRuleSourceType = (type?: string): RuleSourceItemType | undefined => {
    const normalized = String(type || '').trim().toLowerCase()
    return VALUE_BASED_RULE_SOURCE_TYPES.has(normalized as RuleSourceItemType) || normalized === 'api'
        ? normalized as RuleSourceItemType
        : undefined
}

const hasRuleConditionValue = (value: unknown) =>
    value !== null && value !== undefined && (typeof value !== 'string' || value.trim() !== '')

const requireRuleSourceType = (type?: RuleSourceItemType): RuleSourceItemType => {
    const normalized = normalizeRuleSourceType(type)
    if (!normalized) {
        throw new Error('Rule condition targetType is required')
    }
    return normalized
}

const requireValueBasedRuleSource = (source: any, sourceType: RuleSourceItemType) => {
    if (!source.relation || !hasRuleConditionValue(source.value)) {
        throw new Error(`Rule ${sourceType} condition requires relation and value`)
    }
    return {
        relation: normalizeModelRelation(source.relation) || String(source.relation),
        value: String(source.value)
    }
}

// 后端 RuleDto 接口（用于 API 通信）
interface BackendRuleDto {
    id: number | null
    conditions: Array<{
        deviceName: string
        attribute: string
        targetType: RuleSourceItemType
        relation?: string
        value?: string
    }>
    command: {
        deviceName: string
        action: string
        contentDevice: string | null
        content: string | null
    }
    ruleString: string
}

export interface BoardSemanticSnapshot {
    nodes: DeviceNode[]
    environmentVariables: ModelEnvironmentVariable[]
    rules: RuleForm[]
    specifications: Specification[]
    deviceTemplates: DeviceTemplate[]
}

const fromBackendRuleDto = (rule: BackendRuleDto): RuleForm => ({
    // Keep the persisted id as a numeric string for targeted delete and batch scene export/import.
    // Client-created rules use a temporary `rule_<timestamp>` id and are sent with id=null.
    id: rule.id != null ? String(rule.id) : '',
    name: rule.ruleString || '',
    sources: (rule.conditions && rule.conditions.length > 0)
        ? rule.conditions.map((c) => {
            const sourceType = requireRuleSourceType(c.targetType)
            const shouldKeepRelation = VALUE_BASED_RULE_SOURCE_TYPES.has(sourceType)
            return {
                fromId: c.deviceName || '',
                fromApi: sourceType === 'state' ? 'state' : (c.attribute || ''),
                itemType: sourceType,
                relation: shouldKeepRelation ? (normalizeModelRelation(c.relation) || '=') : undefined,
                value: shouldKeepRelation ? c.value : undefined
            }
        })
        : [],
    toId: rule.command?.deviceName || '',
    toApi: rule.command?.action || '',
    contentDevice: rule.command?.contentDevice || undefined,
    content: rule.command?.content || undefined
})

// RuleForm -> BackendRuleDto. Shared by targeted create, checks, and explicit scene batch replacement.
// Client-created rules use a `rule_<timestamp>` id -> send null; persisted rules retain their numeric id.
const toBackendRuleDto = (rule: RuleForm): BackendRuleDto => {
    let id: number | null = null;
    if (rule.id && rule.id.startsWith('rule_')) {
        id = null;
    } else if (rule.id) {
        const num = Number(rule.id);
        if (!isNaN(num)) {
            id = num;
        }
    }
    return {
        id,
        conditions: rule.sources.map(source => {
            const sourceType = requireRuleSourceType(source.itemType)
            const shouldSendRelation = VALUE_BASED_RULE_SOURCE_TYPES.has(sourceType)
            const valueCondition = shouldSendRelation
                ? requireValueBasedRuleSource(source, sourceType)
                : null
            return {
                deviceName: String(source.fromId || ''),
                attribute: sourceType === 'state' ? 'state' : String(source.fromApi || ''),
                targetType: sourceType,
                relation: valueCondition?.relation,
                value: valueCondition?.value
            }
        }),
        command: {
            deviceName: String(rule.toId || ''),
            action: String(rule.toApi || ''),
            contentDevice: rule.contentDevice || null,
            content: rule.content || null
        },
        ruleString: String(rule.name || '')
    };
};

// Only structured specification semantics cross the write boundary. The backend rebuilds
// labels, device summaries, and the user-facing formula preview from these fields.
const toBackendSpecificationWriteDto = (spec: Specification) => ({
    id: spec.id,
    templateId: spec.templateId,
    aConditions: (spec.aConditions || []).map(condition => ({
        deviceId: condition.deviceId,
        targetType: condition.targetType,
        key: condition.key,
        ...(condition.propertyScope ? { propertyScope: condition.propertyScope } : {}),
        relation: normalizeModelRelation(condition.relation) || condition.relation,
        value: condition.value
    })),
    ifConditions: (spec.ifConditions || []).map(condition => ({
        deviceId: condition.deviceId,
        targetType: condition.targetType,
        key: condition.key,
        ...(condition.propertyScope ? { propertyScope: condition.propertyScope } : {}),
        relation: normalizeModelRelation(condition.relation) || condition.relation,
        value: condition.value
    })),
    thenConditions: (spec.thenConditions || []).map(condition => ({
        deviceId: condition.deviceId,
        targetType: condition.targetType,
        key: condition.key,
        ...(condition.propertyScope ? { propertyScope: condition.propertyScope } : {}),
        relation: normalizeModelRelation(condition.relation) || condition.relation,
        value: condition.value
    }))
});

export interface CollectionMutationResult<T> {
    operation: 'created' | 'deleted';
    affectedItem: T;
    currentItems: T[];
    currentCount: number;
}

export interface DuplicateRuleCheckResult {
    isDuplicate: boolean;
    requiresReview: boolean;
    matchedRule?: string | null;
    similarity: number;
    matchType: string;
    reasonCode: DuplicateRuleReasonCode;
    reason: string;
    message: string;
}

export interface RuleSimilarityResult {
    isSimilar: boolean;
    isDuplicate: boolean;
    requiresReview: boolean;
    matchedRule?: string | null;
    similarity: number;
    reasonCode: RuleSimilarityReasonCode;
    reason: string;
    message: string;
}

const DUPLICATE_RULE_REASON_CODES = new Set<DuplicateRuleReasonCode>([
    'NO_EXISTING_RULES',
    'EXACT_MATCH',
    'TRIGGER_SET_CONTAINS_OTHER',
    'SAME_TRIGGER_SHAPE_DIFFERENT_VALUES',
    'PARTIAL_TRIGGER_OVERLAP',
    'NO_MATCHING_SIGNATURE'
])

const RULE_SIMILARITY_REASON_CODES = new Set<RuleSimilarityReasonCode>([
    'NO_EXISTING_RULES',
    'AI_DUPLICATE',
    'AI_SIMILAR',
    'AI_HIGH_SCORE_REVIEW',
    'AI_NO_SIGNIFICANT_SIMILARITY'
])

const MODEL_TOKEN_SOURCES = new Set<ModelTokenSource>(['BUNDLED', 'CUSTOM', 'UNKNOWN'])

export interface EnvironmentVariableChange {
    changeType: 'ADDED' | 'UPDATED' | 'REMOVED';
    name: string;
    previousValue?: ModelEnvironmentVariable | null;
    currentValue?: ModelEnvironmentVariable | null;
    previousModelTokenSource?: ModelTokenSource;
    currentModelTokenSource?: ModelTokenSource;
}

export type EnvironmentVariableField = 'value' | 'trust' | 'privacy';

export interface EnvironmentVariablePatchResult {
    name: string;
    suppliedFields: EnvironmentVariableField[];
    changedFields: EnvironmentVariableField[];
    preservedFields: EnvironmentVariableField[];
    previousValue: ModelEnvironmentVariable;
    currentValue: ModelEnvironmentVariable;
}

export interface EnvironmentMutationResult {
    operation: 'updated' | 'unchanged';
    patchResults: EnvironmentVariablePatchResult[];
    environmentVariables: ModelEnvironmentVariable[];
    environmentChanges: EnvironmentVariableChange[];
    currentCount: number;
}

export interface DeviceMutationResult {
    operation: 'created' | 'updated' | 'renamed';
    affectedDevices: DeviceNode[];
    currentNodes: DeviceNode[];
    environmentVariables: ModelEnvironmentVariable[];
    environmentChanges: EnvironmentVariableChange[];
    currentSpecifications: Specification[];
    previousLabel?: string;
    updatedSpecificationCount: number;
    currentCount: number;
}

export interface DeviceLayout {
    position: { x: number; y: number };
    width: number;
    height: number;
}

export interface DeviceRuntimeUpdate {
    state?: string;
    currentStateTrust?: string;
    currentStatePrivacy?: string;
    variables?: DeviceNode['variables'];
    privacies?: DeviceNode['privacies'];
}

export type DeviceUpdateField =
    | 'position.x' | 'position.y' | 'width' | 'height'
    | 'state' | 'currentStateTrust' | 'currentStatePrivacy' | 'variables' | 'privacies';

export interface DeviceUpdateResult {
    operation: 'updated' | 'unchanged';
    mutationType: 'layout' | 'runtime';
    changedFields: DeviceUpdateField[];
    previousDevice: DeviceNode;
    currentDevice: DeviceNode;
    currentNodes: DeviceNode[];
    currentCount: number;
}

export interface DeviceDeletionResult {
    operation: 'preview' | 'deleted';
    impactToken: string;
    deletedDevice: DeviceNode;
    removedRules: RuleForm[];
    removedSpecifications: Specification[];
    currentNodes: DeviceNode[];
    environmentVariables: ModelEnvironmentVariable[];
    environmentChanges: EnvironmentVariableChange[];
    currentRules: RuleForm[];
    currentSpecifications: Specification[];
}

export interface BoardReplacementPreview {
    impactToken: string;
    deviceCount: number;
    environmentVariableCount: number;
    ruleCount: number;
    specificationCount: number;
}

export interface BoardReplacementStaleData {
    reasonCode: 'BOARD_REPLACEMENT_STALE';
    currentPreview: BoardReplacementPreview;
}

export type DefaultTemplateResetChangeType =
    | 'RESTORE_MISSING'
    | 'REFRESH_DEFAULT'
    | 'REPLACE_CUSTOM_NAME_COLLISION'
    | 'REMOVE_OBSOLETE_DEFAULT'

export type DefaultTemplateResetBlockerReasonCode =
    | 'DEVICE_INSTANCE_INCOMPATIBLE'
    | 'AUTOMATION_RULE_INCOMPATIBLE'
    | 'SPECIFICATION_INCOMPATIBLE'
    | 'ENVIRONMENT_POOL_INCOMPATIBLE'
    | 'BOARD_MODEL_INCOMPATIBLE'

export interface DefaultTemplateResetResult {
    operation: 'preview' | 'reset';
    impactToken: string;
    canApply: boolean;
    templateChanges: Array<{
        templateName: string;
        changeType: DefaultTemplateResetChangeType;
        semanticsChanged: boolean;
    }>;
    affectedDevices: Array<{
        deviceId: string;
        deviceLabel: string;
        templateName: string;
    }>;
    blockers: Array<{
        itemLabel: string;
        reasonCode: DefaultTemplateResetBlockerReasonCode;
        reason: string;
    }>;
    environmentChanges: EnvironmentVariableChange[];
    currentTemplates: DeviceTemplate[];
    environmentVariables: ModelEnvironmentVariable[];
}

export interface DeviceTemplateDeletionResult {
    operation: 'preview' | 'deleted';
    impactToken: string;
    canDelete: boolean;
    template: DeviceTemplate;
    deletedTemplate?: DeviceTemplate;
    blockers: Array<{
        reasonCode: 'DEVICE_INSTANCE_USES_TEMPLATE' | string;
        itemId: string;
        itemLabel: string;
        reason: string;
    }>;
    currentTemplates: DeviceTemplate[];
}

export const BOARD_RESPONSE_INCOMPLETE_CODE = 'BOARD_RESPONSE_INCOMPLETE'

class BoardResponseContractError extends Error {
    readonly code = BOARD_RESPONSE_INCOMPLETE_CODE

    constructor(context: string, detail: string) {
        super(`${context} returned an incomplete authoritative result: ${detail}`)
        this.name = 'BoardResponseContractError'
    }
}

const requireResponseRecord = (value: unknown, context: string): Record<string, any> => {
    if (!value || typeof value !== 'object' || Array.isArray(value)) {
        throw new BoardResponseContractError(context, 'the result must be an object')
    }
    return value as Record<string, any>
}

const requireResponseArray = <T>(value: unknown, context: string, field?: string): T[] => {
    const candidate = field
        ? requireResponseRecord(value, context)[field]
        : value
    if (!Array.isArray(candidate)) {
        throw new BoardResponseContractError(context, `${field || 'result'} must be an array`)
    }
    return candidate as T[]
}

const requireOperation = (result: Record<string, any>, expected: string, context: string) => {
    if (result.operation !== expected) {
        throw new BoardResponseContractError(context, `operation must be '${expected}'`)
    }
}

const requireCurrentCount = (
    result: Record<string, any>,
    currentItems: unknown[],
    context: string
) => {
    if (!Number.isSafeInteger(result.currentCount) || result.currentCount !== currentItems.length) {
        throw new BoardResponseContractError(context, 'currentCount must match the authoritative collection')
    }
}

const requireCheckBoolean = (
    result: Record<string, any>,
    field: string,
    context: string
): boolean => {
    if (typeof result[field] !== 'boolean') {
        throw new BoardResponseContractError(context, `${field} must be boolean`)
    }
    return result[field]
}

const requireCheckText = (
    result: Record<string, any>,
    field: string,
    context: string
): string => {
    if (typeof result[field] !== 'string' || !result[field].trim()) {
        throw new BoardResponseContractError(context, `${field} must be non-blank text`)
    }
    return result[field]
}

const requireCheckSimilarity = (result: Record<string, any>, context: string): number => {
    if (typeof result.similarity !== 'number'
        || !Number.isFinite(result.similarity)
        || result.similarity < 0
        || result.similarity > 1) {
        throw new BoardResponseContractError(context, 'similarity must be a number from 0 to 1')
    }
    return result.similarity
}

const requireOptionalCheckText = (
    result: Record<string, any>,
    field: string,
    context: string
): string | null | undefined => {
    const value = result[field]
    if (value === null || value === undefined) return value
    if (typeof value !== 'string') {
        throw new BoardResponseContractError(context, `${field} must be text or null`)
    }
    return value
}

const validateDuplicateRuleCheckResult = (value: unknown): DuplicateRuleCheckResult => {
    const context = 'Duplicate-rule check'
    const result = requireResponseRecord(value, context)
    requireCheckBoolean(result, 'isDuplicate', context)
    requireCheckBoolean(result, 'requiresReview', context)
    requireOptionalCheckText(result, 'matchedRule', context)
    requireCheckSimilarity(result, context)
    requireCheckText(result, 'matchType', context)
    const reasonCode = requireCheckText(result, 'reasonCode', context)
    if (!DUPLICATE_RULE_REASON_CODES.has(reasonCode as DuplicateRuleReasonCode)) {
        throw new BoardResponseContractError(context, 'reasonCode is invalid')
    }
    requireCheckText(result, 'reason', context)
    requireCheckText(result, 'message', context)
    return result as DuplicateRuleCheckResult
}

const validateRuleSimilarityResult = (value: unknown): RuleSimilarityResult => {
    const context = 'AI rule-similarity check'
    const result = requireResponseRecord(value, context)
    const isSimilar = requireCheckBoolean(result, 'isSimilar', context)
    const isDuplicate = requireCheckBoolean(result, 'isDuplicate', context)
    const requiresReview = requireCheckBoolean(result, 'requiresReview', context)
    if (isDuplicate && !isSimilar) {
        throw new BoardResponseContractError(context, 'a duplicate result must also be similar')
    }
    requireOptionalCheckText(result, 'matchedRule', context)
    const similarity = requireCheckSimilarity(result, context)
    if (requiresReview !== (isDuplicate || isSimilar || similarity >= 0.8)) {
        throw new BoardResponseContractError(context, 'requiresReview contradicts the similarity result')
    }
    const reasonCode = requireCheckText(result, 'reasonCode', context)
    if (!RULE_SIMILARITY_REASON_CODES.has(reasonCode as RuleSimilarityReasonCode)) {
        throw new BoardResponseContractError(context, 'reasonCode is invalid')
    }
    const expectedReasonCode: RuleSimilarityReasonCode = isDuplicate
        ? 'AI_DUPLICATE'
        : isSimilar
          ? 'AI_SIMILAR'
          : similarity >= 0.8
            ? 'AI_HIGH_SCORE_REVIEW'
            : 'AI_NO_SIGNIFICANT_SIMILARITY'
    if (reasonCode !== expectedReasonCode
        && !(reasonCode === 'NO_EXISTING_RULES' && !isSimilar && !isDuplicate && similarity === 0)) {
        throw new BoardResponseContractError(context, 'reasonCode contradicts the similarity result')
    }
    requireCheckText(result, 'reason', context)
    requireCheckText(result, 'message', context)
    return result as RuleSimilarityResult
}

const validateDeviceMutationResult = (
    value: unknown,
    expectedOperation: DeviceMutationResult['operation'],
    expectedDeviceIds: string[],
    context: string
): DeviceMutationResult => {
    const result = requireResponseRecord(value, context)
    requireOperation(result, expectedOperation, context)
    const affectedDevices = requireResponseArray<DeviceNode>(result, context, 'affectedDevices')
    const currentNodes = requireResponseArray<DeviceNode>(result, context, 'currentNodes')
    requireResponseArray<ModelEnvironmentVariable>(result, context, 'environmentVariables')
    requireResponseArray<EnvironmentVariableChange>(result, context, 'environmentChanges')
    requireResponseArray<Specification>(result, context, 'currentSpecifications')
    requireCurrentCount(result, currentNodes, context)

    const affectedIds = affectedDevices.map(device => String(device?.id || ''))
    if (affectedDevices.length !== expectedDeviceIds.length
        || expectedDeviceIds.some(id => !affectedIds.includes(id))) {
        throw new BoardResponseContractError(context, 'affectedDevices does not match the requested device set')
    }
    const currentIds = new Set(currentNodes.map(device => String(device?.id || '')))
    if (affectedIds.some(id => !id || !currentIds.has(id))) {
        throw new BoardResponseContractError(context, 'an affected device is absent from currentNodes')
    }
    return result as DeviceMutationResult
}

const validateDeviceRenameResult = (
    value: unknown,
    nodeId: string,
    label: string,
    expectedLabel: string
): DeviceMutationResult => {
    const context = 'Device rename'
    const result = validateDeviceMutationResult(value, 'renamed', [nodeId], context)
    const affected = result.affectedDevices.find(device => device.id === nodeId)
    const authoritative = result.currentNodes.find(device => device.id === nodeId)
    if (affected?.label !== label || authoritative?.label !== label) {
        throw new BoardResponseContractError(
            context,
            'affectedDevices and currentNodes must contain the requested label'
        )
    }
    if (result.previousLabel !== expectedLabel) {
        throw new BoardResponseContractError(context, 'previousLabel must match expectedLabel')
    }
    if (!Number.isSafeInteger(result.updatedSpecificationCount)
        || result.updatedSpecificationCount < 0) {
        throw new BoardResponseContractError(
            context,
            'updatedSpecificationCount must be a non-negative integer'
        )
    }
    return result
}

const DEVICE_LAYOUT_FIELDS: DeviceUpdateField[] = ['position.x', 'position.y', 'width', 'height']
const DEVICE_RUNTIME_FIELDS: DeviceUpdateField[] = [
    'state', 'currentStateTrust', 'currentStatePrivacy', 'variables', 'privacies'
]

const normalizedDeviceRuntimeCollection = (
    field: 'variables' | 'privacies',
    value: DeviceNode[typeof field]
): string => {
    const normalized = field === 'variables'
        ? ((value as DeviceNode['variables']) ?? []).map(item => ({
            name: item.name ?? null,
            value: item.value ?? null,
            trust: item.trust ?? null
        }))
        : ((value as DeviceNode['privacies']) ?? []).map(item => ({
            name: item.name ?? null,
            privacy: item.privacy ?? null
        }))
    normalized.sort((left, right) => String(left.name).localeCompare(String(right.name)))
    return JSON.stringify(normalized)
}

const deviceUpdateFieldValue = (device: DeviceNode, field: DeviceUpdateField): unknown => {
    if (field === 'position.x') return device.position?.x ?? null
    if (field === 'position.y') return device.position?.y ?? null
    if (field === 'variables' || field === 'privacies') {
        return normalizedDeviceRuntimeCollection(field, device[field])
    }
    return device[field] ?? null
}

const sameDeviceSnapshot = (left: DeviceNode, right: DeviceNode) =>
    left.id === right.id
    && left.templateName === right.templateName
    && left.label === right.label
    && deviceUpdateFieldValue(left, 'position.x') === deviceUpdateFieldValue(right, 'position.x')
    && deviceUpdateFieldValue(left, 'position.y') === deviceUpdateFieldValue(right, 'position.y')
    && left.width === right.width
    && left.height === right.height
    && deviceUpdateFieldValue(left, 'state') === deviceUpdateFieldValue(right, 'state')
    && deviceUpdateFieldValue(left, 'currentStateTrust') === deviceUpdateFieldValue(right, 'currentStateTrust')
    && deviceUpdateFieldValue(left, 'currentStatePrivacy') === deviceUpdateFieldValue(right, 'currentStatePrivacy')
    && deviceUpdateFieldValue(left, 'variables') === deviceUpdateFieldValue(right, 'variables')
    && deviceUpdateFieldValue(left, 'privacies') === deviceUpdateFieldValue(right, 'privacies')

const validateDeviceUpdateResult = (
    value: unknown,
    mutationType: DeviceUpdateResult['mutationType'],
    nodeId: string,
    requested: DeviceLayout | DeviceRuntimeUpdate
): DeviceUpdateResult => {
    const context = mutationType === 'layout' ? 'Device layout update' : 'Device runtime update'
    const result = requireResponseRecord(value, context)
    if (result.operation !== 'updated' && result.operation !== 'unchanged') {
        throw new BoardResponseContractError(context, "operation must be 'updated' or 'unchanged'")
    }
    if (result.mutationType !== mutationType) {
        throw new BoardResponseContractError(context, `mutationType must be '${mutationType}'`)
    }
    if (!result.previousDevice || !result.currentDevice
        || result.previousDevice.id !== nodeId || result.currentDevice.id !== nodeId) {
        throw new BoardResponseContractError(context, 'previousDevice/currentDevice must match the requested device')
    }
    const currentNodes = requireResponseArray<DeviceNode>(result, context, 'currentNodes')
    requireCurrentCount(result, currentNodes, context)
    const authoritative = currentNodes.find(device => device.id === nodeId)
    if (!authoritative || !sameDeviceSnapshot(authoritative, result.currentDevice)) {
        throw new BoardResponseContractError(context, 'currentDevice must match currentNodes')
    }

    const allowedFields = mutationType === 'layout' ? DEVICE_LAYOUT_FIELDS : DEVICE_RUNTIME_FIELDS
    if (!Array.isArray(result.changedFields)
        || result.changedFields.some((field: unknown) => !allowedFields.includes(field as DeviceUpdateField))
        || new Set(result.changedFields).size !== result.changedFields.length) {
        throw new BoardResponseContractError(context, 'changedFields contains an unsupported or duplicate field')
    }
    const actualChanged = allowedFields.filter(field => deviceUpdateFieldValue(
        result.previousDevice,
        field
    ) !== deviceUpdateFieldValue(result.currentDevice, field))
    if (actualChanged.length !== result.changedFields.length
        || actualChanged.some(field => !result.changedFields.includes(field))) {
        throw new BoardResponseContractError(context, 'changedFields must agree with previous/current devices')
    }
    if ((result.operation === 'unchanged') !== (result.changedFields.length === 0)) {
        throw new BoardResponseContractError(context, 'operation must agree with changedFields')
    }

    const preservedFields = mutationType === 'layout'
        ? DEVICE_RUNTIME_FIELDS
        : DEVICE_LAYOUT_FIELDS
    if (preservedFields.some(field => deviceUpdateFieldValue(
        result.previousDevice,
        field
    ) !== deviceUpdateFieldValue(result.currentDevice, field))
        || result.previousDevice.id !== result.currentDevice.id
        || result.previousDevice.templateName !== result.currentDevice.templateName
        || result.previousDevice.label !== result.currentDevice.label) {
        throw new BoardResponseContractError(context, 'the targeted patch changed a preserved device field')
    }

    if (mutationType === 'layout') {
        const layout = requested as DeviceLayout
        if (result.currentDevice.position?.x !== layout.position.x
            || result.currentDevice.position?.y !== layout.position.y
            || result.currentDevice.width !== layout.width
            || result.currentDevice.height !== layout.height) {
            throw new BoardResponseContractError(context, 'currentDevice does not contain the requested layout')
        }
    } else {
        const runtime = requested as DeviceRuntimeUpdate
        for (const field of ['currentStateTrust', 'currentStatePrivacy'] as const) {
            if ((result.currentDevice[field] ?? null) !== (runtime[field] ?? null)) {
                throw new BoardResponseContractError(context, `currentDevice does not contain requested ${field}`)
            }
        }
        if (runtime.state !== undefined && result.currentDevice.state !== runtime.state) {
            throw new BoardResponseContractError(context, 'currentDevice does not contain the requested state')
        }
        for (const field of ['variables', 'privacies'] as const) {
            if (normalizedDeviceRuntimeCollection(field, result.currentDevice[field])
                !== normalizedDeviceRuntimeCollection(field, runtime[field])) {
                throw new BoardResponseContractError(context, `currentDevice does not contain requested ${field}`)
            }
        }
    }
    return result as DeviceUpdateResult
}

const ENVIRONMENT_FIELDS: EnvironmentVariableField[] = ['value', 'trust', 'privacy']

const requireEnvironmentFieldArray = (
    value: unknown,
    field: string,
    context: string
): EnvironmentVariableField[] => {
    if (!Array.isArray(value)
        || value.some(candidate => !ENVIRONMENT_FIELDS.includes(candidate as EnvironmentVariableField))
        || new Set(value).size !== value.length) {
        throw new BoardResponseContractError(
            context,
            `${field} must contain unique value/trust/privacy field names`
        )
    }
    return value as EnvironmentVariableField[]
}

const environmentFieldValue = (
    variable: ModelEnvironmentVariable,
    field: EnvironmentVariableField
) => variable[field] ?? null

const validateEnvironmentMutationResult = (
    value: unknown,
    patches: ModelEnvironmentVariable[]
): EnvironmentMutationResult => {
    const context = 'Environment Pool update'
    const result = requireResponseRecord(value, context)
    if (result.operation !== 'updated' && result.operation !== 'unchanged') {
        throw new BoardResponseContractError(context, "operation must be 'updated' or 'unchanged'")
    }
    const patchResults = requireResponseArray<EnvironmentVariablePatchResult>(
        result,
        context,
        'patchResults'
    )
    const environmentVariables = requireResponseArray<ModelEnvironmentVariable>(
        result,
        context,
        'environmentVariables'
    )
    const environmentChanges = requireResponseArray<EnvironmentVariableChange>(
        result,
        context,
        'environmentChanges'
    )
    requireCurrentCount(result, environmentVariables, context)
    if ((result.operation === 'unchanged') !== (environmentChanges.length === 0)) {
        throw new BoardResponseContractError(context, 'operation must agree with environmentChanges')
    }
    if (patchResults.length !== patches.length) {
        throw new BoardResponseContractError(context, 'patchResults must explain every submitted patch')
    }

    const currentByName = new Map(environmentVariables.map(variable => [variable.name, variable]))
    const resultByName = new Map<string, EnvironmentVariablePatchResult>()
    for (const raw of patchResults) {
        const patchResult = requireResponseRecord(raw, context) as unknown as EnvironmentVariablePatchResult
        if (typeof patchResult.name !== 'string' || !patchResult.name.trim()
            || resultByName.has(patchResult.name)) {
            throw new BoardResponseContractError(context, 'patchResults must have unique non-blank names')
        }
        const suppliedFields = requireEnvironmentFieldArray(
            patchResult.suppliedFields,
            `patchResults.${patchResult.name}.suppliedFields`,
            context
        )
        const changedFields = requireEnvironmentFieldArray(
            patchResult.changedFields,
            `patchResults.${patchResult.name}.changedFields`,
            context
        )
        const preservedFields = requireEnvironmentFieldArray(
            patchResult.preservedFields,
            `patchResults.${patchResult.name}.preservedFields`,
            context
        )
        if (!patchResult.previousValue || !patchResult.currentValue
            || patchResult.previousValue.name !== patchResult.name
            || patchResult.currentValue.name !== patchResult.name) {
            throw new BoardResponseContractError(context, 'each patch result needs matching previous/current values')
        }
        if (changedFields.some(field => !suppliedFields.includes(field))) {
            throw new BoardResponseContractError(context, 'changedFields must be a subset of suppliedFields')
        }
        const expectedPreserved = ENVIRONMENT_FIELDS.filter(field => !suppliedFields.includes(field))
        if (preservedFields.length !== expectedPreserved.length
            || expectedPreserved.some(field => !preservedFields.includes(field))) {
            throw new BoardResponseContractError(context, 'preservedFields must explain every omitted field')
        }
        if (preservedFields.some(field => environmentFieldValue(
            patchResult.previousValue,
            field
        ) !== environmentFieldValue(patchResult.currentValue, field))) {
            throw new BoardResponseContractError(context, 'a preserved field changed value')
        }
        const actualChanged = suppliedFields.filter(field => environmentFieldValue(
            patchResult.previousValue,
            field
        ) !== environmentFieldValue(patchResult.currentValue, field))
        if (actualChanged.length !== changedFields.length
            || actualChanged.some(field => !changedFields.includes(field))) {
            throw new BoardResponseContractError(context, 'changedFields must agree with previous/current values')
        }
        const authoritative = currentByName.get(patchResult.name)
        if (!authoritative || ENVIRONMENT_FIELDS.some(field =>
            environmentFieldValue(authoritative, field)
            !== environmentFieldValue(patchResult.currentValue, field))) {
            throw new BoardResponseContractError(context, 'currentValue must match environmentVariables')
        }
        resultByName.set(patchResult.name, patchResult)
    }

    for (const patch of patches) {
        const patchResult = resultByName.get(patch.name)
        if (!patchResult) {
            throw new BoardResponseContractError(context, `no patch result was returned for ${patch.name}`)
        }
        const expectedSupplied = ENVIRONMENT_FIELDS.filter(field => patch[field] !== null && patch[field] !== undefined)
        if (patchResult.suppliedFields.length !== expectedSupplied.length
            || expectedSupplied.some(field => !patchResult.suppliedFields.includes(field))) {
            throw new BoardResponseContractError(context, `suppliedFields does not match the patch for ${patch.name}`)
        }
    }
    return result as EnvironmentMutationResult
}

const validateDeviceDeletionResult = (
    value: unknown,
    expectedOperation: DeviceDeletionResult['operation'],
    context: string
): Record<string, any> => {
    const result = requireResponseRecord(value, context)
    requireOperation(result, expectedOperation, context)
    if (typeof result.impactToken !== 'string' || !result.impactToken.trim()) {
        throw new BoardResponseContractError(context, 'impactToken is required')
    }
    if (!result.deletedDevice || typeof result.deletedDevice !== 'object' || Array.isArray(result.deletedDevice)) {
        throw new BoardResponseContractError(context, 'deletedDevice is required')
    }
    for (const field of [
        'removedRules',
        'removedSpecifications',
        'currentNodes',
        'environmentVariables',
        'environmentChanges',
        'currentRules',
        'currentSpecifications'
    ]) {
        requireResponseArray(result, context, field)
    }
    return result
}

const validateCollectionMutationResult = <T>(
    value: unknown,
    expectedOperation: CollectionMutationResult<T>['operation'],
    context: string
): CollectionMutationResult<T> => {
    const result = requireResponseRecord(value, context)
    requireOperation(result, expectedOperation, context)
    if (!result.affectedItem || typeof result.affectedItem !== 'object' || Array.isArray(result.affectedItem)) {
        throw new BoardResponseContractError(context, 'affectedItem is required')
    }
    const currentItems = requireResponseArray<T>(result, context, 'currentItems')
    requireCurrentCount(result, currentItems, context)
    return result as CollectionMutationResult<T>
}

const validateBoardBatchResult = (value: unknown) => {
    const context = 'Scene replacement'
    const result = requireResponseRecord(value, context)
    requireResponseArray<DeviceNode>(result, context, 'nodes')
    requireResponseArray<ModelEnvironmentVariable>(result, context, 'environmentVariables')
    requireResponseArray<BackendRuleDto>(result, context, 'rules')
    requireResponseArray<Specification>(result, context, 'specs')
    requireResponseArray<DeviceTemplate>(result, context, 'createdTemplates')
    return result as {
        nodes: DeviceNode[]
        environmentVariables: ModelEnvironmentVariable[]
        rules: BackendRuleDto[]
        specs: Specification[]
        createdTemplates: DeviceTemplate[]
    }
}

const validateBoardReplacementPreview = (value: unknown): BoardReplacementPreview => {
    const context = 'Scene replacement preview'
    const result = requireResponseRecord(value, context)
    if (typeof result.impactToken !== 'string' || !result.impactToken.trim()) {
        throw new BoardResponseContractError(context, 'impactToken is required')
    }
    for (const field of [
        'deviceCount',
        'environmentVariableCount',
        'ruleCount',
        'specificationCount'
    ]) {
        if (!Number.isSafeInteger(result[field]) || result[field] < 0) {
            throw new BoardResponseContractError(context, `${field} must be a non-negative integer`)
        }
    }
    return result as BoardReplacementPreview
}

const validateDeviceTemplateResult = (value: unknown, context: string): DeviceTemplate => {
    const result = requireResponseRecord(value, context)
    if (typeof result.name !== 'string' || !result.name.trim()) {
        throw new BoardResponseContractError(context, 'template name is required')
    }
    if (!result.manifest || typeof result.manifest !== 'object' || Array.isArray(result.manifest)) {
        throw new BoardResponseContractError(context, 'template manifest is required')
    }
    return result as DeviceTemplate
}

const validateDeviceTemplateDeletionResult = (
    value: unknown,
    expectedOperation: DeviceTemplateDeletionResult['operation']
): DeviceTemplateDeletionResult => {
    const context = expectedOperation === 'preview'
        ? 'Device type deletion preview'
        : 'Device type deletion'
    const result = requireResponseRecord(value, context)
    requireOperation(result, expectedOperation, context)
    if (typeof result.impactToken !== 'string' || !result.impactToken.trim()) {
        throw new BoardResponseContractError(context, 'impactToken is required')
    }
    if (typeof result.canDelete !== 'boolean') {
        throw new BoardResponseContractError(context, 'canDelete must be boolean')
    }
    const template = validateDeviceTemplateResult(result.template, `${context} template`)
    const blockers = requireResponseArray<any>(result, context, 'blockers')
    blockers.forEach((blocker, index) => {
        const row = requireResponseRecord(blocker, `${context} blockers[${index}]`)
        for (const field of ['reasonCode', 'itemId', 'itemLabel', 'reason']) {
            if (typeof row[field] !== 'string' || !row[field].trim()) {
                throw new BoardResponseContractError(context, `blockers[${index}].${field} is required`)
            }
        }
    })
    if (result.canDelete !== (blockers.length === 0)) {
        throw new BoardResponseContractError(context, 'canDelete must match blockers')
    }
    const currentTemplates = requireResponseArray<DeviceTemplate>(result, context, 'currentTemplates')
    currentTemplates.forEach((item, index) =>
        validateDeviceTemplateResult(item, `${context} currentTemplates[${index}]`))
    if (expectedOperation === 'deleted') {
        const deleted = validateDeviceTemplateResult(result.deletedTemplate, `${context} deletedTemplate`)
        if (deleted.id !== template.id || currentTemplates.some(item => item.id === deleted.id)) {
            throw new BoardResponseContractError(context, 'deletedTemplate contradicts currentTemplates')
        }
    }
    return result as DeviceTemplateDeletionResult
}

const validateEnvironmentVariable = (value: unknown, context: string): ModelEnvironmentVariable => {
    const result = requireResponseRecord(value, context)
    for (const field of ['name', 'value', 'trust', 'privacy']) {
        if (typeof result[field] !== 'string' || !result[field].trim()) {
            throw new BoardResponseContractError(context, `${field} is required`)
        }
    }
    return result as ModelEnvironmentVariable
}

const validateDefaultTemplateResetResult = (
    value: unknown,
    expectedOperation: DefaultTemplateResetResult['operation']
): DefaultTemplateResetResult => {
    const context = expectedOperation === 'preview'
        ? 'Default device type reset preview'
        : 'Default device type reset'
    const result = requireResponseRecord(value, context)
    requireOperation(result, expectedOperation, context)
    if (typeof result.impactToken !== 'string' || !result.impactToken.trim()) {
        throw new BoardResponseContractError(context, 'impactToken is required')
    }
    if (typeof result.canApply !== 'boolean') {
        throw new BoardResponseContractError(context, 'canApply must be boolean')
    }
    const templateChanges = requireResponseArray<any>(result, context, 'templateChanges')
    const affectedDevices = requireResponseArray<any>(result, context, 'affectedDevices')
    const blockers = requireResponseArray<any>(result, context, 'blockers')
    const environmentChanges = requireResponseArray<EnvironmentVariableChange>(result, context, 'environmentChanges')
    const currentTemplates = requireResponseArray<DeviceTemplate>(result, context, 'currentTemplates')
    const environmentVariables = requireResponseArray<ModelEnvironmentVariable>(result, context, 'environmentVariables')
    if (templateChanges.length === 0) {
        throw new BoardResponseContractError(context, 'templateChanges must describe the bundled defaults')
    }

    const allowedChangeTypes = new Set<DefaultTemplateResetChangeType>([
        'RESTORE_MISSING',
        'REFRESH_DEFAULT',
        'REPLACE_CUSTOM_NAME_COLLISION',
        'REMOVE_OBSOLETE_DEFAULT'
    ])
    const changedNames = new Set<string>()
    templateChanges.forEach((change, index) => {
        const row = requireResponseRecord(change, context)
        if (typeof row.templateName !== 'string' || !row.templateName.trim()) {
            throw new BoardResponseContractError(context, `templateChanges[${index}].templateName is required`)
        }
        const key = row.templateName.trim().toLocaleLowerCase()
        if (changedNames.has(key)) {
            throw new BoardResponseContractError(context, 'templateChanges contains duplicate names')
        }
        changedNames.add(key)
        if (!allowedChangeTypes.has(row.changeType)) {
            throw new BoardResponseContractError(context, `templateChanges[${index}].changeType is invalid`)
        }
        if (typeof row.semanticsChanged !== 'boolean') {
            throw new BoardResponseContractError(context, `templateChanges[${index}].semanticsChanged must be boolean`)
        }
    })
    affectedDevices.forEach((device, index) => {
        const row = requireResponseRecord(device, context)
        for (const field of ['deviceId', 'deviceLabel', 'templateName']) {
            if (typeof row[field] !== 'string' || !row[field].trim()) {
                throw new BoardResponseContractError(context, `affectedDevices[${index}].${field} is required`)
            }
        }
    })
    blockers.forEach((blocker, index) => {
        const row = requireResponseRecord(blocker, context)
        for (const field of ['itemLabel', 'reasonCode', 'reason']) {
            if (typeof row[field] !== 'string' || !row[field].trim()) {
                throw new BoardResponseContractError(context, `blockers[${index}].${field} is required`)
            }
        }
        if (![
            'DEVICE_INSTANCE_INCOMPATIBLE',
            'AUTOMATION_RULE_INCOMPATIBLE',
            'SPECIFICATION_INCOMPATIBLE',
            'ENVIRONMENT_POOL_INCOMPATIBLE',
            'BOARD_MODEL_INCOMPATIBLE'
        ].includes(row.reasonCode)) {
            throw new BoardResponseContractError(context, `blockers[${index}].reasonCode is invalid`)
        }
    })
    if (result.canApply !== (blockers.length === 0)) {
        throw new BoardResponseContractError(context, 'canApply must match blockers')
    }
    currentTemplates.forEach((template, index) =>
        validateDeviceTemplateResult(template, `${context} currentTemplates[${index}]`))
    environmentVariables.forEach((variable, index) =>
        validateEnvironmentVariable(variable, `${context} environmentVariables[${index}]`))

    const environmentByName = new Map(environmentVariables.map(variable => [variable.name, variable]))
    environmentChanges.forEach((change, index) => {
        const row = requireResponseRecord(change, context)
        if (!['ADDED', 'UPDATED', 'REMOVED'].includes(row.changeType)) {
            throw new BoardResponseContractError(context, `environmentChanges[${index}].changeType is invalid`)
        }
        if (typeof row.name !== 'string' || !row.name.trim()) {
            throw new BoardResponseContractError(context, `environmentChanges[${index}].name is required`)
        }
        for (const field of ['previousModelTokenSource', 'currentModelTokenSource'] as const) {
            if (row[field] !== undefined && !MODEL_TOKEN_SOURCES.has(row[field])) {
                throw new BoardResponseContractError(
                    context,
                    `environmentChanges[${index}].${field} is invalid`
                )
            }
        }
        if (expectedOperation === 'reset') {
            const current = environmentByName.get(row.name)
            if (row.changeType === 'REMOVED' ? current !== undefined : current === undefined) {
                throw new BoardResponseContractError(context, 'environmentChanges contradicts environmentVariables')
            }
        }
    })

    if (expectedOperation === 'reset') {
        if (!result.canApply || blockers.length !== 0) {
            throw new BoardResponseContractError(context, 'a committed reset cannot contain blockers')
        }
        const finalNames = new Set(currentTemplates.map(template => template.name.trim().toLocaleLowerCase()))
        for (const change of templateChanges) {
            const key = change.templateName.trim().toLocaleLowerCase()
            const shouldExist = change.changeType !== 'REMOVE_OBSOLETE_DEFAULT'
            if (finalNames.has(key) !== shouldExist) {
                throw new BoardResponseContractError(context, 'templateChanges contradicts currentTemplates')
            }
        }
    }
    return result as DefaultTemplateResetResult
}

const validateFixApplyResult = (
    value: unknown,
    expectedStrategy: FixStrategyName
): Omit<FixApplyResult, 'rules'> & { rules: BackendRuleDto[] } => {
    const context = 'Automatic fix apply'
    const result = requireResponseRecord(value, context)
    if (result.applied !== true
        || (result.verificationRechecked !== true && result.verificationEvidenceReused !== true)) {
        throw new BoardResponseContractError(
            context,
            'the response must confirm either fresh verification or reused verification evidence'
        )
    }
    if (result.strategy !== expectedStrategy) {
        throw new BoardResponseContractError(context, 'strategy does not match the requested strategy')
    }
    const appliedSuggestion = validateFixSuggestion(
        result.appliedSuggestion,
        context,
        expectedStrategy
    )
    if (!appliedSuggestion.verified) {
        throw new BoardResponseContractError(context, 'appliedSuggestion must identify the verified fix actually written')
    }
    const rules = requireResponseArray<BackendRuleDto>(result, context, 'rules')
    if (!Number.isSafeInteger(result.previousRuleCount) || result.previousRuleCount < 0
        || !Number.isSafeInteger(result.currentRuleCount)
        || result.currentRuleCount !== rules.length) {
        throw new BoardResponseContractError(context, 'rule counts must match the authoritative rules snapshot')
    }
    if ((expectedStrategy === 'remove' && result.currentRuleCount >= result.previousRuleCount)
        || (expectedStrategy !== 'remove' && result.currentRuleCount !== result.previousRuleCount)) {
        throw new BoardResponseContractError(context, 'rule counts contradict the applied strategy')
    }
    if (typeof result.message !== 'string' || !result.message.trim()) {
        throw new BoardResponseContractError(context, 'message is required')
    }
    return result as Omit<FixApplyResult, 'rules'> & { rules: BackendRuleDto[] }
}

export default {
    // ==== 节点 ====
    getSnapshot: async (): Promise<BoardSemanticSnapshot> => {
        const context = 'Board semantic snapshot'
        const snapshot = requireResponseRecord(
            unpack<unknown>(await api.get('/board/snapshot')),
            context
        )
        const rawRules = requireResponseArray<BackendRuleDto>(snapshot.rules, `${context}.rules`)
        return {
            nodes: requireResponseArray<DeviceNode>(snapshot.nodes, `${context}.nodes`),
            environmentVariables: requireResponseArray<ModelEnvironmentVariable>(
                snapshot.environmentVariables,
                `${context}.environmentVariables`
            ),
            rules: rawRules.map(fromBackendRuleDto),
            specifications: requireResponseArray<Specification>(
                snapshot.specifications,
                `${context}.specifications`
            ),
            deviceTemplates: requireResponseArray<DeviceTemplate>(
                snapshot.deviceTemplates,
                `${context}.deviceTemplates`
            ).map((template, index) =>
                validateDeviceTemplateResult(template, `${context}.deviceTemplates[${index}]`))
        }
    },
    getNodes: async (): Promise<DeviceNode[]> => {
        return requireResponseArray<DeviceNode>(
            unpack<unknown>(await api.get('/board/nodes')),
            'Device list'
        );
    },
    addNodes: async (
        devices: DeviceNode[],
        environmentVariablePatches: ModelEnvironmentVariable[] = []
    ): Promise<DeviceMutationResult> => {
        const result = unpack<unknown>(await api.post('/board/nodes', {
            devices,
            environmentVariablePatches
        }));
        return validateDeviceMutationResult(
            result,
            'created',
            devices.map(device => device.id),
            'Device creation'
        )
    },
    updateNodeLayout: async (nodeId: string, layout: DeviceLayout): Promise<DeviceUpdateResult> => {
        return validateDeviceUpdateResult(
            unpack<unknown>(await api.put(
                `/board/nodes/${encodeURIComponent(nodeId)}/layout`,
                layout
            )),
            'layout',
            nodeId,
            layout
        )
    },
    updateNodeRuntime: async (nodeId: string, runtime: DeviceRuntimeUpdate): Promise<DeviceUpdateResult> => {
        return validateDeviceUpdateResult(
            unpack<unknown>(await api.put(
                `/board/nodes/${encodeURIComponent(nodeId)}/runtime`,
                runtime
            )),
            'runtime',
            nodeId,
            runtime
        )
    },
    renameNode: async (
        nodeId: string,
        label: string,
        expectedLabel: string
    ): Promise<DeviceMutationResult> => {
        const result = unpack<unknown>(
            await api.patch(`/board/nodes/${encodeURIComponent(nodeId)}/label`, {
                label,
                expectedLabel
            })
        );
        return validateDeviceRenameResult(result, nodeId, label, expectedLabel)
    },
    previewNodeDeletion: async (nodeId: string): Promise<DeviceDeletionResult> => {
        const result = validateDeviceDeletionResult(
            unpack<unknown>(await api.get(`/board/nodes/${encodeURIComponent(nodeId)}/deletion-preview`)),
            'preview',
            'Device deletion preview'
        ) as Omit<DeviceDeletionResult, 'removedRules' | 'currentRules'> & {
            removedRules: BackendRuleDto[];
            currentRules: BackendRuleDto[];
        };
        return {
            ...result,
            removedRules: result.removedRules.map(fromBackendRuleDto),
            currentRules: result.currentRules.map(fromBackendRuleDto)
        };
    },
    deleteNode: async (
        nodeId: string,
        impactToken: string
    ): Promise<DeviceDeletionResult> => {
        const result = validateDeviceDeletionResult(
            unpack<unknown>(await api.post(`/board/nodes/${encodeURIComponent(nodeId)}/delete`, {
                impactToken
            })),
            'deleted',
            'Device deletion'
        ) as Omit<DeviceDeletionResult, 'removedRules' | 'currentRules'> & {
            removedRules: BackendRuleDto[];
            currentRules: BackendRuleDto[];
        };
        return {
            ...result,
            removedRules: result.removedRules.map(fromBackendRuleDto),
            currentRules: result.currentRules.map(fromBackendRuleDto)
        };
    },

    // ==== 环境变量池 ====
    getEnvironment: async (): Promise<ModelEnvironmentVariable[]> => {
        return requireResponseArray<ModelEnvironmentVariable>(
            unpack<unknown>(await api.get('/board/environment')),
            'Environment Pool'
        );
    },
    saveEnvironment: async (variables: ModelEnvironmentVariable[]): Promise<EnvironmentMutationResult> => {
        return validateEnvironmentMutationResult(
            unpack<unknown>(await api.post('/board/environment', variables)),
            variables
        );
    },

    // ==== 规约 ====
    getSpecs: async (): Promise<Specification[]> => {
        return requireResponseArray<Specification>(unpack<unknown>(await api.get('/board/specs')), 'Specification list');
    },
    addSpec: async (spec: Specification): Promise<CollectionMutationResult<Specification>> => {
        return validateCollectionMutationResult<Specification>(
            unpack<unknown>(await api.post('/board/specs', toBackendSpecificationWriteDto(spec))),
            'created',
            'Specification creation'
        );
    },
    removeSpec: async (specId: string): Promise<CollectionMutationResult<Specification>> => {
        return validateCollectionMutationResult<Specification>(
            unpack<unknown>(await api.delete(`/board/specs/${encodeURIComponent(specId)}`)),
            'deleted',
            'Specification deletion'
        );
    },

    // ==== 规则（sources -> target） ====
    getRules: async (): Promise<RuleForm[]> => {
        const data = requireResponseArray<BackendRuleDto>(
            unpack<unknown>(await api.get('/board/rules')),
            'Rule list'
        );
        return data.map(fromBackendRuleDto);
    },
    addRule: async (rule: RuleForm): Promise<CollectionMutationResult<RuleForm>> => {
        assertRuleHasTrigger(rule)

        const result = validateCollectionMutationResult<BackendRuleDto>(
            unpack<unknown>(await api.post('/board/rules', toBackendRuleDto(rule))),
            'created',
            'Rule creation'
        );
        return {
            ...result,
            affectedItem: fromBackendRuleDto(result.affectedItem),
            currentItems: result.currentItems.map(fromBackendRuleDto)
        };
    },
    reorderRules: async (ruleIds: string[]): Promise<RuleForm[]> => {
        const persistedIds = ruleIds.map(ruleId => {
            const numericId = Number(ruleId)
            if (!Number.isSafeInteger(numericId) || numericId <= 0) {
                throw new Error('Every rule must have a persisted id before execution order can be changed')
            }
            return numericId
        })
        const result = requireResponseArray<BackendRuleDto>(
            unpack<unknown>(await api.put('/board/rules/order', { ruleIds: persistedIds })),
            'Rule reorder'
        )
        return result.map(fromBackendRuleDto)
    },
    removeRule: async (ruleId: string): Promise<CollectionMutationResult<RuleForm>> => {
        const numericId = Number(ruleId);
        if (!Number.isSafeInteger(numericId) || numericId <= 0) {
            throw new Error('Persisted rule id is required for deletion');
        }
        const result = validateCollectionMutationResult<BackendRuleDto>(
            unpack<unknown>(await api.delete(`/board/rules/${numericId}`)),
            'deleted',
            'Rule deletion'
        );
        return {
            ...result,
            affectedItem: fromBackendRuleDto(result.affectedItem),
            currentItems: result.currentItems.map(fromBackendRuleDto)
        };
    },

    /** Returns the authoritative current-board impact that the user must confirm. */
    previewBoardReplacement: async (): Promise<BoardReplacementPreview> => {
        return validateBoardReplacementPreview(
            unpack<unknown>(await api.get('/board/replacement-preview'))
        )
    },

    /**
     * Explicit atomic replacement of all four board semantic collections. The impact token must
     * come from the preview shown to the user; omitted collections are never interpreted as patches.
     */
    saveBoardBatch: async (batch: {
        impactToken: string,
        nodes: DeviceNode[],
        environmentVariables: ModelEnvironmentVariable[],
        rules: RuleForm[],
        specs: Specification[],
        templateSnapshots: DeviceTemplate[]
    }): Promise<{
        nodes: DeviceNode[],
        environmentVariables: ModelEnvironmentVariable[],
        rules: RuleForm[],
        specs: Specification[],
        createdTemplates: DeviceTemplate[]
    }> => {
        if (!batch.impactToken.trim()) {
            throw new Error('Scene replacement requires a confirmed impact token')
        }
        // A scene replacement is rejected as a whole if any rule has no trigger source.
        batch.rules.forEach((rule, index) => assertRuleHasTrigger(rule, index));
        const payload = {
            impactToken: batch.impactToken,
            nodes: batch.nodes,
            environmentVariables: batch.environmentVariables,
            rules: batch.rules.map(toBackendRuleDto),
            specs: batch.specs.map(toBackendSpecificationWriteDto),
            templateSnapshots: batch.templateSnapshots
        };
        const saved = validateBoardBatchResult(
            unpack<unknown>(await api.post('/board/batch', payload))
        );
        return {
            ...saved,
            rules: saved.rules.map(fromBackendRuleDto)
        };
    },

    /**
     * Deterministic duplicate check used before saving a rule.
     */
    checkDuplicateRule: async (rule: RuleForm, signal?: AbortSignal): Promise<DuplicateRuleCheckResult> => {
        assertRuleHasTrigger(rule)

        const dto = toBackendRuleDto(rule);

        const response = await api.post<any>('/board/rules/check-duplicate', dto, { signal });
        return validateDuplicateRuleCheckResult(unpack<unknown>(response));
    },

    /**
     * Explicit AI semantic similarity check. This may call the configured external LLM.
     */
    checkRuleSimilarity: async (rule: RuleForm, signal?: AbortSignal): Promise<RuleSimilarityResult> => {
        assertRuleHasTrigger(rule)

        const dto = toBackendRuleDto(rule);

        const response = await api.post<any>('/board/rules/check-similarity', dto, { signal });
        return validateRuleSimilarityResult(unpack<unknown>(response));
    },

    // ==== 布局（包含面板状态、Canvas 缩放位移） ====
    getLayout: async (): Promise<BoardLayoutDto> => {
        return unpack<BoardLayoutDto>(await api.get('/board/layout'));
    },
    saveLayout: async (dto: BoardLayoutDto): Promise<BoardLayoutDto> => {
        return unpack<BoardLayoutDto>(await api.post('/board/layout', dto));
    },

    // ==== 设备模板 ====
    getDeviceTemplates: async (): Promise<DeviceTemplate[]> => {
        const templates = requireResponseArray<DeviceTemplate>(
            unpack<unknown>(await api.get('/board/templates')),
            'Device type catalog'
        );
        return templates.map((template, index) =>
            validateDeviceTemplateResult(template, `Device type catalog[${index}]`));
    },
    getDeviceTemplateSchema: async (): Promise<Record<string, unknown>> => {
        return unpack<Record<string, unknown>>(await api.get('/board/templates/schema'));
    },
    addDeviceTemplate: async (tpl: DeviceTemplate): Promise<DeviceTemplate> => {
        return validateDeviceTemplateResult(
            unpack<unknown>(await api.post('/board/templates', tpl)),
            'Device type import'
        );
    },
    previewDefaultTemplateReset: async (): Promise<DefaultTemplateResetResult> => {
        return validateDefaultTemplateResetResult(
            unpack<unknown>(await api.get('/board/templates/defaults/reset-preview')),
            'preview'
        );
    },
    resetDefaultTemplates: async (impactToken: string): Promise<DefaultTemplateResetResult> => {
        return validateDefaultTemplateResetResult(
            unpack<unknown>(await api.post('/board/templates/defaults/reset', { impactToken })),
            'reset'
        );
    },
    previewDeviceTemplateDeletion: async (id: number): Promise<DeviceTemplateDeletionResult> => {
        return validateDeviceTemplateDeletionResult(
            unpack<unknown>(await api.get(`/board/templates/${id}/deletion-preview`)),
            'preview'
        );
    },
    deleteDeviceTemplate: async (id: number, impactToken: string): Promise<DeviceTemplateDeletionResult> => {
        return validateDeviceTemplateDeletionResult(
            unpack<unknown>(await api.post(`/board/templates/${id}/delete`, { impactToken })),
            'deleted'
        );
    },

    // ==== 验证 ====
    verify: async (req: VerificationRequest): Promise<VerificationResult> => {
        return validateVerificationResult(
            unpack<unknown>(await api.post('/verify', req, SERVER_BOUNDED_REQUEST))
        );
    },
    getTask: async (taskId: number): Promise<VerificationTask> => {
        return validateVerificationTask(
            unpack<unknown>(await api.get(`/verify/tasks/${taskId}`))
        );
    },
    getTasks: async (excludeTaskIds: number[] = []): Promise<VerificationTaskSummary[]> => {
        const params = excludeTaskIds.length > 0
            ? { excludeTaskIds: excludeTaskIds.join(',') }
            : undefined;
        return validateVerificationTaskSummaryList(
            unpack<unknown>(await api.get('/verify/tasks', { params }))
        );
    },
    deleteTask: async (taskId: number): Promise<void> => {
        return unpack<void>(await api.delete(`/verify/tasks/${taskId}`));
    },
    getVerificationRuns: async (): Promise<VerificationRunSummary[]> => {
        return validateVerificationRunSummaryList(
            unpack<unknown>(await api.get('/verify/runs'))
        );
    },
    getVerificationRun: async (runId: number): Promise<VerificationRun> => {
        return validateVerificationRun(
            unpack<unknown>(await api.get(`/verify/runs/${runId}`))
        );
    },
    getVerificationRunTraces: async (runId: number): Promise<Trace[]> => {
        return validateVerificationTraceList(
            unpack<unknown>(await api.get(`/verify/runs/${runId}/traces`))
        );
    },
    deleteVerificationRun: async (runId: number): Promise<void> => {
        return unpack<void>(await api.delete(`/verify/runs/${runId}`));
    },
    getTaskProgress: async (taskId: number): Promise<number> => {
        return validateTaskProgress(
            unpack<unknown>(await api.get(`/verify/tasks/${taskId}/progress`)),
            'Verification task progress'
        );
    },
    cancelTask: async (taskId: number): Promise<TaskCancellationResult> => {
        return validateTaskCancellationResult(
            unpack<unknown>(await api.post(`/verify/tasks/${taskId}/cancel`)),
            taskId,
            'Verification task cancellation'
        );
    },

    // ==== 验证 Trace（反例） ====
    // 获取用户所有验证 Trace
    getVerificationTraces: async (): Promise<Trace[]> => {
        return validateVerificationTraceList(
            unpack<unknown>(await api.get('/verify/traces'))
        );
    },
    // 获取某个验证任务产生的反例 Trace（按 task 维度过滤，避免拿到旧任务/并发任务的反例）
    getTaskTraces: async (taskId: number): Promise<Trace[]> => {
        return validateVerificationTraceList(
            unpack<unknown>(await api.get(`/verify/tasks/${taskId}/traces`))
        );
    },
    // 获取单个 Trace
    getVerificationTrace: async (id: number): Promise<Trace> => {
        return validateVerificationTrace(
            unpack<unknown>(await api.get(`/verify/traces/${id}`))
        );
    },
    // 删除 Trace
    deleteVerificationTrace: async (id: number): Promise<void> => {
        return unpack<void>(await api.delete(`/verify/traces/${id}`));
    },

    // ==== 异步验证 ====
    // 发起异步验证并接收服务端真实任务快照
    verifyAsync: async (req: VerificationRequest): Promise<VerificationTask> => {
        return validateVerificationTask(
            unpack<unknown>(await api.post('/verify/async', req))
        );
    },

    // ==== 设备推荐 ====
    recommendRelatedDevices: async (
        maxRecommendations: number = 5,
        language: string = 'en',
        userRequirement: string = '',
        requestId: string = crypto.randomUUID(),
        signal?: AbortSignal
    ): Promise<DeviceRecommendationResponse<DeviceRecommendation>> => {
        return validateStandaloneRecommendationResponse<DeviceRecommendationResponse<DeviceRecommendation>>(
            unpack<unknown>(await api.post(`/board/devices/recommend?requestId=${encodeURIComponent(requestId)}`, {
                maxRecommendations,
                language,
                userRequirement
            }, { signal, ...SERVER_BOUNDED_REQUEST })),
            'Device recommendation',
            validateDeviceRecommendationCandidate,
            true
        );
    },

    // ==== 规约推荐 ====
    recommendSpecifications: async (
        maxRecommendations: number = 5,
        category: string = 'all',
        language: string = 'en',
        userRequirement: string = '',
        requestId: string = crypto.randomUUID(),
        signal?: AbortSignal
    ): Promise<RecommendationResponse<SpecificationRecommendation>> => {
        return validateStandaloneRecommendationResponse<RecommendationResponse<SpecificationRecommendation>>(
            unpack<unknown>(await api.post('/board/specs/recommend', {
                maxRecommendations, category, language, userRequirement, requestId
            }, {
                signal,
                ...SERVER_BOUNDED_REQUEST
            })),
            'Specification recommendation',
            validateSpecificationRecommendationCandidate
        );
    },

    // ==== 可导入、未验证的场景草案推荐 ====
    recommendScenario: async (
        request: {
            maxDevices?: number,
            maxRules?: number,
            maxSpecs?: number,
            language?: string,
            userRequirement?: string
        },
        requestId: string = crypto.randomUUID(),
        signal?: AbortSignal
    ): Promise<ScenarioRecommendationResponse> => {
        return validateScenarioRecommendationResponse<ScenarioRecommendationResponse>(
            unpack<unknown>(await api.post(
                `/board/scenario/recommend?requestId=${encodeURIComponent(requestId)}`,
                request,
                { signal, ...SERVER_BOUNDED_REQUEST }
            )),
            'Scenario recommendation'
        );
    },

    cancelRecommendation: async (requestId: string): Promise<boolean> => {
        return unpack<boolean>(await api.delete(
            `/board/recommendations/${encodeURIComponent(requestId)}`
        ));
    },

    getRecommendationStatus: async (requestId: string): Promise<InteractiveOperationStatus> => {
        return validateInteractiveOperationStatus(unpack<unknown>(await api.get(
            `/board/recommendations/${encodeURIComponent(requestId)}`
        )));
    },

    // ==== 故障定位与修复 ====
    /**
     * 获取 Trace 的故障规则定位
     */
    getFaultRules: async (traceId: number): Promise<FaultLocalizationResult> => {
        return validateFaultLocalizationResult(
            unpack<unknown>(await api.get(`/verify/traces/${traceId}/fault-rules`)),
            traceId
        );
    },

    /**
     * 获取 Trace 的修复建议
     */
    fixTrace: async (
        traceId: number,
        request?: FixRequest,
        options: { requestId?: string; signal?: AbortSignal } = {}
    ): Promise<FixResult> => {
        const requestId = options.requestId || crypto.randomUUID()
        return validateFixResult(
            unpack<unknown>(await api.post(
                `/verify/traces/${traceId}/fix`,
                request || {},
                { ...SERVER_BOUNDED_REQUEST, params: { requestId }, signal: options.signal }
            )),
            traceId,
            request?.strategies || []
        );
    },

    cancelFixRequest: async (requestId: string): Promise<boolean> => {
        return unpack<boolean>(await api.delete(
            `/verify/fix-requests/${encodeURIComponent(requestId)}`
        ));
    },

    getFixRequestStatus: async (requestId: string): Promise<InteractiveOperationStatus> => {
        return validateInteractiveOperationStatus(unpack<unknown>(await api.get(
            `/verify/fix-requests/${encodeURIComponent(requestId)}`
        )));
    },

    /** Apply the exact signed suggestion the user reviewed after server-side drift checks. */
    applyFix: async (traceId: number, suggestion: FixSuggestion,
                     preferredRangeSelections?: PreferredRangeSelection[]): Promise<FixApplyResult> => {
        if (!suggestion.suggestionToken) {
            throw new BoardResponseContractError('Automatic fix apply', 'suggestionToken is required')
        }
        const payload: FixApplyRequest = {
            strategy: suggestion.strategy,
            suggestion,
            suggestionToken: suggestion.suggestionToken,
            preferredRangeSelections
        };
        const result = validateFixApplyResult(
            unpack<unknown>(await api.post(
                `/verify/traces/${traceId}/fix/apply`, payload, SERVER_BOUNDED_REQUEST
            )),
            suggestion.strategy
        )
        return {
            ...result,
            rules: result.rules.map(fromBackendRuleDto)
        };
    }
}

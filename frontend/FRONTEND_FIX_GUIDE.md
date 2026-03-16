# 前端修改指南

本文档列出当前前端代码与后端 API 契约之间的所有已知问题，按严重度排序。

> 后端 API 端点参考：`backend/CLAUDE.md` → "API Endpoints" 章节

---

## 阻断（`vue-tsc` 编译失败，CI 无法通过）

### F-01 `board.ts:260` — `manifest.Variables` 字段不存在

`DeviceManifest` 类型中的字段名是 `InternalVariables`，不是 `Variables`。
此外 `apis` 和 `workingStates` 虽然字段名正确，但传的是 PascalCase 原始对象，
后端 `RecommendRelatedDevicesTool` 用 camelCase 小写键读取，**三个字段全部数据丢失**。

**文件**: `src/api/board.ts` 第 257-263 行

**现状**:
```typescript
templates: templates.map(t => ({
    name: t.manifest.Name,
    description: t.manifest.Description,
    variables: t.manifest.Variables || [],        // TS 报错 + 字段不存在
    apis: t.manifest.APIs || [],                  // PascalCase，后端读不到
    workingStates: t.manifest.WorkingStates || [] // PascalCase，后端读不到
}))
```

**修改为**:
```typescript
templates: templates.map(t => ({
    name: t.manifest.Name,
    description: t.manifest.Description,
    variables: (t.manifest.InternalVariables || []).map(v => v.Name),
    apis: (t.manifest.APIs || []).map(a => ({ name: a.Name, description: a.Description || '' })),
    workingStates: (t.manifest.WorkingStates || []).map(s => s.Name)
}))
```

---

### F-02 `ChatView.vue:165` — 未使用变量 `toggleChat`

**文件**: `src/components/ChatView.vue` 第 165-167 行

**修改**: 删除以下 3 行：
```typescript
const toggleChat = () => {
  chatStore.toggleChat();
};
```

---

## 高（运行时 404 / 400）

### F-03 `ControlCenter.vue:796` — 导入模板端点不存在 + 请求体格式错误

> **前置依赖**: 先完成 **F-05**（`DeviceTemplate.id` 改为可选），否则下方示例中
> 不带 `id` 的对象无法赋值给 `DeviceTemplate` 类型。

两个问题叠加：
1. `POST /api/device-templates/import` 后端无此端点，**必定 404**
2. 导出功能（第 939 行）写出的是**裸 manifest**，而后端 `POST /api/board/templates`
   要求 `DeviceTemplateDto`（`{ name: string, manifest: object }`），直接发裸 manifest
   会因 `name` 为空触发 **400 校验失败**

**文件**: `src/components/ControlCenter.vue` 第 786-814 行

**修改**: 将整段 `handleImportTemplate` 改为通过 `boardApi` 调用，并包装请求体：
```typescript
const handleImportTemplate = async (event: Event) => {
  const target = event.target as HTMLInputElement
  const file = target.files?.[0]
  if (!file) return
  try {
    const text = await file.text()
    const manifest = JSON.parse(text)
    // 后端要求 { name, manifest } 包装；id 由数据库生成，不传
    await boardApi.addDeviceTemplate({
      name: manifest.Name,
      manifest: manifest
    })
    ElMessage.success('Template imported successfully')
    emit('refresh-templates')
  } catch (error: any) {
    ElMessage.error(error?.message || 'Invalid JSON file')
  }
  // 重置 file input，确保选择同一文件时仍能触发 change 事件
  target.value = ''
}
```

---

## 中（类型漂移 / 字段缺失）

### F-04 `types/verify.ts` — `VerificationRequest` 缺少 `enablePrivacy`

后端 `VerificationRequestDto` 有此字段（默认 `false`）。不加不崩但类型不完整。

**文件**: `src/types/verify.ts` 第 3-9 行

**修改为**:
```typescript
export interface VerificationRequest {
  devices: any[];
  rules: any[];
  specs: any[];
  isAttack: boolean;
  intensity: number;
  enablePrivacy: boolean;
}
```

---

### F-05 `types/device.ts:60` — `DeviceTemplate.id` 类型和可选性

后端 `DeviceTemplateDto.id` 是 `Long`（JSON 数字），且创建时 id 由数据库生成，不应必填。

**文件**: `src/types/device.ts` 第 59-63 行

**修改为**:
```typescript
export interface DeviceTemplate {
    id?: number      // 后端 Long；创建时无 id，响应中才有
    name: string
    manifest: DeviceManifest
}
```

---

### F-06 Task 类型：删除幽灵 `userId`，补 `progress`

后端 `VerificationTaskDto` 和 `SimulationTaskDto` 均**不返回 `userId`**，
但有 `progress: Integer`（0-100），前端类型中 userId 必填但从未使用。

**注意**: `nusmvOutput` 虽然后端 TaskDto 不返回，但 `Board.vue:2016` 和 `Board.vue:2026`
仍在读取 `task.nusmvOutput`。因此**保留为可选字段**而非删除，避免引入新编译错误。
后续如确认不再需要，可连同使用点一起清理。

**文件**: `src/types/verify.ts` 第 57-70 行

**修改为**:
```typescript
export interface VerificationTask {
  id: number;
  // userId 已删除 — 后端不返回，前端无使用处
  status: 'PENDING' | 'RUNNING' | 'COMPLETED' | 'FAILED' | 'CANCELLED';
  createdAt: string;
  startedAt?: string;
  completedAt?: string;
  processingTimeMs?: number;
  progress?: number;       // 新增：0-100 进度
  isSafe?: boolean;
  violatedSpecCount?: number;
  checkLogs?: string[];
  nusmvOutput?: string;    // 后端 TaskDto 不返回，但 Board.vue 仍在读取，保留为可选
  errorMessage?: string;
}
```

**文件**: `src/types/simulation.ts` 第 76-89 行

**修改为**:
```typescript
export interface SimulationTask {
  id: number;
  // userId 已删除
  status: SimulationTaskStatus;
  requestedSteps: number;
  steps: number;
  errorMessage?: string;
  checkLogs?: string[];
  createdAt: string;
  startedAt?: string;
  completedAt?: string;
  processingTimeMs?: number;
  progress?: number;       // 新增
  simulationTraceId?: number;
}
```

---

### F-07 `SimulationTraceSummary` / `SimulationTrace` — userId 对齐

`SimulationTraceSummaryDto`（列表接口）**不返回 `userId`**，但
`SimulationTraceDto`（详情接口）**返回 `userId`**。

当前前端 `SimulationTrace extends SimulationTraceSummary`，如果只删 Summary 的 userId，
Trace 也会丢失。正确做法：Summary 删除，Trace 补回。

**文件**: `src/types/simulation.ts` 第 56-70 行

**修改为**:
```typescript
// 摘要（列表用）— SimulationTraceSummaryDto 不返回 userId
export interface SimulationTraceSummary {
  id: number
  requestedSteps: number
  steps: number
  createdAt: string
}

// 详情 — SimulationTraceDto 返回 userId
export interface SimulationTrace extends SimulationTraceSummary {
  userId?: number          // 详情接口返回，摘要不返回，标可选
  states: SimulationState[]
  logs: string[]
  nusmvOutput: string
  requestJson: string
}
```

---

### F-08 `TraceDevice`（验证侧）— 与后端 `TraceDeviceDto` 字段对齐

后端 `TraceDeviceDto` 有 `mode` 字段；`trustPrivacy`/`privacies` 可能为 null
（`@JsonInclude(NON_NULL)`）。

`newState` 后端仅做反序列化兼容（`@JsonAlias`），新响应中只返回 `state`。
但前端 `TraceVisualization.vue:422/424`、`CanvasBoard.vue:236/262/311/451/461/582`
大量使用 `device.newState` 做 fallback 读取（`device.state || device.newState`），
**不能直接删除**，必须保留为可选字段。

后端 `TraceTrustPrivacyDto.trust` 是可空 `Boolean`（三态：true/false/null），
前端 `TraceTrustPrivacy.trust` 应改为 `boolean | null` 并标可选。

**文件**: `src/types/verify.ts` 第 34-43 行

**修改为**:
```typescript
export interface TraceDevice {
  deviceId: string;
  deviceLabel: string;
  templateName: string;
  state?: string;
  mode?: string;                       // 新增：状态机名称
  newState?: string;                   // 保留：旧数据兼容，多处组件仍在 fallback 读取
  variables: TraceVariable[];
  trustPrivacy?: TraceTrustPrivacy[];   // 改为可选
  privacies?: TraceTrustPrivacy[];      // 改为可选
}
```

同时 `TraceVariable.trust` 应改为可选（后端可空）：

```typescript
export interface TraceVariable {
  name: string;
  value: string;
  trust?: string;    // 改为可选
}
```

同时 `TraceTrustPrivacy.trust` 应改为可空（后端三态 Boolean）：

```typescript
export interface TraceTrustPrivacy {
  name: string;
  trust?: boolean | null;   // 后端 Boolean 包装类型，支持 true/false/null
  privacy: string;
}
```

---

## 低（功能缺口 / 代码规范）

### F-09 `board.ts` — 补 `deleteDeviceTemplate` 方法

后端有 `DELETE /api/board/templates/{id}`，前端 API 层没有封装，
导致 `ControlCenter.vue:850` 使用 raw `fetch`。

**文件**: `src/api/board.ts`

**在 `reloadDeviceTemplates` 之后添加**:
```typescript
deleteDeviceTemplate: async (id: number): Promise<void> => {
    return unpack<void>(await api.delete(`/board/templates/${id}`));
},
```

然后将 `ControlCenter.vue:850` 的 raw fetch 替换为调用此方法。

---

### F-10 raw `fetch()` 调用迁移

以下位置绕过了 `http.ts` 的 axios 拦截器（401 跳转、token 自动注入），
建议迁移到 `boardApi`：

| 位置 | 当前调用 | 建议替换为 |
|------|---------|-----------|
| `ControlCenter.vue:796` | `fetch('/api/device-templates/import')` | 见 F-03 |
| `ControlCenter.vue:850` | `fetch('/api/board/templates/${id}', DELETE)` | `boardApi.deleteDeviceTemplate(id)` |
| `CustomTemplateCreator.vue:224` | `fetch('/api/board/templates', POST)` | `boardApi.addDeviceTemplate(tpl)`（见下方注意事项） |
| `CustomTemplateCreator.vue:387` | `fetch('/api/board/templates', POST)` | `boardApi.addDeviceTemplate(tpl)`（见下方注意事项） |

**CustomTemplateCreator 迁移注意事项**:

现有代码基于 raw fetch 的 `response.ok` / `response.json()` / `newTemplate.data`
做错误处理和返回值提取（第 239-268 行、第 399-404 行）。
迁移到 `boardApi.addDeviceTemplate()` 后，这些逻辑需要同步调整：

- `boardApi.addDeviceTemplate()` 内部已通过 `unpack()` 解包 `Result<T>`，
  直接返回 `DeviceTemplate` 对象（而非 `Response`），不再需要 `.json()` 和 `.data` 访问。
- HTTP 错误会被 axios 拦截器抛出为异常，不再需要手动检查 `response.ok`。

第 224 行示例改法：
```typescript
// 替换前（第 224-268 行）:
// const response = await fetch(...)
// if (!response.ok) { ... }
// const newTemplate = await response.json()
// return newTemplate.data

// 替换后:
const result = await boardApi.addDeviceTemplate({
  name: customTemplateForm.name,
  manifest
})
ElMessage.success('Template created')
router.push('/board')
emit('refresh-templates')
return result
```

第 387 行同理，将 `response.json()` / `result.data` 逻辑替换为直接使用返回值。

`src/api/chat.ts:69` 的 `fetch` 用于 SSE 流式读取，保留 raw fetch 是合理的。
（注意：项目中还有 `src/stores/chat.ts`，是不同文件，此处仅指 `src/api/chat.ts`。）

---

### F-11 API 基址策略统一

当前三套策略并存：
- `http.ts`：硬编码 `http://localhost:8080/api`
- `ControlCenter.vue` / `CustomTemplateCreator.vue`：相对路径 `/api/...`
- `chat.ts`：`VITE_API_BASE_URL` 环境变量

**建议**: `http.ts` 改为从环境变量读取：
```typescript
baseURL: (import.meta.env.VITE_API_BASE_URL || 'http://localhost:8080') + '/api'
```

迁移完 F-10 后，所有非 SSE 请求统一走 axios，基址问题自然收敛。

---

### F-12 Fix 新端点前端未接入（按需）

后端新增：
- `GET /api/verify/traces/{id}/fault-rules` — 故障定位
- `POST /api/verify/traces/{id}/fix` — 修复建议

如需暴露修复功能，需新建 `src/types/fix.ts` 和在 `src/api/board.ts` 中添加调用方法。
具体类型定义参考后端 `dto/fix/` 包中的 DTO。

---

## 速查清单

| 编号 | 严重度 | 文件 | 一句话 |
|------|--------|------|--------|
| F-01 | 阻断 | `api/board.ts:260` | `.Variables` → `.InternalVariables` + PascalCase 映射 |
| F-02 | 阻断 | `ChatView.vue:165` | 删除未使用的 `toggleChat` |
| F-03 | 高 | `ControlCenter.vue:796` | 端点 404 + 裸 manifest 需包装为 `{name, manifest}` |
| F-04 | 中 | `types/verify.ts` | `VerificationRequest` 补 `enablePrivacy: boolean` |
| F-05 | 中 | `types/device.ts:60` | `id: string` → `id?: number` |
| F-06 | 中 | `types/verify.ts` + `types/simulation.ts` | Task 类型删 `userId`、保留 `nusmvOutput?`、补 `progress?` |
| F-07 | 中 | `types/simulation.ts` | `SimulationTraceSummary` 删 `userId` |
| F-08 | 中 | `types/verify.ts` | `TraceDevice` 补 `mode?`、保留 `newState?`、`TraceTrustPrivacy.trust` 改 `boolean \| null` |
| F-09 | 低 | `api/board.ts` | 补 `deleteDeviceTemplate` 方法 |
| F-10 | 低 | 4 处 raw fetch | 迁移到 boardApi |
| F-11 | 低 | `api/http.ts` | baseURL 从环境变量读取 |
| F-12 | 低 | 新建 | Fix 端点按需接入 |

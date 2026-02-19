# NuSMV 模块完整架构与实现文档

> **最后更新**: 2026年2月18日
> **基于实现版本**: 统一 VerificationService + Per-Spec 结果 + DTO 拆分 + 代码整理
> **文档状态**: ✅ 已验证与代码同步

---

## 目录

1. [架构概览](#1-架构概览)
2. [核心组件](#2-核心组件)
3. [数据流](#3-数据流)
4. [SMV生成详解](#4-smv生成详解)
5. [规格类型](#5-规格类型)
6. [验证结果](#7-验证结果)
7. [异步验证架构](#10-异步验证架构)
8. [API 端点](#8-api-端点)
9. [重构记录（2026-02-14）](#9-重构记录2026-02-14)
10. [重构记录（2026-02-15）](#10-重构记录2026-02-15)
11. [Bug 修复记录（2026-02-15）](#11-bug-修复记录2026-02-15)
12. [代码整理记录（2026-02-18）](#12-代码整理记录2026-02-18)

---

## 1. 架构概览

### 1.1 整体架构

```
[Controller层]
    VerificationController
    ├── POST /api/verify          → 同步验证
    ├── POST /api/verify/async    → 异步验证（后端创建任务）
    ├── GET  /api/verify/tasks/{id}          → 任务状态
    ├── GET  /api/verify/tasks/{id}/progress → 任务进度
    ├── POST /api/verify/tasks/{id}/cancel   → 取消任务
    ├── GET  /api/verify/traces              → 用户所有 Trace
    ├── GET  /api/verify/traces/{id}         → 单个 Trace
    └── DELETE /api/verify/traces/{id}       → 删除 Trace

[Service层]
    VerificationService (接口)
    └── VerificationServiceImpl (唯一实现)
        ├── verify()         → 同步验证
        ├── verifyAsync()    → 异步验证 (@Async)
        ├── createTask()     → 创建异步任务
        ├── getTaskProgress() → 获取进度
        └── CRUD: getTask/getUserTraces/getTrace/deleteTrace/cancelTask

[Component层 - NuSMV模块]
    component/nusmv/
    ├── generator/
    │   ├── SmvGenerator              → 协调器，调用各子Builder生成SMV文件
    │   ├── SmvModelValidator         → 集中式前置校验器（P1-P5）
    │   ├── PropertyDimension         → 信任/隐私维度枚举
    │   ├── data/
    │   │   ├── DeviceSmvData         → 设备 SMV 数据模型（纯数据）
    │   │   └── DeviceSmvDataFactory  → 从 DeviceVerificationDto + 模板构建 DeviceSmvData
    │   └── module/
    │       ├── SmvDeviceModuleBuilder  → 设备 MODULE 定义
    │       ├── SmvMainModuleBuilder    → main MODULE（设备实例化 + 状态转换）
    │       ├── SmvRuleCommentWriter    → 规则注释
    │       └── SmvSpecificationBuilder → CTLSPEC / LTLSPEC 生成
    ├── executor/
    │   └── NusmvExecutor             → 执行 NuSMV 进程，返回 per-spec 结果
    └── parser/
        └── SmvTraceParser            → 解析 counterexample 为 TraceStateDto

[DTO层]
    dto/device/
    ├── DeviceNodeDto              → 画布设备节点（UI 布局 + 持久化，含全部字段）
    ├── DeviceVerificationDto      → 验证专用设备数据（仅 id, templateName, state + 运行时状态）
    ├── VariableStateDto           → 变量状态（name, value, trust）
    ├── PrivacyStateDto            → 隐私状态（name, privacy）
    └── DeviceTemplateDto          → 设备模板定义
    dto/verification/
    ├── VerificationRequestDto    → 验证请求（devices: List<DeviceVerificationDto>, rules, specs, isAttack, intensity）
    ├── VerificationResultDto     → 验证结果（safe, traces, specResults, checkLogs）
    └── VerificationTaskDto       → 异步任务状态
    dto/trace/
    ├── TraceDto                  → 违规轨迹（含 states, violatedSpecId）
    ├── TraceStateDto             → 状态步骤
    ├── TraceDeviceDto            → 设备在某步骤的状态
    ├── TraceVariableDto          → 变量值
    └── TraceTrustPrivacyDto      → 信任/隐私变化

[Mapper层]
    util/mapper/
    ├── DeviceNodeMapper           → DeviceNodePo <-> DeviceNodeDto, DeviceNodeDto -> DeviceVerificationDto
    ├── TraceMapper               → TracePo <-> TraceDto
    ├── VerificationTaskMapper    → VerificationTaskPo <-> VerificationTaskDto
    └── SpecificationMapper       → SpecificationPo <-> SpecificationDto

[PO层]
    po/
    ├── VerificationTaskPo        → 验证任务实体（status, isSafe, checkLogsJson）
    └── TracePo                   → 轨迹实体（statesJson, violatedSpecId）
```

---

## 2. 核心组件

### 2.1 VerificationServiceImpl

统一的验证服务，管理同步/异步两条路径：

- **同步 `verify()`**: 直接执行验证，返回 `VerificationResultDto`
- **异步 `verifyAsync()`**: `@Async("verificationTaskExecutor")` 异步执行，通过 `VerificationTaskPo` 跟踪状态
- **任务创建 `createTask()`**: 异步验证前由 Controller 调用，返回 taskId
- **Per-spec 结果**: `buildVerificationResult()` 根据 NusmvExecutor 返回的每个 spec 独立结果生成对应的 traces

### 2.2 NusmvExecutor

执行 NuSMV 进程并解析 per-spec 结果：

- 跨平台命令构建（Windows/Linux）
- 超时控制（配置 `nusmv.timeout-ms`，环境变量 `NUSMV_TIMEOUT_MS` 覆盖）
- 返回 `NusmvResult`，包含 `List<SpecCheckResult>`（每个 spec 的 passed/counterexample）

### 2.3 SmvGenerator + DeviceSmvDataFactory

SMV 文件生成的两层结构：

- `SmvGenerator`: 协调层，调用 DeviceSmvDataFactory 构建设备数据，协调各子 Builder 生成内容，写入临时文件
- `DeviceSmvDataFactory`: 从 `DeviceVerificationDto` + 设备模板构建 `DeviceSmvData`
  - 解析模板 manifest 中的 modes、states、variables、transitions
  - 合并用户运行时输入（currentState、variableValues、trust/privacy 覆盖）

### 2.4 SmvTraceParser

解析 NuSMV counterexample 输出为 `List<TraceStateDto>`：

- 匹配 `State 1.N:` 格式的状态行
- 提取 `device.attr = value` 格式的变量赋值
- 通过 `DeviceSmvData` 映射还原设备名称和状态

---

## 3. 数据流

### 3.1 同步验证流程

```
VerificationRequestDto
    → VerificationServiceImpl.verify()
        → SmvGenerator.generate()           → File (model.smv)
        → NusmvExecutor.execute()           → NusmvResult (per-spec results)
        → buildVerificationResult()
            → SmvTraceParser (for each violated spec)
            → saveTraces() (auto-persist violations)
        → VerificationResultDto
```

### 3.2 异步验证流程

```
VerificationRequestDto
    → Controller: createTask()              → taskId
    → VerificationServiceImpl.verifyAsync() → (异步线程)
        → task.status = RUNNING
        → SmvGenerator.generate()
        → NusmvExecutor.execute()
        → buildVerificationResult()
        → completeTask() / failTask()
        → task.status = COMPLETED / FAILED
```

---

## 4. SMV生成详解

### 4.1 生成结构

```smv
-- Rules (注释)
--IF sensor.temperature>30 THEN ac.turnOn

MODULE DeviceName          -- 设备模块（SmvDeviceModuleBuilder）
  FROZENVAR                -- 攻击模式: is_attack; 传感器: trust_*/privacy_*
  VAR                      -- state, mode, variables, signals
  ASSIGN                   -- init/next 状态转换

MODULE main                -- 主模块（SmvMainModuleBuilder）
  VAR
    intensity: 0..50;      -- 攻击强度（VAR，非 FROZENVAR）
    device1: DeviceName;   -- 设备实例
  ASSIGN
    init(intensity) := <count>;
    next(intensity) := intensity;  -- 保持常量
    -- 状态转换、信号、信任、隐私、变量率

-- Specifications            -- 注释行（非 NuSMV 关键字）
  CTLSPEC AG(...)           -- CTL 规格
  LTLSPEC G(... -> F G(...)) -- LTL 规格
```

### 4.2 攻击模式

- `is_attack`: 设备级 FROZENVAR，非确定性选择
- `intensity`: main 模块 VAR，init 为攻击设备数量，next 保持不变
- 规格中通过 `intensity<=N` 约束攻击影响范围

---

## 5. 规格类型

| 模板ID | 类型 | NuSMV 语法 | 含义 |
|--------|------|-----------|------|
| 1 | Safety | `CTLSPEC AG(A -> B)` | 全局安全性 |
| 2 | Reachability | `CTLSPEC EF(A & B)` | 可达性 |
| 3 | Response | `CTLSPEC AG(A -> AF(B))` | 响应性 |
| 4 | Liveness | `CTLSPEC AG(AF(A))` | 活性 |
| 5 | Fairness | `CTLSPEC AG(A -> EF(B))` | 公平性 |
| 6 | Persistence | `LTLSPEC G(A -> F G(B))` | 持久性 |

条件目标类型（`SpecConditionDto.targetType`）：
- `state`: 设备状态 `device.state = value`
- `variable`: 变量值 `device.var > value`
- `api`: API 信号 `device.apiName_a = TRUE/FALSE`
- `trust`: 信任度 `device.trust_StateName = trusted/untrusted`
- `privacy`: 隐私级别 `device.privacy_StateName = public/private`

---

## 6. 验证结果

### 6.1 VerificationResultDto

```java
VerificationResultDto {
    boolean safe;              // 所有 spec 是否都通过
    List<TraceDto> traces;     // 违规轨迹（仅违反的 spec 有对应 trace）
    List<Boolean> specResults; // per-spec 结果（与 specs 列表一一对应）
    List<String> checkLogs;    // 检查日志
    String nusmvOutput;        // 原始 NuSMV 输出（截断至 10000 字符）
}
```

### 6.2 Per-Spec 结果映射

NuSMV 对每个 SPEC 独立输出 `is true` 或 `is false`：
- `specResults[i] = true`: 第 i 个 spec 通过
- `specResults[i] = false`: 第 i 个 spec 违反，对应的 counterexample 生成 TraceDto

### 6.3 任务状态语义

```java
enum TaskStatus {
    PENDING,    // 任务已创建，等待执行
    RUNNING,    // 验证进行中
    COMPLETED,  // 验证完成（无论安全与否）
    FAILED,     // 执行异常（NuSMV 错误、超时等）
    CANCELLED   // 用户取消
}
```

注意：`COMPLETED` 表示验证正常完成，通过 `isSafe` 字段区分是否安全。`FAILED` 仅用于执行异常。

---

## 7. 异步验证架构

### 7.1 线程池配置

```java
@Bean("verificationTaskExecutor")
public Executor verificationTaskExecutor() { ... }
```

### 7.2 任务生命周期

```
createTask() → PENDING
    ↓
verifyAsync() → RUNNING
    ↓
成功 → COMPLETED (isSafe=true/false)
异常 → FAILED (errorMessage)
取消 → CANCELLED
```

### 7.3 进度跟踪

- 0% → 任务启动
- 20% → 生成 SMV 模型
- 50% → 执行 NuSMV
- 80% → 解析结果
- 100% → 验证完成

通过 `ConcurrentHashMap<Long, Integer>` 内存存储，`GET /tasks/{id}/progress` 查询。

### 7.4 取消机制

- `cancelTask()` 通过 `Thread.interrupt()` 中断运行中的任务
- 异步方法中检查 `Thread.currentThread().isInterrupted()` 响应取消

---

## 8. API 端点

| 端点 | 方法 | 说明 | 请求体 | 返回 |
|------|------|------|--------|------|
| `/api/verify` | POST | 同步验证 | `VerificationRequestDto` | `VerificationResultDto` |
| `/api/verify/async` | POST | 异步验证 | `VerificationRequestDto` | `Long` (taskId) |
| `/api/verify/tasks/{id}` | GET | 任务状态 | - | `VerificationTaskDto` |
| `/api/verify/tasks/{id}/progress` | GET | 任务进度 | - | `Integer` (0-100) |
| `/api/verify/tasks/{id}/cancel` | POST | 取消任务 | - | `Boolean` |
| `/api/verify/traces` | GET | 用户所有 Trace | - | `List<TraceDto>` |
| `/api/verify/traces/{id}` | GET | 单个 Trace | - | `TraceDto` |
| `/api/verify/traces/{id}` | DELETE | 删除 Trace | - | `Void` |

---

## 9. 重构记录（2026-02-14）

### 删除的文件
- `NusmvExecutorService.java` + `NusmvExecutorServiceImpl.java`: 与 component 层 NusmvExecutor 完全重复
- `EnhancedSmvTraceParser.java`: 未被任何代码引用

### 主要修复
1. **Service 合并**: 所有 NuSMV 相关逻辑统一到 `VerificationServiceImpl`
2. **Per-spec 结果**: NusmvExecutor 返回每个 spec 的独立结果，不再 all-or-nothing
3. **任务状态语义**: `COMPLETED` = 验证完成（安全或不安全），`FAILED` = 执行异常
4. **SMV 语法修复**: 移除无效 `SPECIFICATION` 关键字；`intensity` 从 FROZENVAR 改为 VAR
5. **Controller 修复**: 移除 impl 强转；异步任务由后端创建
6. **DTO 修复**: `TraceDto.verificationTaskId` 改为可选（同步验证无 task）
7. **异步事务**: 移除 `verifyAsync()` 上的 `@Transactional`，避免 `@Async` + `@Transactional` 冲突

---

## 10. 重构记录（2026-02-15）

### DeviceNodeDto 拆分

将 `DeviceNodeDto` 按关注点拆分为独立 DTO：

#### 新增文件
- `dto/device/DeviceVerificationDto.java` — 验证专用 DTO，仅含验证所需字段
- `dto/device/VariableStateDto.java` — 变量状态（从 DeviceNodeDto 内部类提取）
- `dto/device/PrivacyStateDto.java` — 隐私状态（从 DeviceNodeDto 内部类提取）

#### DTO 职责划分

| DTO | 用途 | 字段 |
|-----|------|------|
| `DeviceNodeDto` | 画布 CRUD / 持久化 | id, templateName, label, position, state, width, height, currentStateTrust, variables, privacies |
| `DeviceVerificationDto` | SMV 验证请求 | id, templateName, state, currentStateTrust, variables, privacies |
| `VariableStateDto` | 变量运行时状态 | name, value, trust |
| `PrivacyStateDto` | 隐私运行时状态 | name, privacy |

#### 运行时字段语义

- `currentStateTrust`: 设备级信任覆盖 → `smv.currentStateTrust` + `smv.instanceStateTrust`
- `variables[].value`: 变量初始值 → `smv.variableValues`
- `variables[].trust`: 变量信任覆盖 → `smv.instanceVariableTrust`
- `privacies[].privacy`: 状态/变量/内容隐私覆盖 → `smv.instanceVariablePrivacy`

#### 数据流变更

```
画布 CRUD:  Frontend ←→ BoardStorageController ←→ DeviceNodeDto ←→ DeviceNodePo
验证请求:  Frontend → VerificationController → DeviceVerificationDto → DeviceSmvDataFactory → DeviceSmvData
转换桥接:  DeviceNodeMapper.toVerificationDto(DeviceNodeDto) → DeviceVerificationDto
```

#### 修改的文件
- `VerificationRequestDto.devices` 类型: `List<DeviceNodeDto>` → `List<DeviceVerificationDto>`
- `VerificationService` / `VerificationServiceImpl`: 参数类型同步更新
- `SmvGenerator` / `DeviceSmvDataFactory` / `SmvMainModuleBuilder`: 参数类型同步更新
- `DeviceNodeMapper`: 新增 `toVerificationDto()` 方法

---

## 11. Bug 修复记录（2026-02-15）

### 🔴 Critical: VerificationServiceImpl.buildDeviceSmvMap() 数据不完整

**问题**: `VerificationServiceImpl` 中有一个本地 `buildDeviceSmvMap()` 方法，仅设置了 `id`、`name`、`deviceNo`、`currentState` 四个字段，缺少 `states`、`modes`、`variables`、`manifest` 等关键数据。导致 `SmvTraceParser.matchState()` 无法匹配状态名，反例轨迹解析失败。

**修复**: 删除本地方法，改为复用 `DeviceSmvDataFactory.buildDeviceSmvMap()`。同时更新 `buildVerificationResult()` 签名，传入 `rules` 参数。

**涉及文件**:
- `DeviceSmvDataFactory.java`: 提供 `buildDeviceSmvMap()` 方法
- `VerificationServiceImpl.java`: 删除本地 `buildDeviceSmvMap()` 和 `extractDeviceNo()`，注入 `DeviceSmvDataFactory`

### 🔴 Bug: BoardStorageServiceImpl.saveRules() null 进入 Set

**问题**: `saveRules()` 中 `newRuleIds.add(ruleId)` 在 `ruleId` 为 null 时将 null 加入 Set，导致后续删除逻辑 `!newRuleIds.contains(existingId)` 判断异常。

**修复**: 添加 null 守卫：`if (ruleId != null) newRuleIds.add(ruleId)`

### ⚠️ VerificationRequestDto 缺少校验注解

**问题**: `devices` 和 `specs` 字段无 `@NotNull`，`intensity` 无范围约束，Controller 的 `@Valid` 形同虚设。

**修复**: 添加 `@Valid @NotNull` 到 `devices` 和 `specs`，添加 `@Min(0) @Max(50)` 到 `intensity`。

### ⚠️ SmvMainModuleBuilder 重复 null 检查

**问题**: 多模式和单模式分支中，`rule.getCommand() == null` 检查连续出现两次（代码冗余）。

**修复**: 移除重复的 if 块，保留一份。

### ⚠️ UserPo 缺少 @PrePersist

**问题**: `UserPo.createdAt` 标记为 `nullable = false`，但没有 `@PrePersist` 自动填充，依赖调用方手动设置。

**修复**: 添加 `@PrePersist onCreate()` 方法，自动填充 `createdAt`。

---

## 12. 代码整理记录（2026-02-18）

### 架构重构

1. **Generator 模块重组**: `SmvContentBuilder` 拆分为 `DeviceSmvDataFactory`（数据构建）+ `SmvGenerator`（协调），子 Builder 移入 `generator/module/` 子包
2. **SmvRulesModuleBuilder → SmvRuleCommentWriter**: 重命名以准确反映职责（仅写注释），移除未使用的 `deviceSmvMap` 参数
3. **PropertyDimension 枚举**: 新增，统一信任/隐私维度逻辑
4. **设备模板资源迁移**: JSON 模板从 `src/main/java/.../resource/` 移至 `src/main/resources/deviceTemplate/`

### 分层规范修复

5. **ChatService 返回 DTO**: 接口和实现从返回 `ChatSessionPo`/`ChatMessagePo` 改为返回 `ChatSessionResponseDto`/`ChatMessageResponseDto`，Controller 不再暴露 PO
6. **RedisTokenBlacklistService 移至 impl 包**: 从 `service/` 移到 `service/impl/`，符合接口-实现分层约定
7. **ChatMapper 清理**: 全限定类名替换为 import 语句

### 冗余代码清理

8. **NusmvExecutor.TRACE_HEADER_PATTERN**: 未使用的正则常量，已删除
9. **SmvTraceParser.currentStateIndex**: 未使用的局部变量，已删除
10. **WebConfig 重复 CORS**: 与 SecurityConfig 重复的 CORS 配置，已删除（保留 SecurityConfig 中的配置）

### 命名一致性

11. **AuthController**: `@CurrentUser Long currentUser` → `@CurrentUser Long userId`，与其他 Controller 统一
12. **Result.success(null)** → **Result.success()**: ChatController、BoardStorageController 中的 void 响应统一使用无参版本

### 防御性编程

13. **SmvTraceParser.matchState()**: 添加 `getStates()`/`getModes()` null 安全检查
14. **DeviceTemplateMapper**: manifest 序列化从 `toJsonOrEmpty`（返回 `"[]"`）改为 `toJson`（返回 `null`），语义正确

---

## 13. 代码审查修复记录（2026-02-18）

### Bug 修复

1. **SmvSpecificationBuilder.resolveStateTrust()**: 当 `value` 为 null 时，trust 变量名拼接产生尾部下划线（如 `trust_key_`），导致无效 SMV 语法。修复为 null 时省略 `_value` 后缀
2. **BoardStorageServiceImpl.saveRules()**: 当 `ruleId != null` 但不在 `existingRules` 中时，else 分支未设置 ID，导致 JPA 创建新实体而非更新。简化为统一 `po.setId(ruleId)` 逻辑

### 异常处理完善

3. **GlobalExceptionHandler**: 新增 `SmvGenerationException` 专用 handler，返回包含 `errorCategory` 的错误信息，不再被通用 `InternalServerException` handler 吞掉
4. **ValidationException HTTP 状态码对齐**: handler 从 `400 Bad Request` 修正为 `422 Unprocessable Entity`，与 `ValidationException` 自身的 code=422 和 `Result.validationError()` 一致

### 命名改进

5. **SmvMainModuleBuilder.getEndStateForMode() → getStateForMode()**: 该方法同时用于解析 `startState` 和 `endState` 的多模式字符串，旧名称具有误导性

### 配置修复

6. **application.yaml Redis 配置缩进错误**: `spring.data.redis` 配置错误地嵌套在 `jwt:` 下，导致 Redis 连接失败。修正为顶层 `spring.data.redis:` 键
7. **API-DOCUMENTATION.md 合并**: 内容已合并到 README.md，删除冗余文件
8. **CLAUDE.md 完善**: 新增 SMV 生成详细文档、MEDIC-test 对照表、完整 API 端点列表、数据库表清单

## 14. MEDIC 对照审查与增强（2026-02-18）

### 建议1: 攻击模式传感器数值范围扩大
- `SmvDeviceModuleBuilder.appendInternalVariables()`: 攻击模式下传感器设备的数值型变量上界扩大 20%（最少 +10），模拟数据篡改攻击
- `SmvMainModuleBuilder`: 环境变量声明同样在攻击模式下扩大范围
- 参考 MEDIC-test `outModule()` 中被注释的 `upperBound+40` 逻辑

### 建议3: enablePrivacy 开关
- `VerificationRequestDto` 新增 `enablePrivacy` 字段（默认 false）
- 参数从 Controller → Service → SmvGenerator → SmvDeviceModuleBuilder / SmvMainModuleBuilder 全链路传递
- `enablePrivacy=false` 时跳过所有 privacy 相关的 FROZENVAR/VAR 声明、ASSIGN init、next() 转换
- 对应 MEDIC 的 `now == 3` 全局标志

### 建议4: trust 传播逻辑验证
- 对照 MEDIC lines 862-948 验证 trust 传播逻辑
- 差异：本项目使用 AND（所有条件源都可信才传播）而非 MEDIC 的 OR（任一可信即传播），AND 更保守安全
- 攻击模式 `is_attack=TRUE: untrusted` 逻辑一致
- 默认 case 自保持逻辑一致

### 建议5: getModeIndexOfState() 行为验证
- MEDIC 实现：简单计数前导分号
- 本项目实现：多策略（mode 名匹配 → 分号分割 → 状态列表查找），严格兼容 MEDIC 行为且更健壮

### 建议6: 环境变量初始值范围校验
- `SmvMainModuleBuilder.validateEnvVarInitValue()`: 新增校验方法
- 数值型变量：超出 `[lower, upper]` 范围时 clamp 到边界并记录警告
- 枚举型变量：值不在枚举列表中时使用第一个值并记录警告
- 非法数值格式：忽略并记录警告

---

## 15. 模型前置校验与架构整理（2026-02-18）

### 新增组件

**SmvModelValidator**（`generator/SmvModelValidator.java`）— 集中式模型前置校验器

在 `SmvGenerator.buildSmvContent()` 中，`DeviceSmvDataFactory.buildDeviceSmvMap()` 之后、SMV 文本生成之前调用 `modelValidator.validate(deviceSmvMap)`，将所有模板/实例数据的不合法项提前拦截，避免生成无效 SMV 交给 NuSMV 报错。

校验职责分为两类：

| 类型 | 方法 | 调用方 | 行为 |
|------|------|--------|------|
| 硬性校验 | `validate()` | `SmvGenerator` | 抛出 `SmvGenerationException` |
| 软性校验 | `warnUnknownUserVariables()` | `DeviceSmvDataFactory` | 仅 log.warn |
| 软性校验 | `warnStatelessDeviceWithState()` | `DeviceSmvDataFactory` | 仅 log.warn |

### P1: Trigger.Attribute 合法性校验

- 对每个设备的每个 Transition/API 的 `Trigger.Attribute` 检查是否属于合法集合
- 合法集合 = `modes` ∪ `internalVariables[*].name`（含 env var）
- 不合法时抛出 `SmvGenerationException.illegalTriggerAttribute()`，包含设备名、transition/API 名、非法属性、合法列表

### P2: StartState/EndState 格式与语义校验

- 多 mode 设备：`split(";", -1)` 段数必须 == `modes.size()`，每段要么为空要么属于对应 mode 的合法取值
- 单 mode 设备：不能包含 `;`，值必须属于该 mode 的合法取值
- 不合法时抛出 `SmvGenerationException.invalidStateFormat()`

### P3: 同名环境变量冲突检测

- 多设备声明同名外部变量（`IsInside=false`）时，要求类型一致：
  - 都是数值型：`LowerBound`/`UpperBound` 必须相同
  - 都是枚举型：`Values` 集合必须相同（忽略顺序）
  - 类型不同（一个数值一个枚举）：直接冲突
- 不一致时抛出 `SmvGenerationException.envVarConflict()`

### P4: appendEnvTransitions 条件引用优化

- 当 transition 的 `trigger.attribute` 本身是环境变量时，生成的 `next(a_var)` case 条件直接使用 `a_<attr>` 而非 `device.attr`
- 例：`a_time = 23 : 0;` 而非 `clock_1.time = 23 : 0;`
- 新增辅助方法 `SmvMainModuleBuilder.isEnvVariable()` 判断属性是否为环境变量

### P5: trust/privacy 一致性校验

- 检查同一 `(mode, stateName)` 在不同 WorkingState 中是否被赋予不同 trust 值
- 例：`home;idle` trust=trusted 与 `home;active` trust=untrusted → `Mode_home` 冲突
- 不一致时抛出 `SmvGenerationException.trustPrivacyConflict()`
- 注：trust/privacy 的 `next()` 自保持（`TRUE: propVar;`）在 `appendPropertyTransitions` 中已正确生成，无需额外修复

### 异常体系整理

- 删除 `generator/SmvValidationException.java`（独立异常类）
- 在 `exception/SmvGenerationException` 中新增 4 个工厂方法和对应 ErrorCategories：
  - `illegalTriggerAttribute()` → `ILLEGAL_TRIGGER_ATTRIBUTE`
  - `invalidStateFormat()` → `INVALID_STATE_FORMAT`
  - `envVarConflict()` → `ENV_VAR_CONFLICT`
  - `trustPrivacyConflict()` → `TRUST_PRIVACY_CONFLICT`
- 所有校验异常统一走 `BaseException → InternalServerException → SmvGenerationException` 继承链，被 `GlobalExceptionHandler.handleSmvGenerationException()` 捕获

### 校验逻辑集中化

- `DeviceSmvDataFactory` 中原有的 `validateUserVariables()` 方法和内联的多模式 API EndState 分号警告已提取到 `SmvModelValidator` 的公共方法中
- `DeviceSmvDataFactory` 注入 `SmvModelValidator`，调用 `warnUnknownUserVariables()` 和 `warnStatelessDeviceWithState()`

### 单元测试

新增 `SmvGeneratorFixesTest`（8 个测试用例，纯 POJO 构造，不依赖 Spring 上下文）：

| 测试 | 覆盖点 |
|------|--------|
| `triggerAttribute_legal_passes` | P1 正向 |
| `triggerAttribute_illegal_throws` | P1 负向 |
| `multiModeEndState_wrongSegments_throws` | P2 段数不匹配 |
| `envVarConflict_differentRange_throws` | P3 范围冲突 |
| `envVarConflict_sameRange_passes` | P3 正向 |
| `envTransition_usesAVar` | P4 `a_time` 而非 `clock_1.time` |
| `trustNextSelfHold_multiMode` | P5 next() 自保持存在 |
| `trustConflict_throws` | P5 trust 冲突检测 |

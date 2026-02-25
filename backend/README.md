# IoT-Verify Backend

> IoT 设备形式化验证平台后端，基于 NuSMV 模型检测。

## 目录

1. [项目概览](#1-项目概览)
2. [技术栈](#2-技术栈)
3. [项目结构](#3-项目结构)
4. [NuSMV 模块代码详解](#4-nusmv-模块代码详解)
5. [API 端点](#5-api-端点)
6. [数据模型](#6-数据模型)
7. [配置与运行](#7-配置与运行)
8. [实现状态](#8-实现状态)

---

## 1. 项目概览

IoT-Verify 是一个智能家居模拟与形式化验证平台，核心功能包括：

| 功能 | 说明 |
|------|------|
| 设备管理 | 创建、编辑 IoT 设备节点和连接 |
| 规则引擎 | IFTTT 风格的设备交互规则 |
| 规格验证 | 基于 NuSMV 的 CTL/LTL 形式化验证 |
| 随机模拟 | NuSMV 交互式 N 步随机模拟 |
| Trace 分析 | 反例可视化与分析 |
| AI 助手 | 自然语言设备管理接口（火山引擎） |

---

## 2. 技术栈

- Spring Boot 3.5.7 / Java 17
- MySQL + Redis
- JWT 认证
- NuSMV 2.x 模型检测器（已测试 2.5–2.7，不兼容 nuXmv）
- 火山引擎 Ark（AI 助手）

---

## 3. 项目结构

```
src/main/java/cn/edu/nju/Iot_Verify/
├── controller/
│   ├── AuthController.java                # 认证（注册/登录/登出）
│   ├── BoardStorageController.java        # 画布（设备节点/边 CRUD）
│   ├── ChatController.java               # AI 助手（SSE 流式对话）
│   ├── VerificationController.java        # 验证 API 入口
│   └── SimulationController.java          # 模拟 API 入口
├── service/
│   ├── AuthService.java                   # 认证服务
│   ├── BoardStorageService.java           # 画布存储服务
│   ├── ChatService.java                   # AI 对话服务
│   ├── DeviceTemplateService.java         # 设备模板服务
│   ├── NodeService.java                   # 节点服务
│   ├── TokenBlacklistService.java         # Token 黑名单服务
│   ├── UserService.java                   # 用户服务
│   ├── VerificationService.java           # 验证服务接口
│   ├── SimulationService.java             # 模拟服务接口
│   └── impl/
│       ├── AuthServiceImpl.java
│       ├── BoardStorageServiceImpl.java
│       ├── ChatServiceImpl.java
│       ├── DeviceTemplateServiceImpl.java
│       ├── NodeServiceImpl.java
│       ├── RedisTokenBlacklistService.java
│       ├── UserServiceImpl.java
│       ├── VerificationServiceImpl.java   # 验证业务逻辑（同步/异步）
│       └── SimulationServiceImpl.java     # 模拟业务逻辑（执行 + 持久化）
├── component/
│   ├── aitool/                            # AI 工具组件
│   │   ├── AiTool.java                    # 工具接口
│   │   ├── AiToolManager.java             # 工具管理器
│   │   └── node/                          # 节点操作工具
│   │       ├── AddNodeTool.java
│   │       ├── DeleteNodeTool.java
│   │       └── SearchNodeTool.java
│   └── nusmv/                             # ★ NuSMV 核心模块
│       ├── generator/
│       │   ├── SmvGenerator.java           # 协调器：组装完整 SMV 文件
│       │   ├── SmvModelValidator.java      # 前置校验器 (P1-P5)
│       │   ├── PropertyDimension.java      # Trust/Privacy 维度枚举
│       │   ├── data/
│       │   │   ├── DeviceSmvData.java      # 设备 SMV 数据模型（纯 POJO）
│       │   │   └── DeviceSmvDataFactory.java # DTO + 模板 → DeviceSmvData
│       │   └── module/
│       │       ├── SmvDeviceModuleBuilder.java  # 设备 MODULE 定义
│       │       ├── SmvMainModuleBuilder.java    # main MODULE + ASSIGN 规则
│       │       ├── SmvRuleCommentWriter.java    # 规则 → SMV 注释
│       │       └── SmvSpecificationBuilder.java # CTLSPEC / LTLSPEC 生成
│       ├── executor/
│       │   └── NusmvExecutor.java          # 执行 NuSMV 进程（批处理 + 交互式模拟）
│       └── parser/
│           └── SmvTraceParser.java         # 反例文本 → TraceStateDto
├── client/
│   └── ArkAiClient.java                   # 火山引擎 Ark AI 客户端
├── dto/
│   ├── Result.java                        # 统一响应包装
│   ├── auth/                              # 认证 DTO
│   │   ├── LoginRequestDto.java
│   │   ├── RegisterRequestDto.java
│   │   ├── AuthResponseDto.java
│   │   └── RegisterResponseDto.java
│   ├── board/                             # 画布 DTO
│   │   ├── BoardActiveDto.java
│   │   └── BoardLayoutDto.java
│   ├── chat/                              # AI 对话 DTO
│   │   ├── ChatRequestDto.java
│   │   ├── ChatMessageResponseDto.java
│   │   ├── ChatSessionResponseDto.java
│   │   └── StreamResponseDto.java
│   ├── device/                            # 设备 DTO
│   │   ├── DeviceNodeDto.java
│   │   ├── DeviceTemplateDto.java
│   │   ├── DeviceVerificationDto.java     # 验证专用设备数据
│   │   ├── VariableStateDto.java          # 变量状态（name, value, trust）
│   │   └── PrivacyStateDto.java           # 隐私状态（name, privacy）
│   ├── rule/
│   │   ├── RuleDto.java                   # IFTTT 规则
│   │   └── DeviceEdgeDto.java             # 设备连接边
│   ├── spec/
│   │   ├── SpecificationDto.java          # 验证规格
│   │   └── SpecConditionDto.java          # 规格条件
│   ├── simulation/
│   │   ├── SimulationRequestDto.java      # 模拟请求
│   │   ├── SimulationResultDto.java       # 模拟结果（不落库）
│   │   ├── SimulationTaskDto.java         # 模拟异步任务状态
│   │   ├── SimulationTraceDto.java        # 模拟轨迹详情（持久化）
│   │   └── SimulationTraceSummaryDto.java # 模拟轨迹摘要（列表用）
│   ├── verification/
│   │   ├── VerificationRequestDto.java    # 验证请求
│   │   ├── VerificationResultDto.java     # 验证结果
│   │   └── VerificationTaskDto.java       # 异步任务状态
│   └── trace/
│       ├── TraceDto.java                  # Trace 持久化
│       ├── TraceStateDto.java             # 反例状态
│       ├── TraceDeviceDto.java            # 反例设备（state + mode）
│       ├── TraceVariableDto.java          # 反例变量
│       └── TraceTrustPrivacyDto.java      # 反例信任/隐私
├── po/                                    # 持久化实体
│   ├── UserPo.java
│   ├── DeviceNodePo.java
│   ├── DeviceEdgePo.java / DeviceEdgeId.java
│   ├── DeviceTemplatePo.java
│   ├── BoardActivePo.java / BoardLayoutPo.java
│   ├── ChatSessionPo.java / ChatMessagePo.java
│   ├── RulePo.java
│   ├── SpecificationPo.java
│   ├── TracePo.java                       # 验证反例轨迹
│   ├── VerificationTaskPo.java            # 异步验证任务
│   ├── SimulationTaskPo.java              # 异步模拟任务（simulation_task 表）
│   └── SimulationTracePo.java             # 模拟轨迹（simulation_trace 表）
├── repository/                            # JPA Repository
│   ├── UserRepository.java
│   ├── DeviceNodeRepository.java / DeviceEdgeRepository.java
│   ├── DeviceTemplateRepository.java
│   ├── BoardActiveRepository.java / BoardLayoutRepository.java
│   ├── ChatSessionRepository.java / ChatMessageRepository.java
│   ├── RuleRepository.java
│   ├── SpecificationRepository.java
│   ├── TraceRepository.java
│   ├── VerificationTaskRepository.java
│   ├── SimulationTaskRepository.java
│   └── SimulationTraceRepository.java
├── security/                              # 安全模块
│   ├── SecurityConfig.java                # Spring Security + CORS 配置
│   ├── JwtAuthenticationFilter.java       # JWT 过滤器
│   ├── CurrentUser.java                   # @CurrentUser 注解
│   ├── CurrentUserArgumentResolver.java   # 用户 ID 参数解析
│   └── UserContextHolder.java             # 用户上下文
├── util/
│   ├── JwtUtil.java                       # JWT 工具
│   ├── JsonUtils.java                     # JSON 序列化工具
│   ├── LevenshteinDistanceUtil.java       # 编辑距离（AI 工具用）
│   ├── FunctionParameterSchema.java       # AI 函数参数 Schema
│   └── mapper/                            # PO ↔ DTO 转换
│       ├── UserMapper.java
│       ├── DeviceNodeMapper.java / DeviceEdgeMapper.java
│       ├── ChatMapper.java
│       ├── RuleMapper.java
│       ├── SpecificationMapper.java
│       ├── TraceMapper.java
│       ├── VerificationTaskMapper.java
│       ├── SimulationTaskMapper.java
│       └── SimulationTraceMapper.java
├── exception/                             # 异常体系
│   ├── BaseException.java                 # 基类
│   ├── GlobalExceptionHandler.java        # 全局异常处理
│   ├── SmvGenerationException.java        # SMV 生成异常（含工厂方法）
│   ├── BadRequestException.java / ValidationException.java
│   ├── UnauthorizedException.java / ForbiddenException.java
│   ├── ResourceNotFoundException.java / ConflictException.java
│   ├── InternalServerException.java
│   └── ServiceUnavailableException.java
└── configure/
    ├── NusmvConfig.java                   # NuSMV 路径/超时配置
    ├── ThreadPoolConfig.java              # 线程池参数绑定与校验（thread-pool.*）
    ├── ThreadConfig.java                  # 线程池配置
    └── WebConfig.java                     # Web MVC 配置（@CurrentUser 参数解析）
```

---

## 4. NuSMV 模块代码详解

> 完整的用户视角文档（伪代码、SMV 语法、示例文件等）见 [NuSMV_Module_Documentation.md](NuSMV_Module_Documentation.md)。
> 本节聚焦代码实现细节。

### 4.1 SmvGenerator — 协调器

`component/nusmv/generator/SmvGenerator.java`

职责：协调数据准备和各模块构建器，生成完整 SMV 模型文件。

```java
public record GenerateResult(File smvFile, Map<String, DeviceSmvData> deviceSmvMap) {}

public GenerateResult generate(Long userId, List<DeviceVerificationDto> devices,
                               List<RuleDto> rules, List<SpecificationDto> specs,
                               boolean isAttack, int intensity, boolean enablePrivacy)
```

内部流程：
1. `DeviceSmvDataFactory.buildDeviceSmvMap()` — 构建设备数据映射
2. `SmvModelValidator.validate()` — P1-P5 前置校验
3. 按顺序拼接 SMV 文本：RuleComment → DeviceModule → MainModule → Specification
4. 写入临时文件 `model.smv`
5. 返回 `GenerateResult`（文件 + deviceSmvMap，后者供 trace 解析复用）

额外校验：当 `enablePrivacy=false` 时，检查 specs 中是否包含 `targetType="privacy"` 条件，有则抛异常。

### 4.2 DeviceSmvDataFactory — 数据工厂

`component/nusmv/generator/data/DeviceSmvDataFactory.java`

职责：从 `DeviceVerificationDto` + 数据库模板 (`DeviceManifest`) 构建 `DeviceSmvData`。

关键步骤：
1. 从 DB 加载 `DeviceManifest` JSON（含 Modes, WorkingStates, Transitions, APIs, InternalVariables, Contents）
2. `extractModes()` — 解析模式列表
3. `extractStatesAndTrust()` — 解析 WorkingStates，构建 `modeStates` 映射和 trust 默认值
4. `parseCurrentModeStates()` — 将用户传入的 `state` 映射到各模式的初始状态
5. `extractVariables()` — 分离内部变量 (`IsInside=true`) 和环境变量 (`IsInside=false`)
6. `extractSignalVars()` — 从 Transitions 和 APIs 中提取信号变量
7. `extractContents()` — 解析内容（如手机照片）及其隐私属性
8. 合并用户运行时输入（variableValues, instanceVariableTrust, instanceVariablePrivacy）

静态工具方法：
- `cleanStateName(raw)` — 移除分号和空格
- `findDeviceSmvData(name, map)` — 按 varName 或 templateName 查找
- `toVarName(deviceId)` — 转为安全变量名
- `findApi(manifest, actionName)` — 按名称查找 API 定义

### 4.3 DeviceSmvData — 数据模型

`component/nusmv/generator/data/DeviceSmvData.java`

纯数据 POJO，承载从用户输入 + 设备模板解析出的所有信息：

| 字段组 | 字段 | 说明 |
|--------|------|------|
| 标识 | `templateName`, `moduleName`, `varName`, `sensor` | 设备身份和 NuSMV 标识符 |
| 模式与状态 | `modes`, `modeStates`, `states` | 从模板 Modes + WorkingStates 解析 |
| 变量 | `variables`, `envVariables`, `impactedVariables` | 内部变量、环境变量、受影响变量 |
| 信号 | `signalVars` (List&lt;SignalInfo&gt;) | 从 Transitions/APIs 中 signal=true 的项 |
| 内容 | `contents` (List&lt;ContentInfo&gt;) | 设备内容（如 photo），含隐私和可变性 |
| 用户输入 | `currentState`, `currentModeStates`, `variableValues` | 运行时状态和变量值 |
| 信任/隐私 | `modeStateTrust`, `instanceStateTrust`, `instanceVariableTrust`, `instanceVariablePrivacy` | 模板默认 + 用户覆盖 |

### 4.4 SmvDeviceModuleBuilder — 设备 MODULE

`component/nusmv/generator/module/SmvDeviceModuleBuilder.java`

为每种设备模板生成一个 `MODULE` 定义，包含：

1. `FROZENVAR` — 冻结变量（验证期间不变）
   - `is_attack: boolean` — 仅 `isAttack=true`
   - `trust_varName` / `privacy_varName` — 传感器变量的信任/隐私
   - `privacy_contentName` — `IsChangeable=false` 的内容隐私
2. `VAR` — 状态变量
   - 模式状态枚举（如 `ThermostatMode: {cool, heat, off}`）
   - 内部变量（枚举或整数范围）
   - 信号变量（`apiName_a: boolean`）
   - 状态信任/隐私变量
   - `IsChangeable=true` 的内容隐私
   - `varName_rate: min..max` — 受影响变量的变化率（范围根据模板 Dynamics.ChangeRate 动态计算，无 Dynamics 时 fallback 为 -10..10）
3. `ASSIGN` — 初始值
   - `init(modeVar)` — 从用户 state 或模板 InitState 确定
   - `init(variable)` — 从用户 variableValues 或模板默认值，经 `validateInternalInitValue()` 校验（枚举值不在枚举内回退首值；数值超范围 clamp；无枚举/无范围的变量不生成 `init()`）
   - `init(trust_*)` / `init(privacy_*)` — 从模板默认 + 用户覆盖

### 4.5 SmvMainModuleBuilder — main MODULE

`component/nusmv/generator/module/SmvMainModuleBuilder.java`

生成 `MODULE main`，是最复杂的构建器（~1580 行），包含：

1. `FROZENVAR intensity: 0..50` — 仅攻击模式
2. `VAR` — 设备实例化 + 环境变量声明
   - 设备实例：`thermostat_1: Thermostat_thermostat1;`
   - 环境变量：`a_temperature: 15..39;`（攻击模式下仅上界扩展，公式 `expansion = range/5 * intensity/50`）
3. `ASSIGN` — 状态转换逻辑（按顺序）
   - `appendStateTransitions()` — 规则驱动 + 模板 Transition 驱动的状态转换
   - `appendEnvTransitions()` — 环境变量 `next()` 转换（含 NaturalChangeRate、设备影响率、边界检查）
   - `appendApiSignalTransitions()` — API 信号变量（基于状态变化检测）
   - `appendTransitionSignalTransitions()` — 模板 Transition 信号变量
   - `appendPropertyTransitions()` — 状态级信任/隐私传播（使用 `PropertyDimension` 枚举统一逻辑）
   - `appendVariablePropertyTransitions()` — 变量级信任/隐私自保持
   - `appendContentPrivacyTransitions()` — IsChangeable=true 的 content 隐私转换（规则命中时设为 `private`，否则自保持）
   - `appendVariableRateTransitions()` — 受影响变量的变化率
   - `appendExternalVariableAssignments()` — 外部变量镜像环境变量（简单赋值，非 next）
   - `appendInternalVariableTransitions()` — 内部变量 `next()` 转换（攻击模式下范围扩展）

关键设计：
- 环境变量使用 `a_` 前缀在 main 模块声明，避免跨设备引用问题
- 同名环境变量在 `main` 中只声明一次；`init(a_varName)` 通过 `resolveEnvVarInitValues()` 汇总各设备提供的用户初值（经 `validateEnvVarInitValue()` 校验范围）
- 同名环境变量初值在归一化后若不一致，`resolveEnvVarInitValues()` 抛出 `envVarConflict`
- 对无枚举且无上下界定义的环境变量，`main` 默认声明为 `0..100`；初值仅接受整数，越界会 clamp 到 `0/100`
- `PropertyDimension` 枚举合并了 trust 和 privacy 的重复生成逻辑
- 规则条件中的关系符通过 `normalizeRuleRelation()` 归一化
- 规则条件采用 fail-closed：当条件无法解析（设备不存在、空属性、未知属性、不支持 relation、空 value、`IN/NOT_IN` 空列表）时，整条规则 guard 会被置为 `FALSE`
- 当规则条件 `relation != null` 且 `attribute` 指向 API signal 时，会映射为 `device.apiName_a`；仅支持 `=`/`!=`/`IN`/`NOT_IN`，且 value 必须为 `TRUE`/`FALSE`（大小写不敏感）
- 当规则条件 `relation == null` 且 `attribute` 指向 `signal=true` 的 API 时，兼容生成 `(device.apiName_a=TRUE | mode=endState)` 形式条件

### 4.6 SmvSpecificationBuilder — 规格生成

`component/nusmv/generator/module/SmvSpecificationBuilder.java`

根据 `SpecificationDto.templateId` 生成 CTL 或 LTL 公式：
- `templateId="6"` → `LTLSPEC G((IF) -> F G(THEN))`
- `templateId="7"` → Safety 规格（自动注入 trust 和 is_attack 条件）
- 其余 → `CTLSPEC` 各模板（1=AG, 2=AF, 3=AG!, 4=AG→AX, 5=AG→AF）

条件构建通过 `genConditionSpec()` 将 `SpecConditionDto` 映射为 SMV 表达式，支持 `IN`/`NOT_IN` 集合运算。
`targetType` 仅允许 `state|variable|api|trust|privacy`（DTO 层 `@Pattern` 校验 + 生成层 fail-closed）。
`api` 类型条件仅支持 `=`/`!=`/`IN`/`NOT_IN`，值必须为 `TRUE`/`FALSE`，不再硬编码为 `=TRUE`。

攻击预算约束统一放在 `main` 模块的 `INVAR intensity <= N` 中，规格本身不注入 intensity 条件。

无效条件（如找不到设备）抛出 `InvalidConditionException`，生成 `CTLSPEC FALSE` 占位。

### 4.7 NusmvExecutor — 执行器

`component/nusmv/executor/NusmvExecutor.java`

职责：调用 NuSMV 进程并解析输出（批处理验证 + 交互式随机模拟）。

核心逻辑：
- 构建命令：`NuSMV [extraArgs] model.smv`（支持 `command-prefix` 包装）
- 超时控制：从环境变量 `NUSMV_TIMEOUT_MS` 读取，默认由 `NusmvConfig` 配置
- 输出解析：逐行匹配 `-- specification ... is true/false`
- 反例提取：false spec 后的文本直到下一个 spec 结果为 counterexample
- 返回 `NusmvResult`，包含 `List<SpecCheckResult>`（每个 spec 的 passed + counterexample）
- 交互模拟：`executeInteractiveSimulation()` 通过 `-int` 执行 `go -> pick_state -r -> simulate -r -k N -> show_traces -> quit`，并过滤 `NuSMV >` 提示符

### 4.8 SmvTraceParser — 反例解析

`component/nusmv/parser/SmvTraceParser.java`

将 NuSMV 反例文本解析为 `List<TraceStateDto>`：

- 兼容 `State X.Y:` 与 `-> State: X.Y <-` 两种状态行格式
- `device.var = value` → 匹配到对应 `DeviceSmvData` 的变量/状态/信任/隐私
- `a_varName = value` → 环境变量
- 自动补全 `TraceDeviceDto.templateName` 与 `TraceDeviceDto.deviceLabel`
- `trust_` 前缀按类型分流：状态级进入 `trustPrivacy[]`（布尔 trust），变量级写入 `variables[].trust`
- `privacy_` 前缀进入 `privacies[]`（不再混入 `trustPrivacy[]`）
- 过滤内部控制变量：`is_attack`、`*_rate`、`*_a`
- 增量解析：NuSMV 只输出变化项，解析器通过 `previousModeValuesByDevice` 追踪上一状态
- `finalizeModeStates()` — 用临时 `__mode__*` 变量补全未变化模式，并回填最终 `state/mode`

### 4.9 SmvModelValidator — 前置校验

`component/nusmv/generator/SmvModelValidator.java`

在 SMV 生成前执行的集中式校验器：

| 校验 | 方法 | 说明 |
|------|------|------|
| P1 | `validateTriggerAttributes()` | Transition.Trigger.Attribute 必须是合法属性名 |
| P2 | `validateStartEndStates()` | 多模式 EndState 分号段数 = 模式数 |
| P3 | `validateEnvVarConflicts()` | 同名环境变量跨设备范围一致 |
| P5 | `validateTrustPrivacyConsistency()` | 同 (mode, state) 的 trust/privacy 值一致 |

软性校验（由 Factory 调用）：
- `warnUnknownUserVariables()` — 用户变量名不在模板中
- `warnStatelessDeviceWithState()` — 无模式设备传入 state

### 4.10 PropertyDimension — 维度枚举

`component/nusmv/generator/PropertyDimension.java`

```java
public enum PropertyDimension {
    TRUST("trust_", "trusted", "untrusted"),
    PRIVACY("privacy_", "private", "public");

    public final String prefix;       // SMV 变量名前缀
    public final String activeValue;  // 规则触发时的值
    public final String defaultValue; // 默认值
}
```

用于 `SmvMainModuleBuilder.appendPropertyTransitions()` 中合并 trust 和 privacy 的重复生成逻辑。

---

## 5. API 端点

### 认证

所有端点（除 `/api/auth/**`）需要 JWT 认证：`Authorization: Bearer <token>`

### 验证相关

| 方法 | 端点 | 说明 |
|------|------|------|
| `POST` | `/api/verify` | 同步验证 |
| `POST` | `/api/verify/async` | 异步验证，返回 taskId |
| `GET` | `/api/verify/tasks/{id}` | 任务状态 |
| `GET` | `/api/verify/tasks/{id}/progress` | 任务进度 (0-100) |
| `POST` | `/api/verify/tasks/{id}/cancel` | 取消任务 |
| `GET` | `/api/verify/traces` | 用户所有 Trace（验证反例） |
| `GET` | `/api/verify/traces/{id}` | 单个 Trace |
| `DELETE` | `/api/verify/traces/{id}` | 删除 Trace |

### 模拟相关

| 方法 | 端点 | 说明 |
|------|------|------|
| `POST` | `/api/verify/simulate` | 随机模拟 N 步（不落库） |
| `POST` | `/api/verify/simulate/async` | 异步模拟，返回 `taskId` |
| `GET` | `/api/verify/simulations/tasks/{id}` | 模拟任务状态 |
| `GET` | `/api/verify/simulations/tasks/{id}/progress` | 模拟任务进度 (0-100) |
| `POST` | `/api/verify/simulations/tasks/{id}/cancel` | 取消模拟任务 |
| `POST` | `/api/verify/simulations` | 执行模拟并持久化 |
| `GET` | `/api/verify/simulations` | 用户所有模拟记录（摘要） |
| `GET` | `/api/verify/simulations/{id}` | 单条模拟记录（详情） |
| `DELETE` | `/api/verify/simulations/{id}` | 删除模拟记录 |

说明：当同步模拟线程池（`syncSimulationExecutor`）饱和时，`POST /api/verify/simulate` 会返回 `503 Service Unavailable`。

### 其他端点

| 模块   | 前缀          | 说明                                           |
|--------|---------------|------------------------------------------------|
| 认证   | `/api/auth`   | 注册、登录、登出                               |
| 画布   | `/api/board`  | 设备节点/边/规则/规格/模板/布局的 CRUD + 模板重载（统一入口） |
| AI 助手 | `/api/chat`  | SSE 流式对话 + 会话管理（创建/列表/删除/历史） |

---

## 6. 数据模型

### 验证请求 (VerificationRequestDto)

```json
{
  "devices": [
    {
      "varName": "thermostat_1",
      "templateName": "Thermostat",
      "state": "cool",
      "currentStateTrust": "trusted",
      "variables": [{ "name": "temperature", "value": "22", "trust": "trusted" }],
      "privacies": [{ "name": "temperature", "privacy": "public" }]
    }
  ],
  "rules": [
    {
      "conditions": [{ "deviceName": "thermostat_1", "attribute": "temperature", "relation": ">", "value": "30" }],
      "command": { "deviceName": "fan_1", "action": "fanAuto" }
    }
  ],
  "specs": [
    {
      "id": "spec_1", "templateId": "1", "templateLabel": "AG(A)",
      "aConditions": [{ "deviceId": "fan_1", "targetType": "trust", "key": "FanMode_auto", "relation": "NEQ", "value": "untrusted" }],
      "ifConditions": [], "thenConditions": []
    }
  ],
  "isAttack": true,
  "intensity": 3,
  "enablePrivacy": false
}
```

### 验证结果 (VerificationResultDto)

```json
{
  "safe": false,
  "specResults": [true, false],
  "traces": [
    {
      "id": 1,
      "userId": 100,
      "verificationTaskId": null,
      "violatedSpecId": "spec_2",
      "violatedSpecJson": "{\"id\":\"spec_2\",\"templateId\":\"1\",...}",
      "states": [...]
    }
  ],
  "checkLogs": ["validation warning..."],
  "nusmvOutput": "-- specification AG(...) is false\n..."
}
```

### 模拟轨迹 (SimulationTraceDto)

```json
{
  "id": 1,
  "userId": 100,
  "requestedSteps": 10,
  "steps": 10,
  "states": [{ "stateIndex": 0, "devices": [...], "rules": [], "envVariables": [] }, ...],
  "logs": ["Generating NuSMV model...", "Simulation completed."],
  "nusmvOutput": "NuSMV > ...",
  "requestJson": "{\"devices\":[...],\"rules\":[...],\"steps\":10,\"isAttack\":false,\"intensity\":3,\"enablePrivacy\":false}",
  "createdAt": "2026-02-23T12:00:00"
}
```

### 模拟轨迹摘要 (SimulationTraceSummaryDto)

列表接口返回，不含 states/logs/nusmvOutput 等大字段：

```json
{
  "id": 1,
  "requestedSteps": 10,
  "steps": 10,
  "createdAt": "2026-02-23T12:00:00"
}
```

### 模拟任务状态 (SimulationTaskDto)

用于 `POST /api/verify/simulate/async` 创建的异步任务查询接口：

```json
{
  "id": 101,
  "status": "RUNNING",
  "createdAt": "2026-02-24T09:00:00",
  "startedAt": "2026-02-24T09:00:01",
  "completedAt": null,
  "processingTimeMs": null,
  "requestedSteps": 20,
  "steps": null,
  "simulationTraceId": null,
  "checkLogs": ["Task started", "Executing simulation"],
  "errorMessage": null
}
```

---

## 7. 配置与运行

### 环境要求

- JDK 17+
- MySQL 8.0+
- Redis 7.0+
- NuSMV 2.x (已测试 2.5–2.7，需配置路径)

### 关键配置 (application.yaml)

```yaml
nusmv:
  path: /usr/local/bin/NuSMV    # NuSMV 可执行文件路径
  command-prefix: ""             # 可选：命令前缀（如 docker exec ...）
  timeout-ms: 120000              # 执行超时（毫秒）
  max-concurrent: 6               # NuSMV 全局并发上限（验证+模拟共享）
  acquire-permit-timeout-ms: 10000 # 获取执行许可的等待时长（毫秒）
thread-pool:
  chat:
    core-pool-size: 10
    max-pool-size: 50
    queue-capacity: 200
    await-termination-seconds: 30
  verification-task:
    core-pool-size: 5
    max-pool-size: 20
    queue-capacity: 100
    await-termination-seconds: 60
  sync-verification:
    core-pool-size: 4
    max-pool-size: 4
    queue-capacity: 100
    await-termination-seconds: 30
  sync-simulation:
    core-pool-size: 4
    max-pool-size: 4
    queue-capacity: 100
    await-termination-seconds: 30
  simulation-task:
    core-pool-size: 5
    max-pool-size: 20
    queue-capacity: 100
    await-termination-seconds: 60
```

### 构建与运行

```bash
cd backend
mvn clean package -DskipTests
java -jar target/Iot_Verify-0.0.1-SNAPSHOT.jar
```

---

## 8. 实现状态

| 功能 | 状态 | 实现类 |
|------|------|--------|
| SMV 模型生成 | Done | `SmvGenerator` |
| 前置校验 (P1-P5) | Done | `SmvModelValidator` |
| NuSMV 执行 | Done | `NusmvExecutor` |
| 反例解析 | Done | `SmvTraceParser` |
| Trace 持久化 | Done | `TraceRepository` |
| 同步/异步验证 | Done | `VerificationServiceImpl` |
| 任务取消 | Done | `cancelTask()` API |
| 进度追踪 | Done | Progress API (0-100%) |
| 攻击模式 | Done | `isAttack` + `intensity` |
| 隐私维度 | Done | `enablePrivacy` + `PropertyDimension` |
| 随机模拟 | Done | `SimulationServiceImpl` + `NusmvExecutor.executeInteractiveSimulation()` |
| 模拟结果持久化 | Done | `SimulationTraceRepository` + `SimulationController` |
| 模拟异步任务 | Done | `SimulationTaskPo/Repository` + `/api/verify/simulate/async` + `/api/verify/simulations/tasks/*` |
| 线程池统一配置 | Done | `ThreadPoolConfig` + `ThreadConfig` |
| 输入校验强化 | Done | `SmvDeviceModuleBuilder.validateInternalInitValue()` + `SmvMainModuleBuilder.resolveEnvVarInitValues()` / `validateEnvVarInitValue()` + `SmvSpecificationBuilder.buildVariableCondition()` / `validateApiSignalExists()` / `validateApiBooleanRelation()` + `SpecConditionDto @Pattern` |

---

## License

MIT License

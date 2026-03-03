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
9. [2026-03-03 同步更新（代码与文档）](#9-2026-03-03-同步更新代码与文档)

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
│       ├── RedisTokenBlacklistService.java  # Redis 黑名单（SHA-256 key、fail-open、限流日志）
│       ├── UserServiceImpl.java
│       ├── VerificationServiceImpl.java   # 验证业务逻辑（同步/异步）
│       └── SimulationServiceImpl.java     # 模拟业务逻辑（执行 + 持久化）
├── component/
│   ├── aitool/                            # AI 工具组件（25 工具，7 类别）
│   │   ├── AiTool.java                    # 工具接口
│   │   ├── AiToolManager.java             # 工具管理器
│   │   ├── AiToolResponseHelper.java      # 工具响应辅助
│   │   ├── BoardDataHelper.java           # 画布数据辅助（节点/边/规则/规格聚合）
│   │   ├── board/                         # 画布工具
│   │   │   └── BoardOverviewTool.java     # 画布总览（含 edges）
│   │   ├── node/                          # 节点操作工具
│   │   │   ├── AddNodeTool.java
│   │   │   ├── DeleteNodeTool.java
│   │   │   └── SearchNodeTool.java
│   │   ├── rule/                          # 规则工具
│   │   │   ├── ListRulesTool.java
│   │   │   └── ManageRuleTool.java
│   │   ├── spec/                          # 规格工具
│   │   │   ├── ListSpecsTool.java
│   │   │   └── ManageSpecTool.java
│   │   ├── template/                      # 模板工具
│   │   │   ├── AddTemplateTool.java
│   │   │   ├── DeleteTemplateTool.java
│   │   │   └── ListTemplatesTool.java
│   │   ├── simulation/                    # 模拟工具
│   │   │   ├── SimulateModelTool.java         # 同步模拟
│   │   │   ├── SimulateModelAsyncTool.java
│   │   │   ├── SimulateTaskStatusTool.java
│   │   │   ├── CancelSimulateTaskTool.java
│   │   │   ├── ListSimulationTracesTool.java   # 列出模拟轨迹
│   │   │   ├── GetSimulationTraceTool.java     # 获取模拟轨迹详情
│   │   │   └── DeleteSimulationTraceTool.java  # 删除模拟轨迹
│   │   └── verification/                  # 验证工具
│   │       ├── VerifyModelTool.java       # 同步验证
│   │       ├── VerifyModelAsyncTool.java
│   │       ├── VerifyTaskStatusTool.java
│   │       ├── CancelVerifyTaskTool.java
│   │       ├── ListTracesTool.java        # 列出验证 Traces
│   │       ├── GetTraceTool.java          # 获取验证 Trace 详情
│   │       └── DeleteTraceTool.java       # 删除验证 Trace
│   └── nusmv/                             # ★ NuSMV 核心模块
│       ├── generator/
│       │   ├── SmvGenerator.java           # 协调器：组装完整 SMV 文件
│       │   ├── SmvModelValidator.java      # 前置校验器 (P1-P5)
│       │   ├── SmvBoundsUtils.java         # 共享数值边界工具（resolveEffectiveUpperBound）
│       │   ├── SmvRelationUtils.java       # 共享关系归一化工具（EQ/NEQ/GT/GTE/LT/LTE/IN/NOT_IN）
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
│   ├── DeviceNodePo.java                 # @IdClass(DeviceNodeId) — 复合主键 (id, user_id)
│   ├── DeviceNodeId.java                  # 复合主键类（用户级节点隔离）
│   ├── DeviceEdgePo.java / DeviceEdgeId.java
│   ├── DeviceTemplatePo.java
│   ├── BoardActivePo.java / BoardLayoutPo.java
│   ├── ChatSessionPo.java / ChatMessagePo.java
│   ├── RulePo.java
│   ├── SpecificationPo.java
│   ├── TracePo.java                       # 验证反例轨迹
│   ├── VerificationTaskPo.java            # 异步验证任务（含 progress 列）
│   ├── SimulationTaskPo.java              # 异步模拟任务（含 progress 列）
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
4. 写入临时目录下的 `model.smv`（验证: `nusmv_verify_*`，模拟: `nusmv_sim_*`）
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
5. 读取 `InternalVariables`，并通过 `extractEnvVariables()` 提取环境变量 (`IsInside=false`)
6. `extractSignalVars()` — 从 Transitions 和 APIs 中提取信号变量
7. `extractContents()` — 解析内容（如手机照片）及其隐私属性
8. 合并用户运行时输入（variableValues, instanceVariableTrust, instanceVariablePrivacy）

模板来源与生命周期（重要）：
- 验证/模拟运行时只从当前用户的模板表读取（`DeviceTemplateService.findTemplateByName(userId, templateName)`），不直接读取 `resources` 目录。
- 默认模板来自 `src/main/resources/deviceTemplate/*.json`，在用户注册后自动入库；也可通过 `POST /api/board/templates/reload` 重置（先删除该用户现有模板，再导入默认模板）。
- 若请求中的 `templateName` 在该用户模板中不存在，生成阶段抛出 `SmvGenerationException`（`multipleDevicesFailed`）。
- `loadManifest()` 对 null `templateName` 或 DB 中找不到的模板返回 `null`（调用方 `buildDeviceSmvMap()` 记录 WARN 日志并跳过该设备）。实际错误路径：`BaseException` 直接重抛，JSON 解析失败抛 `MANIFEST_PARSE_ERROR`，其他异常抛 `TEMPLATE_LOAD_ERROR`。
- 创建自定义模板时（`addDeviceTemplate`），会先做 manifest 校验（模式/状态名 NuSMV 合法性），再执行 NuSMV 预检（probe generate），失败返回 400/500。

静态工具方法：
- `cleanStateName(raw)` — 移除分号，然后通过 `sanitizeSmvToken()` 清洗（移除空格、非法字符替换为 `_`、数字开头加 `_` 前缀）
- `sanitizeSmvToken(raw)` — NuSMV 标识符集中清洗函数（模式名/状态名/变量标识）：空格清理、非法字符替换、数字前缀处理、保留字大小写无关转义（含 `W`）
- `findDeviceSmvData(name, map)` — 兼容查找（先按 varName，再按 templateName）
- `findDeviceSmvDataStrict(name, map)` — 严格查找；当 templateName 匹配到多个实例时抛出 `SmvGenerationException`（`AMBIGUOUS_DEVICE_REFERENCE`）
- `toVarName(deviceId)` — 转为安全变量名（含数字前缀与保留字防御）
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

生成 `MODULE main`，是最复杂的构建器（~1740 行），包含：

1. `FROZENVAR intensity: 0..50` — 仅攻击模式
2. `VAR` — 设备实例化 + 环境变量声明
   - 设备实例：`thermostat_1: Thermostat_thermostat1;`
   - 环境变量：`a_temperature: 15..39;`（攻击模式下仅上界扩展，公式 `expansion = range/5 * intensity/50`）
3. `ASSIGN` — 状态转换逻辑（按顺序）
   - `appendStateTransitions()` — 规则驱动 + 模板 Transition 驱动的状态转换（攻击模式下非传感器设备增加最高优先级 `is_attack=TRUE: {所有合法状态}` 劫持分支）
   - `appendEnvTransitions()` — 环境变量 `next()` 转换（含 NaturalChangeRate、设备影响率、边界检查）
   - `appendApiSignalTransitions()` — API 信号变量（基于状态变化检测）
   - `appendTransitionSignalTransitions()` — 模板 Transition 信号变量
   - `appendPropertyTransitions()` — 状态级信任/隐私传播（使用 `PropertyDimension` 枚举统一逻辑）
   - `appendVariablePropertyTransitions()` — 变量级信任/隐私自保持
   - `appendContentPrivacyTransitions()` — IsChangeable=true 的 content 隐私转换（规则命中时设为 `private`，否则自保持）
   - `appendVariableRateTransitions()` — 受影响变量的变化率
   - `appendExternalVariableAssignments()` — 外部变量镜像环境变量（简单赋值，非 next）
   - `appendInternalVariableTransitions()` — 内部变量 `next()` 转换（攻击模式下传感器 `is_attack=TRUE` 时可跳变到扩展后范围内任意值，上界经 `SmvBoundsUtils.resolveEffectiveUpperBound()` 计算）

关键设计：
- 环境变量使用 `a_` 前缀在 main 模块声明，避免跨设备引用问题
- 同名环境变量在 `main` 中只声明一次；`init(a_varName)` 通过 `resolveEnvVarInitValues()` 汇总各设备提供的用户初值（经 `validateEnvVarInitValue()` 校验范围）
- 同名环境变量初值在归一化后若不一致，`resolveEnvVarInitValues()` 抛出 `envVarConflict`
- 对无枚举且无上下界定义的环境变量，`main` 默认声明为 `0..100`；初值仅接受整数，越界会 clamp 到 `0/100`
- `PropertyDimension` 枚举合并了 trust 和 privacy 的重复生成逻辑
- 规则条件中的关系符通过 `normalizeRuleRelation()` 归一化
- 规则条件采用 fail-closed：当条件无法解析（设备不存在、空属性、未知属性、不支持 relation、空 value、`IN/NOT_IN` 空列表）时，整条规则 guard 会被置为 `FALSE`
- 规则与内容相关设备引用（`command.deviceName`、`command.contentDevice`、`conditions[].deviceName`）统一使用严格设备解析；templateName 仅在“唯一匹配”时允许回退，歧义时报错而非静默选择
- 在构建 `next(target.mode)` 的规则条件时，若条件同时读取同一目标设备，则自动降级为当前态读取（`effectiveUseNext=false`），避免产生 `next(x)` 递归定义
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

规格构建的异常策略：
- 一般无效条件（如 relation/key/targetType 不合法）抛 `InvalidConditionException`，并降级生成 `CTLSPEC FALSE -- invalid spec: ...` 占位
- 设备引用歧义（`AMBIGUOUS_DEVICE_REFERENCE`）直接抛 `SmvGenerationException`，不会降级为占位规格

### 4.7 NusmvExecutor — 执行器

`component/nusmv/executor/NusmvExecutor.java`

职责：调用 NuSMV 进程并解析输出（批处理验证 + 交互式随机模拟）。

核心逻辑：
- 构建命令：`NuSMV [extraArgs] model.smv`（支持 `command-prefix` 包装）
- 超时控制：由 `NusmvConfig.timeoutMs` 统一配置（`@Min(100)` 启动校验），通过 YAML `${NUSMV_TIMEOUT_MS:120000}` 支持环境变量覆盖
- 全局并发：`Semaphore` 限流（`nusmv.max-concurrent`），验证与模拟共享 NuSMV 进程并发上限
- 输出解析：逐行匹配 `-- specification ... is true/false`
- 反例提取：false spec 后的文本直到下一个 spec 结果为 counterexample
- 返回 `NusmvResult`，包含 `List<SpecCheckResult>`（每个 spec 的 passed + counterexample）
- 交互模拟：`executeInteractiveSimulation()` 通过 `-int` 执行 `go -> pick_state -r -> simulate -r -k N -> show_traces -> quit`，并过滤 `NuSMV >` 提示符
- 排障产物：验证/模拟在生成 `model.smv` 后会先在同目录写 `request.json`（本次请求快照）；执行器会写 `output.txt`；流程产出结果对象时会写 `result.json`。
- `result.json` 外层 `code/message` 与结果语义对齐，不固定为 `200`：成功 `200/success`，busy 类失败 `503`，模拟日志含 `timed out` 时 `504`，其余失败 `500`。
- 说明：若请求在生成 `model.smv` 之前就失败（例如输入前置校验失败），不会产生 `request.json/result.json`；异步取消若发生在结果对象产出前，可能保留 `request.json` 但没有 `result.json`。

### 4.8 SmvTraceParser — 反例解析

`component/nusmv/parser/SmvTraceParser.java`

将 NuSMV 反例文本解析为 `List<TraceStateDto>`：

- 兼容 `State X.Y:` 与 `-> State: X.Y <-` 两种状态行格式
- `device.var = value` → 匹配到对应 `DeviceSmvData` 的变量/状态/信任/隐私
- `a_varName = value` 及其他裸变量（如 `intensity = value`）→ 环境/全局变量
- 自动补全 `TraceDeviceDto.templateName` 与 `TraceDeviceDto.deviceLabel`
- `trust_` 前缀按类型分流：状态级进入 `trustPrivacy[]`（布尔 trust），变量级写入 `variables[].trust`
- `privacy_` 前缀进入 `privacies[]`（不再混入 `trustPrivacy[]`）
- 过滤内部控制变量：`*_rate`、`*_a`；`is_attack` 保留输出，供前端展示反例路径中哪些设备被攻击
- 增量解析：NuSMV 只输出变化项，解析器通过 `previousModeValuesByDevice` 追踪上一状态
- `finalizeModeStates()` — 用临时 `__mode__*` 变量补全未变化模式，并回填最终 `state/mode`

### 4.9 SmvModelValidator — 前置校验

`component/nusmv/generator/SmvModelValidator.java`

在 SMV 生成前执行的集中式校验器：

| 校验 | 方法 | 说明 |
|------|------|------|
| P1 | `validateTriggerAttributes()` | Trigger.Attribute 合法性 + Trigger.Relation 归一化后合法性（`=`/`!=`/`>`/`>=`/`<`/`<=`） |
| P2 | `validateStartEndStates()` | 多模式 EndState 分号段数 = 模式数 |
| P3 | `validateEnvVarConflicts()` | 同名环境变量跨设备范围一致 |
| P4 | `validatePropertyValues()` | trust/privacy 值合法性（实例值、content privacy、manifest variable trust/privacy、workingState privacy 均须为合法枚举值） |
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

所有端点（除 `/api/auth/register` 和 `/api/auth/login`）需要 JWT 认证：`Authorization: Bearer <token>`

> 注：Spring Security 对 `/api/auth/**` 整体 `permitAll()`，但 `POST /api/auth/logout` 在控制器层通过 `@CurrentUser` 和 `@RequestHeader("Authorization")` 强制要求有效 Token，无 Token 会返回 401。

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

说明：
- 当 syncSimulationExecutor 或 syncVerificationExecutor 饱和时，同步接口会返回 503 Service Unavailable。
- 当同步链路中的 SMV 生成阶段抛出 `SmvGenerationException` 时，会原样透传到全局异常处理，响应 `data.errorCategory` 保留错误类别（如 `AMBIGUOUS_DEVICE_REFERENCE`、`ILLEGAL_TRIGGER_RELATION`），并兼容保留 `[errorCategory] message` 文本格式。
- sync-* 线程池采用小队列（默认 16）以减少长队列导致的排队超时。
- 同步超时后会执行 `future.cancel(true)` 并调用线程池 `purge()`，尽快清理已取消的排队任务。

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
- Redis 7.0+（仅用于 JWT 黑名单；不可用时 fail-open 降级——登录/验证等流程不受阻，但登出撤销语义会失效：黑名单写入/查询失败时已登出的 token 仍可继续使用直至过期）
- NuSMV 2.x (已测试 2.5–2.7，需配置路径)
- `commons-pool2`（Lettuce 连接池，已在 pom.xml 中声明）

### 模板前置条件（重要）

- 后端验证/模拟链路依赖“用户模板表”中的 `DeviceManifest` 数据。
- 新用户注册后会自动导入默认模板；历史用户可调用 `POST /api/board/templates/reload` 重置（删除现有模板后重建默认模板）。
- 在调用 `/api/verify*` 或 `/api/verify/simulate*` 前，应确保请求中的每个 `templateName` 都能在当前用户模板列表中匹配。
- 规则/规格中的设备引用建议使用 `varName`；若使用 `templateName` 且在本次请求中匹配到多个实例，将抛出 `AMBIGUOUS_DEVICE_REFERENCE`。

### 关键配置 (application.yaml)

```yaml
spring.data.redis:
  host: ${REDIS_HOST:localhost}
  port: ${REDIS_PORT:6379}
  password: ${REDIS_PASSWORD:}
  database: ${REDIS_DATABASE:0}
  timeout: 3000ms
  lettuce:
    pool:
      max-active: 16
      max-idle: 8
      min-idle: 2
      max-wait: 2000ms
nusmv:
  path: ${NUSMV_PATH:D:/NuSMV/NuSMV-2.7.1-win64/NuSMV-2.7.1-win64/bin/NuSMV.exe}  # NuSMV 可执行文件路径
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
    core-pool-size: 4
    max-pool-size: 8
    queue-capacity: 40
    await-termination-seconds: 60
  sync-verification:
    core-pool-size: 4
    max-pool-size: 4
    queue-capacity: 16
    await-termination-seconds: 30
  sync-simulation:
    core-pool-size: 4
    max-pool-size: 4
    queue-capacity: 16
    await-termination-seconds: 30
  simulation-task:
    core-pool-size: 4
    max-pool-size: 8
    queue-capacity: 40
    await-termination-seconds: 60
```

### 构建与运行

```bash
cd backend
mvn clean package -DskipTests
java -jar target/Iot-Verify-0.0.1-SNAPSHOT.jar
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
| NuSMV 标识符清洗 | Done | `DeviceSmvDataFactory.sanitizeSmvToken()` — 集中处理空格/非法字符/数字前缀，并对保留字做大小写无关转义（含 `W`）；`toVarName()` 同步防御；`computeIdentifiers()` 对 varName/base/suffix 均做数字前缀守卫和保留字转义 |
| 模板 NuSMV 预检 | Done | `BoardStorageServiceImpl.validateTemplateManifestForNuSmv()` + `runTemplateNuSmvPrecheck()` |
| AI 工具安全强化 | Done | JSON 参数解析 400 错误、`ServiceUnavailableException` 503 错误、内部异常信息不泄露、`AddNodeTool` null-safe 数值解析（`parseDoubleOrNull` / `parseIntOrNull`） |
| AI 工具 Trace 管理 | Done | `GetTraceTool` + `DeleteTraceTool` + `ListSimulationTracesTool` + `GetSimulationTraceTool` + `DeleteSimulationTraceTool` |
| 进度 DB 持久化 | Done | `VerificationTaskPo.progress` + `SimulationTaskPo.progress` — 跨实例可见，三级回退链 |
| 跨实例取消安全 | Done | 原子条件 UPDATE (`WHERE status <> CANCELLED`) + `@Modifying(clearAutomatically = true)` — `completeTaskIfNotCancelled` / `failTaskIfNotCancelled` / `cancelTaskIfStillActive`，消除 TOCTOU 竞态 |
| 设备节点用户隔离 | Done | `DeviceNodeId` 复合主键 `(id, user_id)` — 不同用户可拥有同 ID 节点 |
| 聊天历史过滤 | Done | `ChatServiceImpl.filterFrontendVisibleMessages()` — 前端不显示 tool/tool_calls 消息 |
| 生产安全守卫 | Done | `ProductionSafetyCheck` — 统一基于 `spring.profiles.active`（`prod`/`production`）判断生产环境；若 `jwt.secret` 为 null/空白/不安全默认前缀、`DB_PASSWORD` 仍为不安全默认值、`VOLCENGINE_API_KEY` 为 null/空白/占位值则拒绝启动（`PRODUCTION_MODE` 已移除） |
| 异常处理加固 | Done | `IllegalArgumentException` 掩码内部消息、`IllegalStateException` → 500、`DataIntegrityViolationException` → 409 |
| 线程上下文传播 | Done | `ThreadConfig.TaskDecorator` — 深拷贝 `Authentication`（新建 `UsernamePasswordAuthenticationToken`）+ `UserContextHolder.userId` + MDC 传播 |
| Redis 韧性告警 | Done | `RedisTokenBlacklistService` — 连续失败计数 `AtomicInteger`，每 10 次周期性 ERROR 告警（`% ALERT_THRESHOLD`） |
| 请求校验强化 | Done | `@NotEmpty` devices、`@Size(max=10000)` chat content、`@NotNull @RequestBody` 全量覆盖（`BoardStorageController` 通过类级 `@Validated` 激活） |
| 只读事务优化 | Done | `@Transactional(readOnly = true)` 覆盖 `BoardStorageServiceImpl`、`VerificationServiceImpl`、`SimulationServiceImpl`、`ChatServiceImpl` 全部读方法；`TransactionTemplate` 用于 `VerificationServiceImpl.saveTraces()` 和 `ChatServiceImpl.processStreamChat()` 跨代理边界写入 |
| Entity 索引 | Done | `device_edge(user_id)`、`verification_task(user_id)`、`simulation_task(user_id)` 索引 + `device_templates(user_id, name)` 唯一约束 |
| VerificationTaskDto 一致性 | Done | 添加 `@NoArgsConstructor`、`@AllArgsConstructor`、`@JsonInclude(NON_NULL)` 与 `SimulationTaskDto` 对齐 |
| ArkAiClient 超时 | Done | `volcengine.ark.timeout-minutes` 可配（`ARK_TIMEOUT_MINUTES`，默认 5） |
| JsonUtils 增强 | Done | `JavaTimeModule` 注册、`fromJsonToStringList()` / `fromJsonList()` 新增 |
| JwtUtil 生产告警 | Done | `JwtUtil.@PostConstruct` 在生产 profile 下对默认密钥 WARN 日志（防御纵深，`ProductionSafetyCheck` 硬失败） |
| 异步控制器模式 | Done | `verifyAsync` / `simulateAsync` 返回 `Result<Long>`（不再 `ResponseEntity`）；`TaskRejectedException` 抛 `ServiceUnavailableException` |
| 临时文件保留 | Done | `cleanupTempFile()` 为空操作 — `nusmv_*` 临时目录保留用于事后排障 |
| Surefire JVM 配置 | Done | `pom.xml` 配置 `maven-surefire-plugin`：`-Djdk.attach.allowAttachSelf=true -XX:+EnableDynamicAgentLoading`（JDK 17 Mockito/ByteBuddy 兼容） |

---

## 9. 2026-03-03 同步更新（代码与文档）

本节用于同步最近一轮修复，确保文档描述与当前实现一致。

### NuSMV 生成链路修复

- 标识符清洗增强：
  - `DeviceSmvDataFactory.sanitizeSmvToken()` 现在会对 NuSMV 保留字做大小写无关转义（前缀 `_`），并已包含 `W`（weak-until）。
  - `toVarName(deviceId)` 增加数字前缀防御，并对保留字做一致处理，避免生成非法标识符。
- trust/privacy 一致化与校验增强：
  - `normalizeTrustPrivacy()` 统一 `trim + lowercase`。
  - `SmvModelValidator.validatePropertyValues()` 现在校验：实例值、content privacy、manifest variable trust/privacy、workingState privacy。
  - `checkConflict()` 使用归一化值比较，大小写差异不再误报冲突。
  - `SmvDeviceModuleBuilder` 在输出 `init(trust_*/privacy_*)` 前再次归一化；content privacy 为 `null` 时兜底为 `public` 后再输出。
- A10 数值边界修复闭环：
  - 攻击模式上界扩展公式提取为 `SmvBoundsUtils.resolveEffectiveUpperBound()`，并被设备声明、主模块声明/初值校验、transition clamp 三处复用。
  - `SmvMainModuleBuilder` 在环境变量与内部变量的 `next()` 候选表达式中统一使用 `max(lower, min(upper, expr))` 夹紧（包含 WITH-rate/no-rate 的边界分支与 TRUE 分支）。
  - `SmvBoundsUtils` 对负 `intensity` 做防御性归零；`SmvGenerator.generate()` 入口仍保持 `0..50` clamp。
- `SmvSpecificationBuilder.build()` 新增第 5 参数 `enablePrivacy`；当 privacy 关闭时遇到 privacy spec 会跳过并生成 `CTLSPEC FALSE` 占位（防御纵深，上游 `validateNoPrivacySpecs` 为主守卫）。
- 回归测试补齐（`SmvGeneratorFixesTest`）：
  - `numericEnvTransition_withRate_extremeNcr_boundaryBranchesClamped`
  - `internalVariable_extremeNcr_boundaryBranchesClamped`
  - `smvBoundsUtils_edgeCases`（覆盖 `range=0` 与负强度）

### 后端加固（安全、线程安全、数据完整性）

- **生产安全守卫**：新增 `ProductionSafetyCheck`（`@PostConstruct`）— 当 `spring.profiles.active` 包含 `prod`/`production` 时，若 `jwt.secret` 为 null/空白/不安全默认前缀、`spring.datasource.password`（`DB_PASSWORD`）仍为不安全默认值、`volcengine.ark.api-key`（`VOLCENGINE_API_KEY`）为 null/空白/占位值则拒绝启动；`PRODUCTION_MODE` 环境变量已移除，生产判断统一走 Spring Profile。`JwtUtil.@PostConstruct` 额外在生产 profile 下对默认密钥输出 WARN 日志（防御纵深）；profile 匹配大小写不敏感（`toLowerCase()`）。
- **异常处理加固**：`IllegalArgumentException` → 掩码通用消息 (400)、`IllegalStateException` → "Internal server error" (500)、新增 `DataIntegrityViolationException` → 409 CONFLICT。
- **线程池上下文传播**：`ThreadConfig.TaskDecorator` 深拷贝 `Authentication`（新建 `UsernamePasswordAuthenticationToken` + `new ArrayList<>` authorities）、`UserContextHolder.userId` 和 MDC 上下文到子线程，防止跨任务引用污染。
- **异步任务 TOCTOU 消除**：`completeTask`/`failTask` 改为原子条件 UPDATE（`WHERE status <> CANCELLED`）+ `@Modifying(clearAutomatically = true)`，返回受影响行数（0 = 已取消）。`handleCancellation` 改为 `cancelTaskIfStillActive`（`WHERE status IN (PENDING, RUNNING)`），防止覆写已完成/失败的任务。`TransactionTemplate` 用于 `VerificationServiceImpl.saveTraces()` 和 `ChatServiceImpl.processStreamChat()` 的跨代理边界写入。
- **Redis 韧性**：`RedisTokenBlacklistService` 通过 `AtomicInteger` 追踪连续失败次数，每 10 次周期性 ERROR 告警（`failures % ALERT_THRESHOLD == 0`），不会首次告警后沉默。
- **请求校验强化**：`@NotEmpty` 替代设备列表的 `@NotNull`（拒绝空列表）、`@Size(max=10000)` 限制聊天内容、`@NotNull` 覆盖 `BoardStorageController` 所有 `@RequestBody`（通过类级 `@Validated` 激活）。
- **只读事务**：`@Transactional(readOnly = true)` 覆盖 `BoardStorageServiceImpl`、`VerificationServiceImpl`、`SimulationServiceImpl`、`ChatServiceImpl`（`getUserSessions`、`getHistory`）全部读方法。
- **Entity 索引**：`device_edge(user_id)`、`verification_task(user_id)`、`simulation_task(user_id)` 索引 + `device_templates(user_id, name)` 唯一约束（首次部署前需确认无重复数据）。
- **DTO progress 字段**：`VerificationTaskDto.progress` / `SimulationTaskDto.progress` 暴露到 API（纯增量，前端向后兼容）。
- **VerificationTaskDto 一致性**：添加 `@NoArgsConstructor`、`@AllArgsConstructor`、`@JsonInclude(NON_NULL)` 与 `SimulationTaskDto` 对齐。
- **AI 工具安全**：`AiToolManager.execute()` catch-all 安全网返回通用消息 `"Tool execution failed due to an internal error"`（不泄露 `e.getMessage()`）；`AddTemplateTool` 在 `@PostConstruct` 预建 `tolerantMapper`；`AddNodeTool` 使用 `parseDoubleOrNull()` / `parseIntOrNull()` 替代直接 `asDouble()` / `asInt()`，正确处理 JSON null、非数字字符串、空字符串（均传 `null` 给 `NodeService`，触发默认布局值）。
- **ArkAiClient 超时**：通过 `volcengine.ark.timeout-minutes`（`ARK_TIMEOUT_MINUTES`）可配，默认 5 分钟。
- **JsonUtils**：注册 `JavaTimeModule`；新增 `fromJsonToStringList()` / `fromJsonList()` 辅助方法。
- **DELETE trace 404**：`VerificationServiceImpl.deleteTrace()` 对不存在的 trace 抛出 `ResourceNotFoundException`（原为静默 200）。
- **JwtAuthenticationFilter**：`getUserIdFromToken()` 调用包裹 try-catch — 畸形 token 视为未认证（不抛 500）。
- **异步控制器模式**：`verifyAsync` / `simulateAsync` 返回 `Result<Long>`（不再 `ResponseEntity`）；`TaskRejectedException` 抛 `ServiceUnavailableException`，由 `GlobalExceptionHandler` 统一处理。
- **临时文件保留**：`cleanupTempFile()` 在 `VerificationServiceImpl` 和 `SimulationServiceImpl` 中为空操作 — `nusmv_*` 临时目录保留用于事后排障。
- **Surefire JVM 配置**：`pom.xml` 配置 `maven-surefire-plugin` 添加 `-Djdk.attach.allowAttachSelf=true -XX:+EnableDynamicAgentLoading`，修复 JDK 17 下 Mockito/ByteBuddy `MockMaker` 初始化失败问题。
- **错误信息抑制**：`application.yaml` 设置 `server.error.include-message: never` 和 `include-binding-errors: never`，防止 Spring `/error` 端点泄露内部异常信息。
- **SecurityConfig ObjectMapper**：`SecurityFilterChain` 使用 Spring 管理的 `ObjectMapper`（通过 `@RequiredArgsConstructor` 注入），继承 `JavaTimeModule` 等已注册模块（原为 `new ObjectMapper()` 局部实例）。
- **ArkAiClient ObjectMapper**：通过构造函数注入 Spring 管理的 `ObjectMapper`（原为 `new ObjectMapper()` 字段初始化），确保序列化配置与全局一致。
- **ArkAiClient 解析预检**：`parseToolMessage()` 和 `parseAssistantToolCalls()` 在调用 `objectMapper.readTree()` 前增加 `content.stripLeading().startsWith("{")` 快速预检（容忍前导空白/换行），纯文本消息不再进入 JSON 解析路径（避免异常驱动回退的栈填充开销）；回退路径记录 DEBUG 日志（原为静默 `catch (Exception ignore)`）。

---

## License

MIT License

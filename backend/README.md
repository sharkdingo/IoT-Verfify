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
| Trace 分析 | 反例可视化与分析 |
| AI 助手 | 自然语言设备管理接口（火山引擎） |

---

## 2. 技术栈

- Spring Boot 3.5.7 / Java 21
- MySQL + Redis
- JWT 认证
- NuSMV 模型检测器
- 火山引擎 Ark（AI 助手）

---

## 3. 项目结构

```
src/main/java/cn/edu/nju/Iot_Verify/
├── controller/
│   └── VerificationController.java      # 验证 API 入口
├── service/
│   └── impl/VerificationServiceImpl.java # 验证业务逻辑（同步/异步）
├── component/nusmv/                      # ★ NuSMV 核心模块
│   ├── generator/
│   │   ├── SmvGenerator.java             # 协调器：组装完整 SMV 文件
│   │   ├── SmvModelValidator.java        # 前置校验器 (P1-P5)
│   │   ├── PropertyDimension.java        # Trust/Privacy 维度枚举
│   │   ├── data/
│   │   │   ├── DeviceSmvData.java        # 设备 SMV 数据模型（纯 POJO）
│   │   │   └── DeviceSmvDataFactory.java # DTO + 模板 → DeviceSmvData
│   │   └── module/
│   │       ├── SmvDeviceModuleBuilder.java  # 设备 MODULE 定义
│   │       ├── SmvMainModuleBuilder.java    # main MODULE + ASSIGN 规则
│   │       ├── SmvRuleCommentWriter.java    # 规则 → SMV 注释
│   │       └── SmvSpecificationBuilder.java # CTLSPEC / LTLSPEC 生成
│   ├── executor/
│   │   └── NusmvExecutor.java            # 执行 NuSMV 进程，per-spec 结果解析
│   └── parser/
│       └── SmvTraceParser.java           # 反例文本 → TraceStateDto
├── dto/
│   ├── device/
│   │   ├── DeviceVerificationDto.java    # 验证专用设备数据
│   │   ├── VariableStateDto.java         # 变量状态（name, value, trust）
│   │   └── PrivacyStateDto.java          # 隐私状态（name, privacy）
│   ├── rule/RuleDto.java                 # IFTTT 规则
│   ├── spec/
│   │   ├── SpecificationDto.java         # 验证规格
│   │   └── SpecConditionDto.java         # 规格条件
│   ├── verification/
│   │   ├── VerificationRequestDto.java   # 验证请求
│   │   ├── VerificationResultDto.java    # 验证结果
│   │   └── VerificationTaskDto.java      # 异步任务状态
│   └── trace/
│       ├── TraceDto.java                 # Trace 持久化
│       ├── TraceStateDto.java            # 反例状态
│       ├── TraceDeviceDto.java           # 反例设备
│       ├── TraceVariableDto.java         # 反例变量
│       └── TraceTrustPrivacyDto.java     # 反例信任/隐私
├── exception/
│   └── SmvGenerationException.java       # SMV 生成异常（含工厂方法）
└── configure/
    └── NusmvConfig.java                  # NuSMV 路径/超时配置
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
   - `varName_rate: integer` — 受影响变量的变化率
3. `ASSIGN` — 初始值
   - `init(modeVar)` — 从用户 state 或模板 InitState 确定
   - `init(variable)` — 从用户 variableValues 或模板默认值
   - `init(trust_*)` / `init(privacy_*)` — 从模板默认 + 用户覆盖

### 4.5 SmvMainModuleBuilder — main MODULE

`component/nusmv/generator/module/SmvMainModuleBuilder.java`

生成 `MODULE main`，是最复杂的构建器（~1270 行），包含：

1. `FROZENVAR intensity: 0..50` — 仅攻击模式
2. `VAR` — 设备实例化 + 环境变量声明
   - 设备实例：`thermostat_1: Thermostat_thermostat1;`
   - 环境变量：`a_temperature: 11..39;`（攻击模式下范围扩大 20%）
3. `ASSIGN` — 状态转换逻辑
   - `appendTransitionAssignments()` — 模板 Transitions → `next(device.modeVar)`
   - `appendRuleAssignments()` — IFTTT 规则 → API 信号 + 状态转换
   - `appendPropertyTransitions()` — 信任/隐私传播（使用 `PropertyDimension` 枚举统一逻辑）
   - `appendSensorEnvAssignments()` — 传感器环境变量赋值
   - `appendImpactedVariableAssignments()` — 受影响变量的 rate 计算
   - `appendContentPrivacyAssignments()` — 内容隐私传播

关键设计：
- 环境变量使用 `a_` 前缀在 main 模块声明，避免跨设备引用问题
- `PropertyDimension` 枚举合并了 trust 和 privacy 的重复生成逻辑
- 规则条件中的关系符通过 `normalizeRuleRelation()` 归一化

### 4.6 SmvSpecificationBuilder — 规格生成

`component/nusmv/generator/module/SmvSpecificationBuilder.java`

根据 `SpecificationDto.templateId` 生成 CTL 或 LTL 公式：
- `templateId="6"` → `LTLSPEC G((IF) -> F G(THEN))`
- 其余 → `CTLSPEC` 各模板（AG, AG!, AG→, AG→AG, AG→EF）

条件构建通过 `buildSingleCondition()` 将 `SpecConditionDto` 映射为 SMV 表达式，支持 `IN`/`NOT_IN` 集合运算。

攻击模式下通过 `withAttackConstraint()` 在前件中注入 `intensity<=N`。

无效条件（如找不到设备）抛出 `InvalidConditionException`，生成 `CTLSPEC FALSE` 占位。

### 4.7 NusmvExecutor — 执行器

`component/nusmv/executor/NusmvExecutor.java`

职责：调用 NuSMV 进程并解析输出。

核心逻辑：
- 构建命令：`NuSMV [options] model.smv`
- 超时控制：从环境变量 `NUSMV_TIMEOUT_MS` 读取，默认由 `NusmvConfig` 配置
- 输出解析：逐行匹配 `-- specification ... is true/false`
- 反例提取：false spec 后的文本直到下一个 spec 结果为 counterexample
- 返回 `NusmvResult`，包含 `List<SpecCheckResult>`（每个 spec 的 passed + counterexample）

### 4.8 SmvTraceParser — 反例解析

`component/nusmv/parser/SmvTraceParser.java`

将 NuSMV 反例文本解析为 `List<TraceStateDto>`：

- 按 `State X.Y:` 正则分割状态
- `device.var = value` → 匹配到对应 `DeviceSmvData` 的变量/状态/信任/隐私
- `a_varName = value` → 环境变量
- 增量解析：NuSMV 只输出变化项，解析器通过 `previousModeValuesByDevice` 追踪上一状态
- `finalizeModeStates()` — 补全未变化的模式状态

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
| `GET` | `/api/verify/traces` | 用户所有 Trace |
| `GET` | `/api/verify/traces/{id}` | 单个 Trace |
| `DELETE` | `/api/verify/traces/{id}` | 删除 Trace |

### 其他端点

| 模块 | 前缀 | 说明 |
|------|------|------|
| 认证 | `/api/auth` | 注册、登录、登出 |
| 画布 | `/api/board` | 设备节点和边的 CRUD |
| 设备模板 | `/api/device-templates` | 模板管理 |
| 规则 | `/api/rules` | IFTTT 规则 CRUD |
| 规格 | `/api/specifications` | 验证规格 CRUD |
| AI 助手 | `/api/ai` | SSE 流式对话 |

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
  "traces": [{ "id": 1, "specId": "spec_2", "states": [...] }],
  "checkLogs": ["validation warning..."],
  "nusmvOutput": "-- specification AG(...) is false\n..."
}
```

---

## 7. 配置与运行

### 环境要求

- JDK 21+
- MySQL 8.0+
- Redis 7.0+
- NuSMV 2.6+ (需配置路径)

### 关键配置 (application.yml)

```yaml
nusmv:
  path: /usr/local/bin/NuSMV    # NuSMV 可执行文件路径
  timeout: 60000                 # 执行超时（毫秒）
  options: ""                    # 额外命令行参数
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

---

## License

MIT License

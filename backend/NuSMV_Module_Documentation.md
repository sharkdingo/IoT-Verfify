# NuSMV 模块用户指南

> **最后更新**: 2026年2月25日
> **适用版本**: 统一 VerificationService + Per-Spec 结果 + DTO 拆分 + PropertyDimension + 随机模拟（同步/异步）+ 输入校验强化

本文档面向**使用者**，介绍如何通过 API 进入 NuSMV 验证流程，以及用户输入如何影响最终生成的 SMV 模型。

> **NuSMV 版本要求**: 本系统仅支持 NuSMV 2.x（已测试 2.5–2.7）。输出解析依赖 NuSMV 标准英文输出格式（`-- specification ... is true/false`、`Trace Type: Simulation`、`NuSMV >` 提示符等）。不兼容 nuXmv 或其他变体。
>
> **模板前置条件（重要）**:
> - 运行时模板来源是“当前用户模板表”（DB），不是直接读取 `resources/deviceTemplate`。
> - 默认模板由 `resources/deviceTemplate/*.json` 初始化到 DB（注册后自动导入；`POST /api/board/templates/reload` 为“重置模板”：先删除该用户现有模板，再导入默认模板）。
> - 若请求中的 `templateName` 在当前用户模板中不存在，SMV 生成会失败（`SmvGenerationException`）。
> - 规则/规格里的设备引用优先按 `varName` 解析；按 `templateName` 回退时仅允许唯一匹配，若命中多个实例会抛 `AMBIGUOUS_DEVICE_REFERENCE`。

---

## 目录

1. [快速入门：从 API 到 NuSMV](#1-快速入门从-api-到-nusmv)
2. [请求数据结构](#2-请求数据结构)
3. [NuSMV 管线概览](#3-nusmv-管线概览)
4. [SMV 文件结构与语法](#4-smv-文件结构与语法)
5. [用户输入对 SMV 建模的影响](#5-用户输入对-smv-建模的影响)
6. [完整 SMV 文件示例](#6-完整-smv-文件示例)
7. [规格模板与 CTL/LTL 语法](#7-规格模板与-ctlltl-语法)
8. [Trace 解析与反例结构](#8-trace-解析与反例结构)
9. [校验规则 (P1-P5)](#9-校验规则-p1-p5)
10. [随机模拟功能](#10-随机模拟功能)
11. [API 端点速查](#11-api-端点速查)
12. [逻辑完整性检查清单](#12-逻辑完整性检查清单)

---

## 1. 快速入门：从 API 到 NuSMV

### 伪代码流程

```
前置: 请求中的每个 device.templateName 必须能在当前用户模板表中解析

用户 → POST /api/verify (VerificationRequestDto)
  │
  ├─ VerificationController.verify()
  │     └─ verificationService.verify(userId, devices, rules, specs, isAttack, intensity, enablePrivacy)
  │
  ├─ VerificationServiceImpl.doVerify()
  │     │
  │     ├─ [1] smvGenerator.generate(...)
  │     │     ├─ DeviceSmvDataFactory.buildDeviceSmvMap()   // 用户输入 + 模板 → DeviceSmvData
  │     │     ├─ SmvModelValidator.validate()               // P1-P5 前置校验
  │     │     ├─ SmvRuleCommentWriter.build()               // 规则 → SMV 注释
  │     │     ├─ SmvDeviceModuleBuilder.build()             // 每设备 → MODULE 定义
  │     │     ├─ SmvMainModuleBuilder.build()               // main MODULE + ASSIGN
  │     │     └─ SmvSpecificationBuilder.build()            // specs → CTLSPEC / LTLSPEC
  │     │     → 输出: model.smv 文件
  │     │
  │     ├─ [2] nusmvExecutor.execute(smvFile)
  │     │     → 调用 NuSMV 进程，逐 spec 解析 true/false + counterexample
  │     │
  │     └─ [3] smvTraceParser.parseCounterexampleStates(...)
  │           → 将 NuSMV 反例文本 → List<TraceStateDto>
  │
  └─ 返回 VerificationResultDto { safe, specResults, traces, checkLogs, nusmvOutput }
```

### 同步 vs 异步 vs 模拟

| 方式 | 端点 | 返回值 | 适用场景 |
|------|------|--------|----------|
| 同步验证 | `POST /api/verify` | `VerificationResultDto` | 小规模模型，快速验证 |
| 异步验证 | `POST /api/verify/async` | `taskId (Long)` | 大规模模型，后台执行 |
| 随机模拟 | `POST /api/verify/simulate` | `SimulationResultDto` | 观察模型 N 步随机行为（不落库） |
| 异步模拟 | `POST /api/verify/simulate/async` | `taskId (Long)` | 大规模模拟，后台执行 |
| 模拟并持久化 | `POST /api/verify/simulations` | `SimulationTraceDto` | 模拟并保存记录，支持后续查询/删除 |

异步验证通过 `GET /api/verify/tasks/{id}` / `.../progress` 轮询；异步模拟通过 `GET /api/verify/simulations/tasks/{id}` / `.../progress` 轮询，两个任务都支持 `.../cancel` 取消。

同步 `POST /api/verify` 与 `POST /api/verify/simulate` 会透传 `SmvGenerationException`（包含 `errorCategory`），不会统一降级为通用 internal error。

---

## 2. 请求数据结构

### 2.1 VerificationRequestDto（顶层请求）

```json
{
  "devices": [ DeviceVerificationDto... ],
  "rules":   [ RuleDto... ],
  "specs":   [ SpecificationDto... ],
  "isAttack":      false,       // 是否启用攻击模式
  "intensity":     3,           // 攻击强度 0-50
  "enablePrivacy": false        // 是否启用隐私维度建模
}
```

| 字段 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| `devices` | `List<DeviceVerificationDto>` | 必填 | 参与验证的设备实例列表 |
| `rules` | `List<RuleDto>` | `[]` | IFTTT 规则列表 |
| `specs` | `List<SpecificationDto>` | 必填 | 待验证的安全/隐私规格列表 |
| `isAttack` | `boolean` | `false` | 启用后生成 `is_attack` 冻结变量，扩大传感器范围 |
| `intensity` | `int` | `3` | 攻击预算(0-50)，用于全局 `INVAR intensity<=N` 约束，并按比例影响范围扩展 |
| `enablePrivacy` | `boolean` | `false` | 启用后为状态/变量/内容生成 `privacy_*` 变量 |

### 2.2 DeviceVerificationDto（设备实例）

```json
{
  "varName": "thermostat_1",
  "templateName": "Thermostat",
  "state": "cool",
  "currentStateTrust": "trusted",
  "variables": [
    { "name": "temperature", "value": "22", "trust": "trusted" }
  ],
  "privacies": [
    { "name": "temperature", "privacy": "public" }
  ]
}
```

| 字段 | 类型 | 说明 |
|------|------|------|
| `varName` | `String` | 设备实例变量名，作为 SMV 中的标识符（如 `thermostat_1`） |
| `templateName` | `String` | 设备模板名称；运行时按 `userId + templateName` 从数据库加载 `DeviceManifest`（不直接读 resources） |
| `state` | `String` | 当前状态（如 `cool`），映射到模板的 WorkingStates |
| `currentStateTrust` | `String` | 设备级信任覆盖（`trusted`/`untrusted`） |
| `variables` | `List<VariableStateDto>` | 每个变量的当前值和信任度 |
| `privacies` | `List<PrivacyStateDto>` | 每个状态/变量的隐私覆盖 |

### 2.3 RuleDto（IFTTT 规则）

```json
{
  "conditions": [
    { "deviceName": "thermostat_1", "attribute": "temperature", "relation": ">", "value": "30" }
  ],
  "command": {
    "deviceName": "fan_1",
    "action": "fanAuto",
    "contentDevice": null,
    "content": null
  },
  "ruleString": "IF thermostat_1.temperature>30 THEN fan_1.fanAuto"
}
```

| 字段 | 说明 |
|------|------|
| `conditions[].deviceName` | 触发条件设备引用。解析顺序：先 `varName`，再 `templateName`（仅唯一匹配）。找不到时规则 fail-closed（guard=`FALSE`）；若 `templateName` 匹配多个实例则抛 `AMBIGUOUS_DEVICE_REFERENCE`。 |
| `conditions[].attribute` | 属性名（支持 `state`、mode 名、InternalVariable 名、或 `signal=true` 的 API 名）。当 relation 非空时，attribute 必须解析到 mode/internal variable/API signal 之一，否则 fail-closed。`state` 是保留别名，会根据 value 解析到具体 mode 状态。 |
| `conditions[].relation` | 关系运算符：`EQ`/`NEQ`/`GT`/`GTE`/`LT`/`LTE`/`IN`/`NOT_IN`，归一化为 `=`/`!=`/`>`/`>=`/`<`/`<=`/`in`/`not in`。支持前后空格（如 `" GT "`），`IN`/`NOT_IN` 展开为 `(x=a \| x=b)` / `(x!=a & x!=b)`。若 relation 不在支持集合内，规则条件解析失败（fail-closed）。若 attribute 为 API signal，则 relation 仅支持 `=`/`!=`/`IN`/`NOT_IN`。 |
| `conditions[].value` | 比较值（`IN`/`NOT_IN` 时为逗号/分号/竖线分隔的值列表）。当 relation 非空时 value 必须非空；`IN`/`NOT_IN` 的空列表（如 `" , ; | "`) 视为无效条件并 fail-closed。若 attribute 为 API signal，则 value 必须是 `TRUE`/`FALSE`（或其列表，大小写不敏感）。 |
| `command.deviceName` | 目标设备引用，使用严格解析（先 `varName`，再唯一 `templateName`）。找不到抛 `DEVICE_NOT_FOUND`；歧义抛 `AMBIGUOUS_DEVICE_REFERENCE`。 |
| `command.action` | 触发的 API 名称 |
| `command.contentDevice` | 隐私规则内容来源设备，使用与 `command.deviceName` 相同的严格解析（歧义会抛异常，不会静默绑定）。 |
| `command.content` | 隐私规则：内容名称 |

### 2.4 SpecificationDto（验证规格）

```json
{
  "id": "spec_1",
  "templateId": "1",
  "templateLabel": "AG(A)",
  "aConditions": [
    { "deviceId": "thermostat_1", "targetType": "state", "key": "ThermostatMode", "relation": "NEQ", "value": "cool" }
  ],
  "ifConditions": [],
  "thenConditions": []
}
```

| 字段 | 说明 |
|------|------|
| `templateId` | 规格模板编号，决定 CTL/LTL 公式结构（`"6"` → LTLSPEC，其余 → CTLSPEC） |
| `aConditions` | "A" 部分条件列表 |
| `ifConditions` | "IF" 部分条件列表（前件） |
| `thenConditions` | "THEN" 部分条件列表（后件） |

**SpecConditionDto.targetType 支持的类型（大小写不敏感，后端归一化为小写，DTO 层 `@Pattern` 校验）：**

| targetType | SMV 变量映射 | 示例 |
|------------|-------------|------|
| `state` | `device.{mode} = stateName` | `thermostat_1.ThermostatMode = cool` |
| `variable` | `device.varName` 或 `a_varName`（环境变量） | `thermostat_1.temperature > 30` |
| `api` | `device.{apiName}_a` | `fan_1.fanAuto_a = FALSE`（仅支持 `=`/`!=`/`IN`/`NOT_IN`，值必须为 `TRUE`/`FALSE`） |
| `trust` | `device.trust_{mode}_{state}` | `thermostat_1.trust_ThermostatMode_cool = untrusted` |
| `privacy` | `device.privacy_{mode}_{state}` | `thermostat_1.privacy_ThermostatMode_cool = private` |

**SpecConditionDto.relation 支持（同样会自动去前后空格）：**

- 支持：`EQ`/`NEQ`/`GT`/`GTE`/`LT`/`LTE`/`IN`/`NOT_IN`（归一化为 `=`/`!=`/`>`/`>=`/`<`/`<=`/`in`/`not in`）。
- `api` 类型仅支持：`=`/`!=`/`IN`/`NOT_IN`，且值必须为 `TRUE`/`FALSE`（或其列表）。
- `SpecConditionDto.deviceId` 使用严格设备解析（先 `varName`，再唯一 `templateName`）；若歧义，直接抛 `SmvGenerationException(AMBIGUOUS_DEVICE_REFERENCE)`。
- 不支持的 relation、空白 value、无法解析的 key/targetType 会触发 `InvalidConditionException`，最终该 spec 降级为：
  - `CTLSPEC FALSE -- invalid spec: ...`

---

## 3. NuSMV 管线概览

```
┌─────────────────────────────────────────────────────────────┐
│ SmvGenerator.generate()                                     │
│                                                             │
│  ┌──────────────────────────────────────────────────────┐   │
│  │ DeviceSmvDataFactory.buildDeviceSmvMap()              │   │
│  │  对每个 DeviceVerificationDto:                        │   │
│  │  1. 从 DB 加载 DeviceManifest (模板 JSON)             │   │
│  │  2. 解析 Modes / WorkingStates / Variables / APIs     │   │
│  │  3. 合并用户运行时输入 (state, variables, privacies)   │   │
│  │  → Map<varName, DeviceSmvData>                        │   │
│  └──────────────────────────────────────────────────────┘   │
│                          ↓                                  │
│  ┌──────────────────────────────────────────────────────┐   │
│  │ SmvModelValidator.validate()                         │   │
│  │  P1: Trigger.Attribute 合法性                         │   │
│  │  P2: 多模式 EndState 分号段数匹配                      │   │
│  │  P3: 环境变量跨设备范围冲突                             │   │
│  │  P5: trust/privacy 一致性                             │   │
│  └──────────────────────────────────────────────────────┘   │
│                          ↓                                  │
│  ┌──────────────────────────────────────────────────────┐   │
│  │ 生成 SMV 文本 (按顺序拼接)                             │   │
│  │  1. SmvRuleCommentWriter  → -- 规则注释                │   │
│  │  2. SmvDeviceModuleBuilder → MODULE Device_xxx        │   │
│  │  3. SmvMainModuleBuilder   → MODULE main              │   │
│  │  4. SmvSpecificationBuilder → CTLSPEC / LTLSPEC       │   │
│  └──────────────────────────────────────────────────────┘   │
│                          ↓                                  │
│  写入临时文件 model.smv                                      │
└─────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────┐
│ NusmvExecutor.execute(smvFile)                              │
│  1. 构建命令: NuSMV [extraArgs] model.smv                   │
│  2. 启动进程，读取 stdout                                    │
│  3. 逐行匹配 "-- specification ... is true/false"           │
│  4. 提取每个 false spec 的 counterexample 文本               │
│  → NusmvResult { specResults[], output }                    │
└─────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────┐
│ SmvTraceParser.parseCounterexampleStates()                  │
│  1. 按 "State X.Y:" / "-> State: X.Y <-" 分割反例文本        │
│  2. 解析每行 "device.var = value"                            │
│  3. 映射回 DeviceSmvData 的状态/变量/信任/隐私                │
│  → List<TraceStateDto>                                      │
└─────────────────────────────────────────────────────────────┘
```

失败闭环说明（关键）：

- **模板缺失/模板非法**：在 `DeviceSmvDataFactory.buildDeviceSmvMap()` 阶段失败，直接返回错误，不进入 NuSMV 执行。
- **规则条件无法解析**：规则 guard 置为 `FALSE`（fail-closed），避免“无效条件变无条件触发”。
- **规格条件无法解析**：一般降级为 `CTLSPEC FALSE -- invalid spec: ...`（fail-closed），保持 spec 数量与结果可对齐。
- **设备引用歧义**：不会降级为占位；直接抛 `AMBIGUOUS_DEVICE_REFERENCE`，请求失败并返回明确错误。
- **NuSMV 结果数量与规格数量不一致**：验证结果标记为不安全（fail-closed）。

---

## 4. SMV 文件结构与语法

一个完整的 SMV 文件由以下部分组成：

```smv
-- 规则注释 (SmvRuleCommentWriter)
--IF thermostat_1.temperature>30 THEN fan_1.fanAuto

-- 设备模块定义 (SmvDeviceModuleBuilder) — 每种设备模板一个
MODULE Thermostat_thermostat1
  FROZENVAR                          -- 冻结变量（验证期间不变）
    is_attack: boolean;              -- 仅 isAttack=true 时生成
  VAR                                -- 状态变量
    ThermostatMode: {cool, heat, off};         -- 模式状态
    temperature: 15..35;                        -- 外部变量（由 main 的 a_temperature 映射）
    setCool_a: boolean;                         -- API 信号
    trust_ThermostatMode_cool: {untrusted, trusted};  -- 状态信任
    trust_temperature: {untrusted, trusted};          -- 变量信任
    privacy_ThermostatMode_cool: {private, public};   -- 仅 enablePrivacy
    privacy_temperature: {private, public};           -- 变量隐私
  ASSIGN
    init(ThermostatMode) := cool;    -- 初始状态
    init(setCool_a) := FALSE;
    init(trust_ThermostatMode_cool) := trusted;
    init(trust_temperature) := trusted;
    init(privacy_ThermostatMode_cool) := public;
    init(privacy_temperature) := public;

-- 主模块 (SmvMainModuleBuilder)
MODULE main
  FROZENVAR
    intensity: 0..50;                -- 仅 isAttack=true 时生成
  INVAR intensity <= 3;              -- 全局攻击预算约束
  VAR
    thermostat_1: Thermostat_thermostat1;      -- 设备实例化
    fan_1: Fan_fan1;
    a_temperature: 15..35;              -- 环境变量（a_ 前缀）
  ASSIGN
    -- 状态转换 (攻击劫持优先 + 模板 Transitions)
    next(thermostat_1.ThermostatMode) := case
      thermostat_1.is_attack=TRUE: {cool, heat, off};
      thermostat_1.ThermostatMode = cool & thermostat_1.temperature > 30 & thermostat_1.is_attack=FALSE : heat;
      TRUE : thermostat_1.ThermostatMode;      -- 默认自保持
    esac;
    -- API 信号（基于状态变化检测）
    next(fan_1.fanAuto_a) := case
      fan_1.FanMode!=auto & next(fan_1.FanMode)=auto: TRUE;
      TRUE: FALSE;
    esac;
    -- 信任传播 (PropertyDimension.TRUST)
    next(fan_1.trust_FanMode_auto) := case
      fan_1.is_attack=TRUE: untrusted;
      thermostat_1.temperature > 30 & (thermostat_1.trust_temperature=trusted): trusted;
      thermostat_1.temperature > 30: untrusted;
      TRUE: fan_1.trust_FanMode_auto;         -- 自保持
    esac;

-- 规格 (SmvSpecificationBuilder)
  CTLSPEC AG(thermostat_1.ThermostatMode != off)
  CTLSPEC AG(!(fan_1.FanMode = auto & fan_1.trust_FanMode_auto = untrusted))
  LTLSPEC G((thermostat_1.temperature > 25) -> F G(fan_1.FanMode = auto))
```

### NuSMV 关键语法速查

| 语法 | 含义 | 示例 |
|------|------|------|
| `MODULE name` | 模块定义 | `MODULE Thermostat_t1` |
| `FROZENVAR` | 冻结变量（初始化后不变） | `is_attack: boolean;` |
| `VAR` | 状态变量 | `mode: {on, off};` |
| `ASSIGN` | 赋值块 | `init(x) := 0; next(x) := ...` |
| `init(v) := expr` | 初始值 | `init(mode) := off;` |
| `next(v) := case ... esac` | 状态转移 | 见上方示例 |
| `CTLSPEC` | CTL 时序逻辑规格 | `CTLSPEC AG(p)` |
| `LTLSPEC` | LTL 时序逻辑规格 | `LTLSPEC G(p -> F q)` |
| `AG(p)` | 所有路径全局成立 | 安全性属性 |
| `EF(p)` | 存在路径最终成立 | 可达性属性 |
| `G(p -> F q)` | 全局：p 则最终 q | 活性属性 |

---

## 5. 用户输入对 SMV 建模的影响

### 5.1 isAttack（攻击模式）

当 `isAttack=true` 时，SMV 模型发生以下变化：

**设备模块 (SmvDeviceModuleBuilder)：**
```smv
FROZENVAR
    is_attack: boolean;    -- 每个设备增加冻结攻击标记
```

**主模块 (SmvMainModuleBuilder)：**
```smv
FROZENVAR
    intensity: 0..50;      -- 全局攻击预算变量
INVAR intensity <= 3;      -- 全局预算约束（示例 N=3）

-- 环境变量范围按 intensity 比例扩展（仅上界扩展）
-- expansion = (upper-lower)/5 * intensity/50
-- 例：temperature 原始 15..35，intensity=50 时变为 15..39
VAR
    a_temperature: 15..39;
```

**规格 (SmvSpecificationBuilder)：**
```smv
-- 修复后：规格不再自动注入 intensity<=N
-- 预算约束统一放在 main 的 INVAR 中
CTLSPEC AG(!(fan.state = auto & fan.trust_FanMode_auto = untrusted))
```

### 5.2 intensity（攻击强度）

`intensity`（0-50）在当前实现中有两项作用：

1. **全局预算约束**：在 `main` 模块生成 `INVAR intensity <= N`。
2. **范围扩展比例**：攻击模式下按 `intensity/50` 缩放扩展幅度。

```smv
-- 示例：range = upper - lower = 20
-- intensity = 0   => expansion = 0
-- intensity = 25  => expansion = 2
-- intensity = 50  => expansion = 4
```

### 5.3 enablePrivacy（隐私维度）

当 `enablePrivacy=true` 时：

**设备模块 — 传感器变量隐私：**
```smv
FROZENVAR
    privacy_temperature: {public, private};   -- 传感器的每个变量
```

**设备模块 — 状态隐私：**
```smv
VAR
    privacy_ThermostatMode_cool: {private, public};   -- 每个 (mode, state) 组合
```

**设备模块 — 内容隐私：**
```smv
-- IsChangeable=false 的内容 → FROZENVAR（隐私不可变）
FROZENVAR
    privacy_photo: {public, private};

-- IsChangeable=true 的内容 → VAR（隐私可变）
VAR
    privacy_photo: {public, private};
```

**主模块 — 隐私传播规则：**
```smv
-- 规则触发时，隐私从源设备传播到目标设备
-- guard 使用完整的规则条件（appendRuleConditions），而非简化的 API 信号
-- 例：规则 "IF condition THEN camera.takePhoto(MobilePhone.photo)"
next(camera_1.privacy_photo) := case
    <规则条件>: private;                       -- 规则触发时设为 private
    TRUE : camera_1.privacy_photo;           -- 自保持
esac;
```

**注意：** 当 `enablePrivacy=false` 时，如果 specs 中包含 `targetType="privacy"` 的条件，会抛出 `SmvGenerationException`，因为 `privacy_*` 变量未被声明。

### 5.4 devices（设备实例）

| 用户输入字段 | SMV 影响 |
|-------------|---------|
| `varName` | 决定 SMV 实例变量名（如 `thermostat_1`）和模块名后缀 |
| `templateName` | 从 DB 加载 DeviceManifest，决定模式/状态/变量/转换的完整定义 |
| `state` | 决定 `init(ModeVar)` 的初始值 |
| `currentStateTrust` | 覆盖模板默认的状态信任初始值 |
| `variables[].value` | 决定 `init(varName)` 的初始值 |
| `variables[].trust` | 覆盖变量信任初始值 |
| `privacies[].privacy` | 覆盖隐私初始值（仅 enablePrivacy=true 时有效） |

环境变量初始值补充说明（`IsInside=false`）：

- 同名环境变量在 `main` 中只声明一次（`a_varName`），其 `init(a_varName)` 通过 `resolveEnvVarInitValues()` 汇总各设备的用户输入（每个设备的初值先经 `validateEnvVarInitValue()` 校验范围/枚举合法性）。
- 若多个设备对同名环境变量给出冲突初值（校验/归一化后不一致），`resolveEnvVarInitValues()` 抛出 `envVarConflict`。
- 对”无枚举且无上下界定义”的环境变量，`main` 默认声明为 `0..100`；用户初值仅接受整数，越界会 clamp 到 `0/100`，非数字则忽略该初值。

内部变量初始值补充说明（`IsInside=true`）：

- `SmvDeviceModuleBuilder.validateInternalInitValue()` 对用户传入的 `init()` 值进行校验：枚举变量检查值是否在枚举内（不在则回退首值并 warn）；数值变量检查是否在 `[lower..upper]` 范围内（越界则 clamp 并 warn）；无枚举且无范围的变量不生成 `init()`，保持 NuSMV 非确定初始化。

### 5.5 rules（IFTTT 规则）

规则在 SMV 中体现为多组 `next()` 赋值：

```
用户规则: IF thermostat_1.temperature > 30 THEN fan_1.fanAuto
```

生成的 SMV（假设 fanAuto API: startState=off, endState=auto, signal=true；以下示例假设 `isAttack=false`，攻击模式下会额外追加 `& fan_1.is_attack=FALSE` 条件）：
```smv
-- 1. 状态转换（由规则条件直接驱动，API 的 EndState 决定目标状态）
--    guard = 规则条件 + API startState 约束
next(fan_1.FanMode) := case
    thermostat_1.temperature > 30 & fan_1.FanMode=off : auto;
    TRUE : fan_1.FanMode;
esac;

-- 2. API 信号（基于状态变化检测，非规则条件直接驱动）
--    有 startState 时: guard = 当前状态=startState & next(状态)=endState
--    无 startState 时: guard = 当前状态!=endState & next(状态)=endState
next(fan_1.fanAuto_a) := case
    fan_1.FanMode=off & next(fan_1.FanMode)=auto: TRUE;     -- startState=off
    TRUE: FALSE;
esac;

-- 3. 信任传播（TRUST 维度）
--    guard = 规则条件 & 所有源变量的 trust 都为 trusted（AND 语义）
--    攻击模式下额外增加 is_attack=TRUE → untrusted 优先分支
next(fan_1.trust_FanMode_auto) := case
    fan_1.is_attack=TRUE: untrusted;                          -- 仅 isAttack=true
    thermostat_1.temperature > 30 & (thermostat_1.trust_temperature=trusted): trusted;
    thermostat_1.temperature > 30: untrusted;                 -- 条件满足但源不可信
    TRUE: fan_1.trust_FanMode_auto;                           -- 自保持
esac;

-- 4. 隐私传播（仅 enablePrivacy=true，PRIVACY 维度）
--    guard = 规则条件 & 所有源变量的 privacy 都为 private
next(fan_1.privacy_FanMode_auto) := case
    thermostat_1.temperature > 30 & (thermostat_1.privacy_temperature=private): private;
    TRUE: fan_1.privacy_FanMode_auto;                         -- 自保持
esac;
```

注意：信任传播生成两行——条件满足且源可信时设为 trusted，条件满足但源不可信时设为 untrusted。隐私传播只生成一行（条件满足且源为 private 时设为 private）。

**规则条件解析失败处理（fail-closed）：** 当规则的某个 IF 条件无法解析（例如设备不存在、`attribute` 为空、`relation!=null` 时 attribute 无法匹配任何 mode/internal variable/API signal、relation 不受支持、relation 非空但 value 为空、`IN/NOT_IN` 值列表为空、API signal 的 relation/value 不合法）时，`appendRuleConditions` 会将整条规则的 guard 设为 `FALSE`，使该规则永远不触发。这是 fail-closed 策略——宁可规则不生效，也不让无效条件被静默忽略导致规则变成无条件触发。日志会输出 warn 级别信息指明失败原因。

**`useNext` 递归规避（状态建模关键）：** 在构建 `next(target.mode)` 的 rule guard 时，若条件引用的正是同一目标设备，生成器会将该条件改为读取当前态（`effectiveUseNext=false`），避免产生 `next(x)` 依赖 `next(x)` 的递归定义（NuSMV `recursively defined` 错误）。

### 5.6 SmvMainModuleBuilder 完整转换类型

`MODULE main` 的 `ASSIGN` 块按以下顺序生成各类 `next()` 转换：

| 序号 | 方法名 | 生成内容 | 说明 |
|------|--------|---------|------|
| 1 | `appendStateTransitions()` | `next(device.ModeVar)` | 规则驱动的状态转换 + 模板 Transition 驱动的状态转换。攻击模式下非传感器设备增加最高优先级分支 `is_attack=TRUE: {所有合法状态}`，模拟执行器被劫持 |
| 2 | `appendEnvTransitions()` | `next(a_varName)` | 环境变量的 next() 转换，含 NaturalChangeRate、设备影响率、边界检查。Transition trigger 引用环境变量时使用 `a_<attr>`（仅检查当前设备的 env var，避免跨设备同名冲突） |
| 3 | `appendApiSignalTransitions()` | `next(device.apiName_a)` | API 信号变量，基于状态变化检测（`current!=end & next(mode)=end`） |
| 4 | `appendTransitionSignalTransitions()` | `next(device.transName_t)` | 模板 Transition 信号变量，基于状态变化检测 |
| 5 | `appendPropertyTransitions()` (TRUST) | `next(device.trust_Mode_State)` | 状态级信任传播（含 is_attack 优先分支） |
| 6 | `appendPropertyTransitions()` (PRIVACY) | `next(device.privacy_Mode_State)` | 状态级隐私传播（仅 enablePrivacy=true） |
| 7 | `appendVariablePropertyTransitions()` (TRUST) | `next(device.trust_varName)` | 变量级信任自保持（actuator 的 VAR 变量必须有 next） |
| 8 | `appendVariablePropertyTransitions()` (PRIVACY) | `next(device.privacy_varName)` | 变量级隐私自保持（仅 enablePrivacy=true） |
| 9 | `appendContentPrivacyTransitions()` | `next(device.privacy_contentName)` | IsChangeable=true 的 content 隐私转换：当规则命令引用该 content 时（如 `THEN Facebook.post(MobilePhone.photo)`），规则触发将 content 隐私设为 `private`；否则自保持 |
| 10 | `appendVariableRateTransitions()` | `next(device.varName_rate)` | 受影响变量的变化率，由设备 WorkingState.Dynamics 决定。`_rate` 范围根据模板中实际 ChangeRate 值动态计算（无 Dynamics 时 fallback 为 -10..10） |
| 11 | `appendExternalVariableAssignments()` | `device.varName := a_varName` | 外部变量（IsInside=false）镜像环境变量（简单赋值，非 next）。注意：代码中此方法在 `appendVariableRateTransitions` 之后调用 |
| 12 | `appendInternalVariableTransitions()` | `next(device.varName)` | 内部变量（IsInside=true）的 next() 转换；攻击模式下生成 `is_attack=TRUE: lower..upper` 分支（使用模板原始范围，不含扩展）。Transition trigger 引用同样使用当前设备 env var 检查 |

环境变量 `next()` 转换示例（数值型，有设备影响率）：
```smv
next(a_temperature) :=
case
    -- 有设备影响率时（如 airconditioner.temperature_rate）
    a_temperature=35-(airconditioner.temperature_rate): {toint(a_temperature)-1+airconditioner.temperature_rate, a_temperature+airconditioner.temperature_rate};
    a_temperature>35-(airconditioner.temperature_rate): {35};
    a_temperature=15-(airconditioner.temperature_rate): {a_temperature+airconditioner.temperature_rate, a_temperature+1+airconditioner.temperature_rate};
    a_temperature<15-(airconditioner.temperature_rate): {15};
    TRUE: {a_temperature-1+airconditioner.temperature_rate, a_temperature+airconditioner.temperature_rate, a_temperature+1+airconditioner.temperature_rate};
esac;
```

内部变量攻击扩展：分两处生效——

1. **VAR 声明范围扩展**（`SmvDeviceModuleBuilder.appendInternalVariables`）：仅对传感器设备的数值型内部变量，公式与环境变量相同 `expansion = range/5 * intensity/50`，仅扩展上界。
2. **next() 攻击分支**（`SmvMainModuleBuilder.appendInternalVariableTransitions`）：当 `isAttack=true` 且设备为传感器时，生成 `device.is_attack=TRUE: lower..upper` 分支，使用模板原始范围（不含扩展），允许攻击者将变量设为任意合法值。
3. **执行器状态劫持**（`SmvMainModuleBuilder.appendStateTransitions`）：当 `isAttack=true` 且设备为非传感器（执行器）时，在 `next(device.ModeVar)` 的 case 中生成最高优先级分支 `device.is_attack=TRUE: {所有合法状态}`，允许攻击者将执行器劫持到任意合法状态。该分支优先于规则和模板 Transition，因此被攻击的执行器会绕过正常转换逻辑。由此产生的状态跳变也会触发 API 信号脉冲（`appendApiSignalTransitions` 检测到 `next(mode)=endState`），这是预期行为——被劫持的设备可以产生任意信号。

---

## 6. 完整 SMV 文件示例

以下是一个包含恒温器 + 风扇的场景，启用攻击模式和隐私维度后生成的完整 SMV 文件：

**场景：** 恒温器温度 > 30 时自动开启风扇，验证风扇不会在不可信状态下运行。

**请求参数：** `isAttack=true, intensity=50, enablePrivacy=true`

```smv
--IF thermostat_1.temperature>30 THEN fan_1.fanAuto

MODULE Thermostat_thermostat1
FROZENVAR
	is_attack: boolean;
VAR
	ThermostatMode: {cool, heat, off};
	temperature: 15..35;
	setCool_a: boolean;
	trust_ThermostatMode_cool: {untrusted, trusted};
	trust_ThermostatMode_heat: {untrusted, trusted};
	trust_ThermostatMode_off: {untrusted, trusted};
	trust_temperature: {untrusted, trusted};
	privacy_ThermostatMode_cool: {private, public};
	privacy_ThermostatMode_heat: {private, public};
	privacy_ThermostatMode_off: {private, public};
	privacy_temperature: {private, public};
ASSIGN
	init(is_attack) := {TRUE, FALSE};
	init(ThermostatMode) := cool;
	init(setCool_a) := FALSE;
	init(trust_ThermostatMode_cool) := trusted;
	init(trust_ThermostatMode_heat) := trusted;
	init(trust_ThermostatMode_off) := trusted;
	init(trust_temperature) := trusted;
	init(privacy_ThermostatMode_cool) := public;
	init(privacy_ThermostatMode_heat) := public;
	init(privacy_ThermostatMode_off) := public;
	init(privacy_temperature) := public;

MODULE Fan_fan1
FROZENVAR
	is_attack: boolean;
VAR
	FanMode: {auto, manual, off};
	fanAuto_a: boolean;
	trust_FanMode_auto: {untrusted, trusted};
	trust_FanMode_manual: {untrusted, trusted};
	trust_FanMode_off: {untrusted, trusted};
	privacy_FanMode_auto: {private, public};
	privacy_FanMode_manual: {private, public};
	privacy_FanMode_off: {private, public};
ASSIGN
	init(is_attack) := {TRUE, FALSE};
	init(FanMode) := off;
	init(fanAuto_a) := FALSE;
	init(trust_FanMode_auto) := trusted;
	init(trust_FanMode_manual) := trusted;
	init(trust_FanMode_off) := trusted;
	init(privacy_FanMode_auto) := public;
	init(privacy_FanMode_manual) := public;
	init(privacy_FanMode_off) := public;

MODULE main
FROZENVAR
	intensity: 0..50;
INVAR intensity <= 50;
VAR
	thermostat_1: Thermostat_thermostat1;
	fan_1: Fan_fan1;
	a_temperature: 15..39;
ASSIGN
	init(intensity) := 0 + toint(thermostat_1.is_attack) + toint(fan_1.is_attack);
	-- 状态转换（攻击劫持优先 + 规则条件驱动 + API startState 约束）
	next(thermostat_1.ThermostatMode) := case
		thermostat_1.is_attack=TRUE: {cool, heat, off};
		TRUE: thermostat_1.ThermostatMode;
	esac;
	next(fan_1.FanMode) := case
		fan_1.is_attack=TRUE: {auto, manual, off};
		thermostat_1.temperature > 30 & fan_1.is_attack=FALSE & fan_1.FanMode=off : auto;
		TRUE : fan_1.FanMode;
	esac;
	-- API 信号（基于状态变化检测）
	next(fan_1.fanAuto_a) := case
		fan_1.FanMode!=auto & next(fan_1.FanMode)=auto: TRUE;
		TRUE: FALSE;
	esac;
	next(thermostat_1.setCool_a) := case
		thermostat_1.ThermostatMode!=cool & next(thermostat_1.ThermostatMode)=cool: TRUE;
		TRUE: FALSE;
	esac;
	-- 环境变量 next() 转换（含 NaturalChangeRate 边界检查）
	next(a_temperature) :=
	case
		a_temperature>=35: {a_temperature-1, a_temperature};   -- 上边界：禁止继续上升，允许下降和保持
		a_temperature<=15: {a_temperature, a_temperature+1};   -- 下边界：禁止继续下降，允许上升和保持
		TRUE: {a_temperature-1, a_temperature, a_temperature+1};
	esac;
	-- 信任传播
	next(fan_1.trust_FanMode_auto) := case
		fan_1.is_attack=TRUE: untrusted;
		thermostat_1.temperature > 30 & (thermostat_1.trust_temperature=trusted): trusted;
		thermostat_1.temperature > 30: untrusted;
		TRUE: fan_1.trust_FanMode_auto;
	esac;
	next(fan_1.trust_FanMode_manual) := case
		fan_1.is_attack=TRUE: untrusted;
		TRUE: fan_1.trust_FanMode_manual;
	esac;
	next(fan_1.trust_FanMode_off) := case
		fan_1.is_attack=TRUE: untrusted;
		TRUE: fan_1.trust_FanMode_off;
	esac;
	-- thermostat_1 状态级 trust（攻击优先 + 自保持）
	next(thermostat_1.trust_ThermostatMode_cool) := case
		thermostat_1.is_attack=TRUE: untrusted;
		TRUE: thermostat_1.trust_ThermostatMode_cool;
	esac;
	next(thermostat_1.trust_ThermostatMode_heat) := case
		thermostat_1.is_attack=TRUE: untrusted;
		TRUE: thermostat_1.trust_ThermostatMode_heat;
	esac;
	next(thermostat_1.trust_ThermostatMode_off) := case
		thermostat_1.is_attack=TRUE: untrusted;
		TRUE: thermostat_1.trust_ThermostatMode_off;
	esac;
	-- 变量级 trust（自保持）
	next(thermostat_1.trust_temperature) := thermostat_1.trust_temperature;
	-- 隐私传播
	next(fan_1.privacy_FanMode_auto) := case
		thermostat_1.temperature > 30 & (thermostat_1.privacy_temperature=private): private;
		TRUE: fan_1.privacy_FanMode_auto;
	esac;
	next(fan_1.privacy_FanMode_manual) := fan_1.privacy_FanMode_manual;
	next(fan_1.privacy_FanMode_off) := fan_1.privacy_FanMode_off;
	-- thermostat_1 状态级 privacy（自保持）
	next(thermostat_1.privacy_ThermostatMode_cool) := thermostat_1.privacy_ThermostatMode_cool;
	next(thermostat_1.privacy_ThermostatMode_heat) := thermostat_1.privacy_ThermostatMode_heat;
	next(thermostat_1.privacy_ThermostatMode_off) := thermostat_1.privacy_ThermostatMode_off;
	-- 变量级 privacy（自保持）
	next(thermostat_1.privacy_temperature) := thermostat_1.privacy_temperature;
	-- 外部变量赋值（简单赋值，非 next）
	thermostat_1.temperature := a_temperature;
-- Specifications
	CTLSPEC AG(!(fan_1.FanMode = auto & fan_1.trust_FanMode_auto = untrusted))
	CTLSPEC AG(!(fan_1.FanMode = auto & fan_1.privacy_FanMode_auto = private))
	LTLSPEC G((thermostat_1.temperature > 30) -> F G(fan_1.FanMode = auto))
```

### 6.1 参数组合示例（修复后）

#### 示例 A：`isAttack=true, intensity=0, enablePrivacy=false`

```smv
MODULE main
FROZENVAR
    intensity: 0..50;
INVAR intensity <= 0;
VAR
    ts_1: Sensor_ts1;
ASSIGN
    init(intensity) := 0 + toint(ts_1.is_attack);
```

含义：预算为 0，强制所有设备 `is_attack=FALSE`。

#### 示例 B：`isAttack=true, intensity=25, enablePrivacy=false`

```smv
MODULE Sensor_ts1
FROZENVAR
    is_attack: boolean;
VAR
    temperature: 0..110;   -- 原始 0..100，range=100，expansion=100/5*25/50=10
ASSIGN
    init(is_attack) := {TRUE, FALSE};

MODULE main
FROZENVAR
    intensity: 0..50;
INVAR intensity <= 25;
```

#### 示例 C：`isAttack=true, intensity=50, enablePrivacy=true`

```smv
MODULE Camera_c1
FROZENVAR
    is_attack: boolean;
    privacy_photo: {public, private};
VAR
    trust_Mode_on: {untrusted, trusted};
    privacy_Mode_on: {private, public};
ASSIGN
    init(is_attack) := {TRUE, FALSE};

MODULE main
FROZENVAR
    intensity: 0..50;
INVAR intensity <= 50;
```

#### 示例 D：规格不再注入 `intensity<=N`

```smv
-- 当前行为（修复后）
CTLSPEC AG(!(door_1.LockState = unlocked & door_1.trust_LockState_unlocked = untrusted))

-- 预算约束在 main
INVAR intensity <= 3;
```
---

## 7. 规格模板与 CTL/LTL 语法

`SmvSpecificationBuilder` 根据 `templateId` 选择 CTL 或 LTL 公式结构：

### CTL 规格（templateId != "6"）

| templateId | 名称 | 生成公式 | 语义 |
|-----------|------|---------|------|
| `1` | Always | `CTLSPEC AG(A)` 或 `CTLSPEC AG((IF) -> (THEN))` | A 全局成立；当 aConditions 为空但有 if/then 时生成蕴含形式 |
| `2` | Eventually | `CTLSPEC AF(A)` | A 在所有路径上最终成立 |
| `3` | Never | `CTLSPEC AG !(A)` | A 在所有路径上全局不成立 |
| `4` | Immediate | `CTLSPEC AG((IF) -> AX(THEN))` | IF 成立后下一状态 THEN 立即成立 |
| `5` | Response | `CTLSPEC AG((IF) -> AF(THEN))` | IF 成立后所有路径上 THEN 最终成立 |
| `7` | Safety | `CTLSPEC AG !(A & trust=untrusted & ...)` | 安全性：不可信状态下 A 不应成立（自动注入 trust 和 is_attack 条件） |

### LTL 规格（templateId == "6"）

| templateId | 名称 | 生成公式 | 语义 |
|-----------|------|---------|------|
| `6` | Persistence | `LTLSPEC G((IF) -> F G(THEN))` | 持久性：IF 之后 THEN 最终持久成立 |

### 攻击模式下的规格处理

修复后，`SmvSpecificationBuilder` 不再在规格前件注入 `& intensity<=N`，以避免 vacuity（空真）。

```smv
-- 修复前（旧）
CTLSPEC AG((condition & intensity<=3))

-- 修复后（新）
CTLSPEC AG(condition)
```

攻击预算统一放在 `main` 模块中：

```smv
MODULE main
FROZENVAR
    intensity: 0..50;
INVAR intensity <= 3;
```

### templateId 7（Safety）详解

Safety 规格由 `buildSafetySpec()` 生成，自动为 `aConditions` 中的每个条件注入对应的 trust 和 is_attack 约束：

```smv
-- 输入：aConditions = [{ deviceId: "fan_1", targetType: "state", key: "FanMode", value: "auto" }]
-- isAttack=true 时生成：
CTLSPEC AG !(fan_1.FanMode=auto & fan_1.trust_FanMode_auto=untrusted & fan_1.is_attack=FALSE)

-- isAttack=false 时生成（不含 is_attack 条件，因为 is_attack 变量未声明）：
CTLSPEC AG !(fan_1.FanMode=auto & fan_1.trust_FanMode_auto=untrusted)
```

语义：在所有可达状态中，不应出现"条件 A 成立且对应 trust 为 untrusted"的情况。`is_attack=FALSE` 约束确保只检查非攻击设备的不可信状态。

### 条件构建规则

每个 `SpecConditionDto` 根据 `targetType` 映射为 SMV 表达式：

```
targetType=state    → deviceVarName.ModeName = stateName
targetType=variable → a_varName OP value               (环境变量：key 以 "a_" 开头，或 key 在设备 envVariables 中)
                    → deviceVarName.varName OP value    (内部变量：key 在设备 internalVariables 中)
                    → 若 key 既非环境变量也非内部变量 → InvalidConditionException
targetType=api      → deviceVarName.apiName_a OP TRUE/FALSE（仅支持 =, !=, IN, NOT_IN）
targetType=trust    → deviceVarName.trust_{key} OP value（key 通过 resolvePropertyKey 解析）
targetType=privacy  → deviceVarName.privacy_{key} OP value（key 通过 resolvePropertyKey 解析）
未知 targetType     → InvalidConditionException（fail-closed，不再猜测拼接）
```

多个条件用 `&` 连接。relation 支持 `IN` (值在集合中) 和 `NOT_IN` (值不在集合中)，集合值用逗号分隔。

Safety(`templateId=7`) 的 trust 注入细节：

- 当 `targetType=variable` 且条件写为 `a_varName OP value`（环境变量）时，Safety 注入 trust 使用 `deviceVarName.trust_varName`（去掉 `a_` 前缀），不会生成不存在的 `trust_a_varName`。

Spec 构建的 fail-closed 策略：

- 若条件无法构建（如 relation 不支持、value 为空、key 无法解析、targetType 不支持），该 spec 不会被静默忽略，而是降级为：
  - `CTLSPEC FALSE -- invalid spec: <reason>`
- 若设备引用歧义（`deviceId` 按 `templateName` 命中多个实例），则直接抛 `AMBIGUOUS_DEVICE_REFERENCE`，不降级。

---

## 8. Trace 解析与反例结构

当 NuSMV 报告某个 spec 为 false 时，会输出一个 counterexample（反例路径）。`SmvTraceParser` 将其解析为结构化数据。

### NuSMV 原始反例格式

以下示例与 section 6 的 `isAttack=true, intensity=50, enablePrivacy=true` 场景一致。

```
-- specification AG (...) is false
-- as demonstrated by the following execution sequence
Trace Description: CTL Counterexample
Trace Type: Counterexample
  -> State: 1.1 <-
    thermostat_1.ThermostatMode = cool
    thermostat_1.temperature = 22
    thermostat_1.is_attack = FALSE
    thermostat_1.trust_temperature = trusted
    thermostat_1.privacy_temperature = public
    thermostat_1.trust_ThermostatMode_cool = trusted
    thermostat_1.privacy_ThermostatMode_cool = public
    fan_1.FanMode = off
    fan_1.is_attack = TRUE
    fan_1.fanAuto_a = FALSE
    fan_1.trust_FanMode_auto = trusted
    fan_1.trust_FanMode_off = trusted
    fan_1.privacy_FanMode_auto = public
    fan_1.privacy_FanMode_off = public
    intensity = 1
    a_temperature = 22
  -> State: 1.2 <-
    thermostat_1.temperature = 35
    a_temperature = 35
    fan_1.fanAuto_a = TRUE
  -> State: 1.3 <-
    fan_1.FanMode = auto
    fan_1.fanAuto_a = FALSE
    fan_1.trust_FanMode_auto = untrusted
```

### 解析后的 TraceStateDto 结构

> **注意：** `TraceDeviceDto` 中 `state` 为当前状态值，`mode` 为状态机名称。
> 旧字段 `newState` 已移除，统一使用 `state` + `mode`。反序列化历史 JSON 时通过 `@JsonAlias("newState")` 自动映射。
>
> **过滤规则：** `*_rate` 和 `*_a` 变量被过滤不进入输出；`is_attack` 保留输出。
> `trust_` 前缀分流：匹配 `mode_state` 格式的写入 `trustPrivacy[]`（布尔），其余写入 `variables[].trust`（字符串）。
> `privacy_` 前缀统一写入 `privacies[]`。裸变量（`intensity`、`a_*`）写入 `envVariables[]`。

```json
[
  {
    "stateIndex": 1,
    "envVariables": [
      { "name": "intensity", "value": "1" },
      { "name": "a_temperature", "value": "35" }
    ],
    "devices": [
      {
        "deviceId": "thermostat_1",
        "deviceLabel": "thermostat_1",
        "templateName": "Thermostat",
        "state": "cool",
        "mode": "ThermostatMode",
        "variables": [
          { "name": "temperature", "value": "22", "trust": "trusted" },
          { "name": "is_attack", "value": "FALSE" }
        ],
        "trustPrivacy": [
          { "name": "ThermostatMode_cool", "trust": true }
        ],
        "privacies": [
          { "name": "temperature", "privacy": "public" },
          { "name": "ThermostatMode_cool", "privacy": "public" }
        ]
      },
      {
        "deviceId": "fan_1",
        "deviceLabel": "fan_1",
        "templateName": "Fan",
        "state": "off",
        "mode": "FanMode",
        "variables": [
          { "name": "is_attack", "value": "TRUE" }
        ],
        "trustPrivacy": [
          { "name": "FanMode_auto", "trust": true },
          { "name": "FanMode_off", "trust": true }
        ],
        "privacies": [
          { "name": "FanMode_auto", "privacy": "public" },
          { "name": "FanMode_off", "privacy": "public" }
        ]
      }
    ]
  },
  {
    "stateIndex": 2,
    "devices": [
      {
        "deviceId": "thermostat_1",
        "deviceLabel": "thermostat_1",
        "templateName": "Thermostat",
        "state": "cool",
        "mode": "ThermostatMode",
        "variables": [
          { "name": "temperature", "value": "35" }
        ]
      },
      {
        "deviceId": "fan_1",
        "deviceLabel": "fan_1",
        "templateName": "Fan",
        "state": "off",
        "mode": "FanMode"
      }
    ]
  },
  {
    "stateIndex": 3,
    "devices": [
      {
        "deviceId": "fan_1",
        "deviceLabel": "fan_1",
        "templateName": "Fan",
        "state": "auto",
        "mode": "FanMode",
        "trustPrivacy": [
          { "name": "FanMode_auto", "trust": false }
        ]
      }
    ]
  }
]
```

### 解析逻辑要点

- 兼容 `State X.Y:` 与 `-> State: X.Y <-` 两种状态行格式
- `device.var = value` 格式匹配设备内部变量
- `a_varName = value` 及其他裸变量（如 `intensity = value`）匹配环境/全局变量
- 自动填充 `TraceDeviceDto.templateName` 与 `TraceDeviceDto.deviceLabel`
- 状态名通过 `DeviceSmvData.states` 反向匹配
- `trust_` 前缀分流：状态级写入 `trustPrivacy[]`（`trust` 为布尔），变量级写入 `variables[].trust`
- `privacy_` 前缀写入 `privacies[]`（条目名去掉前缀）
- 内部控制变量 `*_rate`、`*_a` 会被忽略，不进入输出；`is_attack` 保留输出，供前端展示反例路径中哪些设备被攻击
- 多模式设备先用临时 `__mode__*` 变量收集，再在 `finalizeModeStates()` 阶段回填最终 `state/mode`
- 增量解析：只输出变化的变量（NuSMV 只打印变化项）

---

## 9. 校验规则 (P1-P5)

`SmvModelValidator` 在生成 SMV 文本前执行以下校验：

| 编号 | 校验内容 | 失败行为 |
|------|---------|---------|
| P1 | Trigger.Attribute 必须在 modes + internalVariables 中，且 Trigger.Relation 归一化后必须为 `=`/`!=`/`>`/`>=`/`<`/`<=` | 抛出 `illegalTriggerAttribute` / `illegalTriggerRelation` |
| P2 | 多模式设备的 Transition.EndState 分号段数必须等于模式数 | 抛出 `invalidStateFormat` |
| P3 | 同名环境变量（IsInside=false）在不同设备模板中的范围/枚举值必须一致 | 抛出 `envVarConflict` |
| P4 | Transition trigger 引用环境变量（IsInside=false）时，生成阶段自动使用 `a_<attr>` 引用而非 `device.<attr>`，避免引用未声明的设备内部变量 | 生成阶段内联处理（`SmvMainModuleBuilder.appendEnvTransitions` / `appendInternalVariableTransitions`），非前置校验 |
| P5 | 同一 (mode, stateName) 在不同 WorkingState 中的 trust/privacy 值必须一致 | 抛出 `trustPrivacyConflict` |

软性校验（仅 warn，不阻断）：
- 用户传入的变量名不存在于模板中
- 无模式传感器设备传入了 state 参数
- 内部变量 `init()` 值校验（`SmvDeviceModuleBuilder.validateInternalInitValue()`）：枚举值不在枚举内回退首值；数值超范围 clamp；无枚举/无范围的变量不生成 `init()`
- 环境变量 `init()` 值校验（`SmvMainModuleBuilder.validateEnvVarInitValue()`）：枚举值不在枚举内回退首值；数值超范围 clamp（攻击模式下使用扩展后的上界）；非数字则忽略

生成阶段附加校验 / fail-closed（不属于 P1-P5）：

- Rule 条件解析失败（设备不存在、空属性、未知属性、不支持 relation、空 value、`IN/NOT_IN` 空列表、API signal 的 relation/value 不合法等）时，规则 guard 置为 `FALSE`。
- Rule/Command/Spec 设备引用若出现 templateName 歧义，直接抛 `AMBIGUOUS_DEVICE_REFERENCE`（不会 fail-closed）。
- Spec 条件解析失败（不支持 relation、空 value、无法解析 key、不支持 targetType 等）时，降级输出 `CTLSPEC FALSE -- invalid spec: ...`。
- 同名环境变量的用户初值在不同设备间冲突时，抛出 `envVarConflict`。
- 对默认范围 `0..100` 的环境变量，非整数初值会被忽略，越界值会被 clamp。

---

## 10. 随机模拟功能

除了规约验证，系统还支持 NuSMV 交互式随机模拟，用于观察模型在 N 步内的随机行为轨迹。

### 10.1 模拟流程

```
用户 → POST /api/verify/simulate (SimulationRequestDto)
  │
  ├─ SimulationController.simulate()
  │     └─ simulationService.simulate(userId, devices, rules, steps, isAttack, intensity, enablePrivacy)
  │
  ├─ SimulationServiceImpl.doSimulate()
  │     │
  │     ├─ [1] smvGenerator.generate(..., specs=空列表)
  │     │     → 生成不含 CTLSPEC/LTLSPEC 的 model.smv
  │     │
  │     ├─ [2] nusmvExecutor.executeInteractiveSimulation(smvFile, steps)
  │     │     → 以 -int 模式启动 NuSMV，执行:
  │     │        go → pick_state -r → simulate -r -k N → show_traces → quit
  │     │     → 提取 "Trace Type: Simulation" 之后的轨迹文本，过滤 NuSMV 提示符
  │     │
  │     └─ [3] smvTraceParser.parseCounterexampleStates(traceText, deviceSmvMap)
  │           → 复用反例解析器，模拟轨迹格式与反例格式一致
  │
  └─ 返回 SimulationResultDto { states, steps, requestedSteps, nusmvOutput, logs }
```

### 10.2 SimulationRequestDto

```json
{
  "devices": [ DeviceVerificationDto... ],
  "rules":   [ RuleDto... ],
  "steps":         10,          // 模拟步数 (1-100)，默认 10
  "isAttack":      false,
  "intensity":     3,
  "enablePrivacy": false
}
```

与 `VerificationRequestDto` 的区别：无 `specs` 字段（模拟不检查规约），新增 `steps` 控制模拟步数。

### 10.3 SimulationResultDto

```json
{
  "states": [ TraceStateDto... ],   // 初始状态 + N 步，复用 TraceStateDto
  "steps":  3,                      // 实际模拟步数 = states.size() - 1
  "requestedSteps": 10,             // 用户请求的模拟步数
  "nusmvOutput": "...",             // NuSMV 原始输出（截断）
  "logs": [ "Generating...", ... ]  // 执行日志
}
```

> 说明：`steps` 为“实际可解析步数”，计算方式是 `states.size() - 1`。因此它可能小于 `requestedSteps`（例如 NuSMV 轨迹较短或解析后状态为空）。

### 10.4 关键实现细节

| 要点 | 说明 |
|------|------|
| 交互模式 | NuSMV 以 `-int` 参数启动，通过 stdin 管道发送命令 |
| stdin 关闭 | 写完命令后必须关闭 OutputStream，否则 NuSMV 不会退出 |
| stdout/stderr 分离 | 不合并 stderr，独立线程读取，便于区分模型错误 |
| 提示符过滤 | 交互模式输出含 `NuSMV >` 提示符行，提取轨迹时过滤 |
| 空轨迹检测 | 若 `go` 阶段模型有错误，`show_traces` 无输出，返回带 raw output 的错误 |
| 超时保护 | 通过 `syncSimulationExecutor`（`thread-pool.sync-simulation.*`）+ `nusmvConfig.timeoutMs * 2` |
| 过载保护 | 当 `syncSimulationExecutor`（同步模拟）或 `syncVerificationExecutor`（同步验证）饱和时，抛出 `ServiceUnavailableException`，HTTP 返回 `503` |
| 生成异常透传 | 同步 verify/sim 在 `ExecutionException` 解包和内部执行链路中会透传 `SmvGenerationException`，保留 `errorCategory` |
| 同步队列策略 | `syncVerificationExecutor` / `syncSimulationExecutor` 默认使用小队列（16），减少长队列导致的排队超时 |
| 取消回收策略 | 同步请求超时 `future.cancel(true)` 后，会调用线程池 `purge()` 以更快清理已取消的排队任务 |
| 全局并发闸门 | `NusmvExecutor` 使用 `Semaphore` 控制 NuSMV 进程总并发（`nusmv.max-concurrent`），验证与模拟共享 |
| 许可等待超时 | 获取并发许可超时由 `nusmv.acquire-permit-timeout-ms` 控制，超时返回 busy（调用层转换为 `503` 或任务失败） |
| 持久化（可选） | `POST /api/verify/simulate` 不落库；`POST /api/verify/simulations` 执行模拟并持久化到 `simulation_trace` 表，支持后续查询/删除 |
| 调试产物 | `NusmvExecutor` 会将原始输出写到 `output.txt`；验证/模拟在已生成 `model.smv` 且流程产出结果对象时会写 `result.json`（与 `model.smv` 同目录） |
| `result.json` 语义 | `result.json` 外层 `code/message` 不固定 `200`：成功 `200/success`，busy 类失败 `503`，模拟日志命中 `timed out` 时 `504`，其余失败 `500` |
| 失败前置说明 | 若请求在生成 `model.smv` 之前就失败（如输入前置校验失败），不会产生 `result.json` |
| 取消边界说明 | 异步任务在结果对象产出前被取消时，可能不写 `result.json`（例如验证异步在生成 `model.smv` 后、执行前被取消） |
| 临时文件策略 | 当前实现会保留 `model.smv` 临时文件用于排障（不在 finally 中删除） |

---

## 11. API 端点速查

| 方法 | 端点 | 说明 |
|------|------|------|
| `POST` | `/api/verify` | 同步验证，返回 `VerificationResultDto` |
| `POST` | `/api/verify/async` | 异步验证，返回 `taskId` |
| `GET` | `/api/verify/tasks/{id}` | 获取异步验证任务状态 |
| `GET` | `/api/verify/tasks/{id}/progress` | 获取验证任务进度 (0-100) |
| `POST` | `/api/verify/tasks/{id}/cancel` | 取消异步验证任务 |
| `POST` | `/api/verify/simulate` | 随机模拟 N 步（不落库），返回 `SimulationResultDto` |
| `POST` | `/api/verify/simulate/async` | 异步随机模拟，返回 `taskId` |
| `GET` | `/api/verify/simulations/tasks/{id}` | 获取模拟异步任务状态 |
| `GET` | `/api/verify/simulations/tasks/{id}/progress` | 获取模拟任务进度 (0-100) |
| `POST` | `/api/verify/simulations/tasks/{id}/cancel` | 取消模拟异步任务 |
| `POST` | `/api/verify/simulations` | 随机模拟 N 步并持久化，返回 `SimulationTraceDto` |
| `GET` | `/api/verify/simulations` | 获取当前用户所有模拟记录（摘要） |
| `GET` | `/api/verify/simulations/{id}` | 获取单条模拟记录（含完整 states） |
| `DELETE` | `/api/verify/simulations/{id}` | 删除单条模拟记录 |
| `GET` | `/api/verify/traces` | 获取用户所有 Trace |
| `GET` | `/api/verify/traces/{id}` | 获取单个 Trace |
| `DELETE` | `/api/verify/traces/{id}` | 删除 Trace |

所有端点需要 JWT 认证（`Authorization: Bearer <token>`），用户 ID 通过 `@CurrentUser` 注解自动注入。

---

## 12. 逻辑完整性检查清单

下列链路在当前后端实现中是闭合的：

1. **输入约束闭环**：DTO 校验（`@NotNull/@Pattern/@Min/@Max`） + 生成阶段 fail-closed（规则/spec 条件解析失败不会静默放过）。
2. **模板闭环**：目录模板（resources）先入库，运行时按 `userId + templateName` 读取 DB，缺失即失败。
3. **建模闭环**：`DeviceSmvDataFactory` → `SmvModelValidator(P1-P5)` → `SmvDevice/Main/SpecificationBuilder` 产出完整 `model.smv`。
4. **执行闭环**：`NusmvExecutor` 支持批处理验证与交互模拟，含超时、并发闸门、busy 返回、stdout/stderr 处理。
5. **结果闭环（验证）**：per-spec 结果解析、反例解析、trace 持久化、任务状态与进度、同步/异步统一错误语义。
6. **结果闭环（模拟）**：轨迹解析、`steps` 与 `requestedSteps` 对照（`steps = states.size() - 1`，可能小于 `requestedSteps`）、可选持久化、异步任务生命周期管理。
7. **可观测性闭环**：`model.smv` / `output.txt` / `result.json`（验证与模拟主路径）可用于回放与排障，取消早退路径需结合任务状态排查。

仍需依赖的运行前提：

- MySQL、Redis、JWT、NuSMV 可执行路径配置正确。Redis 仅用于 JWT 黑名单（SHA-256 key），不可用时 fail-open 降级（不阻塞登录/验证流程，但登出撤销语义失效——已登出 token 仍可使用直至过期）；需 `commons-pool2` 启用 Lettuce 连接池。
- 当前用户模板已初始化且与前端请求中的 `templateName` 一致。

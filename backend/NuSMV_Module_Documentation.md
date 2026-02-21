# NuSMV 模块用户指南

> **最后更新**: 2026年2月20日
> **适用版本**: 统一 VerificationService + Per-Spec 结果 + DTO 拆分 + PropertyDimension

本文档面向**使用者**，介绍如何通过 API 进入 NuSMV 验证流程，以及用户输入如何影响最终生成的 SMV 模型。

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
10. [API 端点速查](#10-api-端点速查)

---

## 1. 快速入门：从 API 到 NuSMV

### 伪代码流程

```
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

### 同步 vs 异步

| 方式 | 端点 | 返回值 | 适用场景 |
|------|------|--------|----------|
| 同步 | `POST /api/verify` | `VerificationResultDto` | 小规模模型，快速验证 |
| 异步 | `POST /api/verify/async` | `taskId (Long)` | 大规模模型，后台执行 |

异步模式下通过 `GET /api/verify/tasks/{id}` 轮询状态，`GET /api/verify/tasks/{id}/progress` 获取进度百分比 (0-100)。

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
| `templateName` | `String` | 设备模板名称，用于从数据库加载 `DeviceManifest` |
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
| `conditions[].deviceName` | 触发条件的设备变量名 |
| `conditions[].attribute` | 属性名（`state`、变量名、或信号名） |
| `conditions[].relation` | 关系运算符：`EQ`/`NEQ`/`GT`/`GTE`/`LT`/`LTE`，归一化为 `=`/`!=`/`>`/`>=`/`<`/`<=` |
| `conditions[].value` | 比较值 |
| `command.deviceName` | 目标设备变量名 |
| `command.action` | 触发的 API 名称 |
| `command.contentDevice` | 隐私规则：内容来源设备 |
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

**SpecConditionDto.targetType 支持的类型：**

| targetType | SMV 变量映射 | 示例 |
|------------|-------------|------|
| `state` | `device.{mode}_{stateName}` | `thermostat_1.ThermostatMode = cool` |
| `variable` | `device.varName` 或 `a_varName`（环境变量） | `thermostat_1.temperature > 30` |
| `api` | `device.{apiName}_a` | `fan_1.fanAuto_a = TRUE` |
| `trust` | `device.trust_{mode}_{state}` | `thermostat_1.trust_ThermostatMode_cool = untrusted` |
| `privacy` | `device.privacy_{mode}_{state}` | `thermostat_1.privacy_ThermostatMode_cool = private` |

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
│  1. 构建命令: NuSMV [options] model.smv                     │
│  2. 启动进程，读取 stdout                                    │
│  3. 逐行匹配 "-- specification ... is true/false"           │
│  4. 提取每个 false spec 的 counterexample 文本               │
│  → NusmvResult { specResults[], output }                    │
└─────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────┐
│ SmvTraceParser.parseCounterexampleStates()                  │
│  1. 按 "State X.Y:" 分割反例文本                             │
│  2. 解析每行 "device.var = value"                            │
│  3. 映射回 DeviceSmvData 的状态/变量/信任/隐私                │
│  → List<TraceStateDto>                                      │
└─────────────────────────────────────────────────────────────┘
```

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
    trust_temperature: {trusted, untrusted};   -- 传感器变量信任
    privacy_temperature: {public, private};    -- 仅 enablePrivacy=true
  VAR                                -- 状态变量
    ThermostatMode: {cool, heat, off};         -- 模式状态
    temperature: 15..35;                        -- 内部变量
    trust_ThermostatMode_cool: {trusted, untrusted};  -- 状态信任
    privacy_ThermostatMode_cool: {public, private};   -- 仅 enablePrivacy
  ASSIGN
    init(ThermostatMode) := cool;    -- 初始状态
    init(temperature) := 22;
    init(trust_ThermostatMode_cool) := trusted;

-- 主模块 (SmvMainModuleBuilder)
MODULE main
  FROZENVAR
    intensity: 0..50;                -- 仅 isAttack=true 时生成
  INVAR intensity <= 3;              -- 全局攻击预算约束
  VAR
    thermostat_1: Thermostat_thermostat1;      -- 设备实例化
    fan_1: Fan_fan1;
    a_time: 0..23;                   -- 环境变量（a_ 前缀）
  ASSIGN
    -- 状态转换 (来自模板 Transitions)
    next(thermostat_1.ThermostatMode) := case
      thermostat_1.ThermostatMode = cool & thermostat_1.temperature > 30 : heat;
      TRUE : thermostat_1.ThermostatMode;      -- 默认自保持
    esac;
    -- 规则驱动的 API 信号
    next(fan_1.fanAuto_a) := case
      thermostat_1.temperature > 30 : TRUE;
      TRUE : FALSE;
    esac;
    -- 信任传播 (PropertyDimension.TRUST)
    next(fan_1.trust_FanMode_auto) := case
      fan_1.fanAuto_a = TRUE : thermostat_1.trust_temperature;
      TRUE : fan_1.trust_FanMode_auto;         -- 自保持
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
    privacy_ThermostatMode_cool: {public, private};   -- 每个 (mode, state) 组合
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
next(camera_1.privacy_photo) := case
    camera_1.takePhoto_a = TRUE : private;   -- API 触发时设为 private
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

### 5.5 rules（IFTTT 规则）

规则在 SMV 中体现为多组 `next()` 赋值：

```
用户规则: IF thermostat_1.temperature > 30 THEN fan_1.fanAuto
```

生成的 SMV（假设 fanAuto API: startState=off, endState=auto, signal=true）：
```smv
-- 1. 状态转换（由规则条件直接驱动，API 的 EndState 决定目标状态）
--    guard = 规则条件 + API startState 约束
next(fan_1.FanMode) := case
    thermostat_1.temperature > 30 & fan_1.FanMode=off : auto;
    TRUE : fan_1.FanMode;
esac;

-- 2. API 信号（基于状态变化检测，非规则条件直接驱动）
--    guard = 当前状态!=endState & next(状态)=endState
next(fan_1.fanAuto_a) := case
    fan_1.FanMode!=auto & next(fan_1.FanMode)=auto: TRUE;
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

**规则条件解析失败处理（fail-closed）：** 当规则的某个 IF 条件无法解析（设备不存在、属性无法匹配任何 mode/变量/API）时，`appendRuleConditions` 会将整条规则的 guard 设为 `FALSE`，使该规则永远不触发。这是 fail-closed 策略——宁可规则不生效，也不让无效条件被静默忽略导致规则变成无条件触发。日志会输出 warn 级别信息指明哪个设备的哪个属性无法解析。

### 5.6 SmvMainModuleBuilder 完整转换类型

`MODULE main` 的 `ASSIGN` 块按以下顺序生成各类 `next()` 转换：

| 序号 | 方法名 | 生成内容 | 说明 |
|------|--------|---------|------|
| 1 | `appendStateTransitions()` | `next(device.ModeVar)` | 规则驱动的状态转换 + 模板 Transition 驱动的状态转换 |
| 2 | `appendEnvTransitions()` | `next(a_varName)` | 环境变量的 next() 转换，含 NaturalChangeRate、设备影响率、边界检查。Transition trigger 引用环境变量时使用 `a_<attr>`（仅检查当前设备的 env var，避免跨设备同名冲突） |
| 3 | `appendApiSignalTransitions()` | `next(device.apiName_a)` | API 信号变量，基于状态变化检测（`current!=end & next(mode)=end`） |
| 4 | `appendTransitionSignalTransitions()` | `next(device.transName_t)` | 模板 Transition 信号变量，基于状态变化检测 |
| 5 | `appendPropertyTransitions()` (TRUST) | `next(device.trust_Mode_State)` | 状态级信任传播（含 is_attack 优先分支） |
| 6 | `appendPropertyTransitions()` (PRIVACY) | `next(device.privacy_Mode_State)` | 状态级隐私传播（仅 enablePrivacy=true） |
| 7 | `appendVariablePropertyTransitions()` (TRUST) | `next(device.trust_varName)` | 变量级信任自保持（actuator 的 VAR 变量必须有 next） |
| 8 | `appendVariablePropertyTransitions()` (PRIVACY) | `next(device.privacy_varName)` | 变量级隐私自保持（仅 enablePrivacy=true） |
| 9 | `appendContentPrivacyTransitions()` | `next(device.privacy_contentName)` | IsChangeable=true 的 content 隐私自保持 |
| 10 | `appendVariableRateTransitions()` | `next(device.varName_rate)` | 受影响变量的变化率，由设备 WorkingState.Dynamics 决定。`_rate` 范围根据模板中实际 ChangeRate 值动态计算（无 Dynamics 时 fallback 为 -10..10） |
| 11 | `appendExternalVariableAssignments()` | `device.varName := a_varName` | 外部变量（IsInside=false）镜像环境变量（简单赋值，非 next） |
| 12 | `appendInternalVariableTransitions()` | `next(device.varName)` | 内部变量（IsInside=true）的 next() 转换，攻击模式下范围扩展。Transition trigger 引用同样使用当前设备 env var 检查 |

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
	trust_temperature: {trusted, untrusted};
	privacy_temperature: {public, private};
VAR
	ThermostatMode: {cool, heat, off};
	temperature: 15..35;
	trust_ThermostatMode_cool: {trusted, untrusted};
	trust_ThermostatMode_heat: {trusted, untrusted};
	trust_ThermostatMode_off: {trusted, untrusted};
	privacy_ThermostatMode_cool: {public, private};
	privacy_ThermostatMode_heat: {public, private};
	privacy_ThermostatMode_off: {public, private};
ASSIGN
	init(is_attack) := {TRUE, FALSE};
	init(ThermostatMode) := cool;
	init(temperature) := 22;
	init(trust_ThermostatMode_cool) := trusted;
	init(trust_ThermostatMode_heat) := trusted;
	init(trust_ThermostatMode_off) := trusted;
	init(privacy_ThermostatMode_cool) := public;
	init(privacy_ThermostatMode_heat) := public;
	init(privacy_ThermostatMode_off) := public;

MODULE Fan_fan1
FROZENVAR
	is_attack: boolean;
VAR
	FanMode: {auto, manual, off};
	fanAuto_a: boolean;
	trust_FanMode_auto: {trusted, untrusted};
	trust_FanMode_manual: {trusted, untrusted};
	trust_FanMode_off: {trusted, untrusted};
	privacy_FanMode_auto: {public, private};
	privacy_FanMode_manual: {public, private};
	privacy_FanMode_off: {public, private};
ASSIGN
	init(is_attack) := {TRUE, FALSE};
	init(FanMode) := off;
	init(fanAuto_a) := FALSE;
	init(trust_FanMode_auto) := trusted;
	init(trust_FanMode_off) := trusted;
	init(privacy_FanMode_auto) := public;
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
	-- 状态转换（规则条件直接驱动 + API startState 约束）
	next(fan_1.FanMode) := case
		thermostat_1.temperature > 30 & fan_1.FanMode=off : auto;
		TRUE : fan_1.FanMode;
	esac;
	-- API 信号（基于状态变化检测）
	next(fan_1.fanAuto_a) := case
		fan_1.FanMode!=auto & next(fan_1.FanMode)=auto: TRUE;
		TRUE: FALSE;
	esac;
	-- 环境变量 next() 转换（含 NaturalChangeRate 边界检查）
	next(a_temperature) :=
	case
		a_temperature>=35: a_temperature;
		a_temperature<=15: a_temperature;
		TRUE: {a_temperature-1, a_temperature, a_temperature+1};
	esac;
	-- 信任传播
	next(fan_1.trust_FanMode_auto) := case
		fan_1.is_attack=TRUE: untrusted;
		thermostat_1.temperature > 30 & (thermostat_1.trust_temperature=trusted): trusted;
		thermostat_1.temperature > 30: untrusted;
		TRUE: fan_1.trust_FanMode_auto;
	esac;
	-- 隐私传播
	next(fan_1.privacy_FanMode_auto) := case
		thermostat_1.temperature > 30 & (thermostat_1.privacy_temperature=private): private;
		TRUE: fan_1.privacy_FanMode_auto;
	esac;
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
    trust_Mode_on: {trusted, untrusted};
    privacy_Mode_on: {public, private};
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
targetType=variable → deviceVarName.varName OP value  (内部变量)
                    → a_varName OP value               (环境变量)
targetType=api      → deviceVarName.apiName_a = TRUE/FALSE
targetType=trust    → deviceVarName.trust_ModeName_stateName = trusted/untrusted
targetType=privacy  → deviceVarName.privacy_ModeName_stateName = public/private
```

多个条件用 `&` 连接。relation 支持 `IN` (值在集合中) 和 `NOT_IN` (值不在集合中)，集合值用逗号分隔。

---

## 8. Trace 解析与反例结构

当 NuSMV 报告某个 spec 为 false 时，会输出一个 counterexample（反例路径）。`SmvTraceParser` 将其解析为结构化数据。

### NuSMV 原始反例格式

```
-- specification AG (...) is false
-- as demonstrated by the following execution sequence
Trace Description: CTL Counterexample
Trace Type: Counterexample
  -> State: 1.1 <-
    thermostat_1.ThermostatMode = cool
    thermostat_1.temperature = 22
    fan_1.FanMode = off
    fan_1.trust_FanMode_auto = trusted
    a_temperature = 35
  -> State: 1.2 <-
    thermostat_1.temperature = 35
    fan_1.fanAuto_a = TRUE
  -> State: 1.3 <-
    fan_1.FanMode = auto
    fan_1.trust_FanMode_auto = untrusted
```

### 解析后的 TraceStateDto 结构

```json
[
  {
    "stateIndex": 1,
    "devices": [
      {
        "deviceId": "thermostat_1",
        "state": "cool",
        "mode": "ThermostatMode",
        "variables": [
          { "name": "temperature", "value": "22" }
        ],
        "trustPrivacy": [
          { "name": "trust_ThermostatMode_cool", "value": "trusted" }
        ]
      },
      {
        "deviceId": "fan_1",
        "state": "off",
        "mode": "FanMode",
        "variables": [],
        "trustPrivacy": [
          { "name": "trust_FanMode_auto", "value": "trusted" }
        ]
      }
    ]
  },
  {
    "stateIndex": 2,
    "devices": [ ... ]
  }
]
```

### 解析逻辑要点

- 按 `State X.Y:` 模式分割状态
- `device.var = value` 格式匹配设备内部变量
- `a_varName = value` 格式匹配环境变量
- 状态名通过 `DeviceSmvData.states` 反向匹配
- 信任/隐私变量通过 `trust_`/`privacy_` 前缀识别
- 增量解析：只输出变化的变量（NuSMV 只打印变化项）

---

## 9. 校验规则 (P1-P5)

`SmvModelValidator` 在生成 SMV 文本前执行以下校验：

| 编号 | 校验内容 | 失败行为 |
|------|---------|---------|
| P1 | Transition.Trigger.Attribute 必须是合法属性名（模式名/状态名/变量名/信号名/API名） | 抛出 `illegalTriggerAttribute` |
| P2 | 多模式设备的 Transition.EndState 分号段数必须等于模式数 | 抛出 `invalidStateFormat` |
| P3 | 同名环境变量（IsInside=false）在不同设备模板中的范围/枚举值必须一致 | 抛出 `envVarConflict` |
| P5 | 同一 (mode, stateName) 在不同 WorkingState 中的 trust/privacy 值必须一致 | 抛出 `trustPrivacyConflict` |

软性校验（仅 warn，不阻断）：
- 用户传入的变量名不存在于模板中
- 无模式传感器设备传入了 state 参数

---

## 10. API 端点速查

| 方法 | 端点 | 说明 |
|------|------|------|
| `POST` | `/api/verify` | 同步验证，返回 `VerificationResultDto` |
| `POST` | `/api/verify/async` | 异步验证，返回 `taskId` |
| `GET` | `/api/verify/tasks/{id}` | 获取异步任务状态 |
| `GET` | `/api/verify/tasks/{id}/progress` | 获取任务进度 (0-100) |
| `POST` | `/api/verify/tasks/{id}/cancel` | 取消异步任务 |
| `GET` | `/api/verify/traces` | 获取用户所有 Trace |
| `GET` | `/api/verify/traces/{id}` | 获取单个 Trace |
| `DELETE` | `/api/verify/traces/{id}` | 删除 Trace |

所有端点需要 JWT 认证（`Authorization: Bearer <token>`），用户 ID 通过 `@CurrentUser` 注解自动注入。

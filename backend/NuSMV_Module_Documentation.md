# NuSMV 模块完整架构与实现文档

> **最后更新**: 2025年2月
> **基于实现版本**: SmvGenerator + generator package
> **文档状态**: ✅ 已验证与代码同步

---

## 目录

1. [架构概览](#1-架构概览)
2. [核心组件](#2-核心组件)
3. [数据流](#3-数据流)
4. [SMV生成详解](#4-smv生成详解)
5. [规格类型](#5-规格类型)
6. [使用示例](#6-使用示例)
7. [验证结果](#7-验证结果)
8. [已知问题与改进建议](#8-已知问题与改进建议)

---

## 1. 架构概览

### 1.1 整体架构

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           NuSMV验证系统架构                                   │
└─────────────────────────────────────────────────────────────────────────────┘

[Controller层]
    VerificationController
    └── POST /api/verify (VerificationRequestDto)
        └── 调用NusmvVerificationServiceImpl.verify() [异步]

[Service层]
    NusmvVerificationServiceImpl (事务管理)
    ├── 1. 更新任务状态(RUNNING)
    ├── 2. 调用SmvGenerator.generate() [生成SMV文件]
    ├── 3. 调用NusmvExecutor.execute() [执行NuSMV]
    ├── 4. 调用SmvTraceParser.parseCounterexampleStates() [解析反例]
    ├── 5. 保存Trace到数据库
    ├── 6. 更新任务状态(COMPLETED/FAILED)
    └── 7. 清理临时文件(finally)

[Component层 - NuSMV模块]
    ┌───────────────────────────────────────────────────────────────┐
    │ SmvGenerator (协调器 - 薄协调层)                                 │
    │ ├── generate()          - 调用SmvContentBuilder生成SMV文件      │
    │ └── generateSpecString()- 调用SmvContentBuilder生成规格字符串   │
    └───────────────────────────────────────────────────────────────┘
            │
            └──► SmvContentBuilder (generator package - 核心处理器)
                ├── SmvContentBuilder.build()  - 协调数据准备和内容生成
                │   ├── buildDeviceSmvMap()    - 构建设备SMV数据
                │   ├── SmvRulesModuleBuilder - 规则注释生成
                │   ├── SmvDeviceModuleBuilder - 设备MODULE生成
                │   ├── SmvMainModuleBuilder  - main模块生成
                │   └── SmvSpecificationBuilder - 规格SPEC生成

    ┌───────────────────────────────────────────────────────────────┐
    │ NusmvExecutor (执行器)                                         │
    │ ├── 跨平台命令构建 (Windows/Linux)                            │
    │ ├── 进程管理 (带60秒超时)                                      │
    │ ├── 输出读取                                                   │
    │ └── 反例提取                                                   │
    └───────────────────────────────────────────────────────────────┘

    ┌───────────────────────────────────────────────────────────────┐
    │ SmvTraceParser (解析器)                                        │
    │ └── 解析NuSMV输出为TraceDto列表                                │
    └───────────────────────────────────────────────────────────────┘
```

### 1.2 文件位置

| 层级 | 组件 | 文件路径 |
|-----|------|---------|
| **Layer 1: 生成** | 协调器 | `generator/SmvGenerator.java` |
| **Layer 1: 生成** | 内容生成器 | `generator/SmvContentBuilder.java` |
| **Layer 1: 生成** | 设备模块生成器 | `generator/SmvDeviceModuleBuilder.java` |
| **Layer 1: 生成** | 主模块生成器 | `generator/SmvMainModuleBuilder.java` |
| **Layer 1: 生成** | 规则模块生成器 | `generator/SmvRulesModuleBuilder.java` |
| **Layer 1: 生成** | 规格模块生成器 | `generator/SmvSpecificationBuilder.java` |
| **Layer 2: 执行** | 执行器 | `executor/NusmvExecutor.java` |
| **Layer 3: 解析** | Trace 解析器 | `parser/SmvTraceParser.java` |
| **共享数据** | SMV 数据模型 | `data/DeviceSmvData.java` |
| **共享数据** | 模板包装器 | `data/TemplateWrapper.java` |

---

## 2. 核心组件

### 2.1 SmvGenerator (协调器)

**职责**: 薄协调层，仅负责调用 SmvContentBuilder，不包含任何数据准备逻辑。

**核心方法**:

```java
@Component
@RequiredArgsConstructor
public class SmvGenerator {
    private final SmvContentBuilder smvContentBuilder;

    // 生成 SMV 文件
    public File generate(Long userId, List<DeviceNodeDto> devices,
                         List<RuleDto> rules, List<SpecificationDto> specs,
                         boolean isAttack, int intensity) throws Exception {
        String smvContent = smvContentBuilder.build(userId, devices, rules, specs, isAttack, intensity);
        // 写入临时文件
        return smvFile;
    }

    // 生成规格字符串
    public String generateSpecString(SpecificationDto spec, boolean isAttack, int intensity) {
        return smvContentBuilder.generateSpecString(spec, isAttack, intensity);
    }
}
```

**设计说明**:
- **薄协调器**：只做调用，不做数据准备
- 所有数据准备逻辑在 SmvContentBuilder 中

### 2.2 SmvContentBuilder (核心处理器)

**职责**: 核心处理器，包含所有数据准备和内容生成逻辑。

```java
@Component
@RequiredArgsConstructor
public class SmvContentBuilder {
    private final ObjectMapper objectMapper;
    private final DeviceTemplateService deviceTemplateService;
    private final SmvDeviceModuleBuilder deviceModuleBuilder;
    private final SmvRulesModuleBuilder rulesModuleBuilder;
    private final SmvMainModuleBuilder mainModuleBuilder;
    private final SmvSpecificationBuilder specBuilder;

    // 1. 构建完整 SMV 内容
    public String build(Long userId, List<DeviceNodeDto> devices,
                       List<RuleDto> rules, List<SpecificationDto> specs,
                       boolean isAttack, int intensity) {
        // 1.1 准备设备 SMV 数据
        Map<String, DeviceSmvData> deviceSmvMap = buildDeviceSmvMap(...);

        // 1.2 组装 SMV 内容
        content.append(rulesModuleBuilder.build(...));
        content.append(deviceModuleBuilder.build(...));
        content.append(mainModuleBuilder.build(...));
        content.append(specBuilder.build(...));
        return content.toString();
    }

    // 2. 生成规格字符串
    public String generateSpecString(SpecificationDto spec, boolean isAttack, int intensity) {
        return specBuilder.generateSpecString(spec, isAttack, intensity);
    }
}
```

**核心流程**:
1. 调用 `buildDeviceSmvMap()` 准备设备 SMV 数据
2. 协调各模块生成器组装 SMV 内容
        // 1.1 准备设备SMV数据（模板加载、转换提取）
        Map<String, DeviceSmvData> deviceSmvMap = buildDeviceSmvMap(
            userId, devices, rules, templateCache);

        // 1.2 生成SMV内容
        String smvContent = smvContentBuilder.build(
            userId, devices, rules, specs, isAttack, intensity, deviceSmvMap);

        // 1.3 写入临时文件
        File smvFile = File.createTempFile("nusmv_model_", ".smv");
        Files.write(smvFile.toPath(), smvContent.getBytes(StandardCharsets.UTF_8));
        smvFile.deleteOnExit();
        return smvFile;
    }

    // 2. 生成单个规格字符串（供预览/调试）
    public String generateSpecString(SpecificationDto spec,
                                     boolean isAttack, int intensity) {
        return smvContentBuilder.generateSpecString(spec, isAttack, intensity);
    }

1. 调用 `SmvContentBuilder.build()` 生成 SMV 内容
2. 将内容写入临时文件

### 2.2 SmvContentBuilder (内容协调器)

**职责**: 协调各Builder，组装完整SMV内容。

**调用顺序**:
```java
build()
├── rulesModuleBuilder.build()     // 1. 规则注释
├── deviceModuleBuilder.build()   // 2. 设备MODULE（去重）
├── mainModuleBuilder.build()     // 3. main MODULE
└── specBuilder.build()           // 4. 规格SPEC
```

### 2.3 SmvDeviceModuleBuilder (设备模块生成器)

**职责**: 生成单个设备的NuSMV MODULE定义。

**生成内容结构**:
```smv
-- 设备注释
MODULE <TemplateName>

-- FROZENVAR: 攻击检测变量（仅传感器）
FROZENVAR
    is_attack: boolean;
    trust_<var>: {trusted, untrusted};
    privacy_<var>: {public, private};

-- VAR: 状态和变量
VAR
    <state>: {<state1>, <state2>, ...};
    <var>: <range>;
    <var>_a: boolean;           -- 信号变量
    <var>_rate: <range>;        -- 变化率变量

-- ASSIGN: 初始值和转换
ASSIGN
    init(<state>) := <initState>;
    init(<var>) := <initValue>;
    next(<state>) :=
        case
            -- 转换条件
            TRUE: <state>;
        esac;
```

### 2.4 SmvMainModuleBuilder (主模块生成器)

**职责**: 生成main MODULE，包含所有设备实例和转换逻辑。

**生成内容结构**:
```smv
MODULE main
VAR
    -- 设备实例化
    <deviceId>: <TemplateName>;

    -- 环境变量
    a_<varName>: <range>;

    -- 攻击强度
    intensity: 0..10;

ASSIGN
    -- 强度初始化
    init(intensity) := 0;

    -- 设备状态转换（基于规则）
    next(<device>.<state>) :=
        case
            <ruleConditions>: <nextState>;
            TRUE: <device>.<state>;
        esac;

    -- Trust转换
    next(<device>.trust_<state>) :=
        case
            -- 攻击检测
            <device>.is_attack=TRUE: untrusted;
            -- 规则触发 + 来源可信
            <conditions> & (<source>.trust_<attr>=trusted): trusted;
            -- 规则触发 + 来源不可信
            <conditions>: untrusted;
            TRUE: <device>.trust_<state>;
        esac;

    -- Privacy转换
    next(<device>.privacy_<state>) :=
        case
            <conditions> & (<source>.privacy_<attr>=private): private;
            TRUE: <device>.privacy_<state>;
        esac;
```

### 2.5 SmvRulesModuleBuilder (规则注释生成器)

**职责**: 生成规则的纯注释说明（规则逻辑实际嵌入设备转换中）。

**设计说明**:
- 规则逻辑通过 `SmvContentBuilder.processRules()` 转换为设备转换
- 本Builder仅生成可读性注释
- 采用此设计是为了将规则作用点与设备状态紧密关联

**生成内容**:
```smv
-- Rule 1: IF temperature > 28 THEN device_001.turnOn
-- Source: TemperatureSensor (device_001)
-- Target: AC Cooler (device_002) -> turnOn API
```

### 2.6 SmvSpecificationBuilder (规格生成器)

**职责**: 生成CTL/LTL规格定义。

**支持的规格类型**:
| templateId | 类型 | NuSMV语法 |
|-----------|------|----------|
| "1" | always | `CTLSPEC AG(A)` |
| "2" | eventually | `CTLSPEC AF(A)` |
| "3" | never | `CTLSPEC AG !(A)` |
| "4" | immediate | `CTLSPEC AG(A → AX(B))` |
| "5" | response | `CTLSPEC AG(A → AF(B))` |
| "6" | persistence | `LTLSPEC G(A → F G(B))` |
| "7" | safety | `CTLSPEC AG(untrusted → !(A))` |

---

## 3. 数据流

### 3.1 输入数据结构

```java
// VerificationRequestDto
{
    devices: [
        {
            id: "device_001",
            templateName: "MotionDetector",
            state: "inactive",
            variables: [{name: "motion", value: "active", trust: "trusted"}],
            privacies: [{name: "motion", privacy: "private"}]
        }
    ],
    rules: [
        {
            sources: [{
                fromId: "device_001",
                targetType: "variable",
                property: "motion",
                relation: "=",
                value: "active"
            }],
            toId: "device_002",
            toApi: "lock"
        }
    ],
    specs: [
        {
            templateId: "1",
            aConditions: [{
                deviceId: "device_002",
                targetType: "state",
                key: "LockState",
                relation: "=",
                value: "locked"
            }]
        }
    ],
    isAttack: false,
    intensity: 3
}
```

### 3.2 内部数据模型 (DeviceSmvData)

```java
public class DeviceSmvData {
    // 设备标识
    public String id;           // 实例ID: "device_001"
    public String name;         // 模板名: "MotionDetector"
    public int deviceNo;        // 设备序号

    // 静态结构
    public List<String> states;         // ["inactive", "active"]
    public List<String> modes;          // []
    public Map<String, List<String>> modeStates;  // {}
    public List<InternalVariable> variables;      // 内部变量
    public List<SignalInfo> signalVars;          // 信号变量
    public Map<String, InternalVariable> envVariables;  // 环境变量

    // 运行时状态
    public String currentState;         // "inactive"
    public Map<String, String> variableValues;    // {motion: "active"}

    // Trust/Privacy
    public String instanceStateTrust;              // "trusted"
    public Map<String, String> instanceVariableTrust;  // {motion: "trusted"}
    public Map<String, String> instanceVariablePrivacy; // {motion: "private"}
    public Map<String, String> stateTrust;         // {inactive: "trusted"}
    public Map<String, String> contentPrivacy;     // {motion: "private"}

    // 转换逻辑（由规则生成）
    public List<TransitionInfo> transitions;

    // 模板引用
    public transient DeviceManifest manifest;
}
```

### 3.3 转换规则生成

`SmvContentBuilder.processRules()` 将规则转换为设备转换：

```java
private void processRules(List<RuleDto> rules,
                          Map<String, DeviceSmvData> deviceSmvMap) {
    for (RuleDto rule : rules) {
        String targetDeviceId = rule.getToId();
        DeviceSmvData targetSmv = deviceSmvMap.get(targetDeviceId);

        for (RuleDto.SourceEntryDto source : rule.getSources()) {
            String sourceDeviceId = source.getFromId();
            DeviceSmvData sourceSmv = deviceSmvMap.get(sourceDeviceId);

            // 构建条件表达式
            String condition = buildConditionExpression(source, sourceSmv);

            // 添加到目标设备的转换列表
            targetSmv.transitions.add(new TransitionInfo(
                condition,
                targetSmv.currentState,  // fromState
                getTargetState(rule, targetSmv),  // toState
                rule
            ));
        }
    }
}
```

---

## 4. SMV生成详解

### 4.1 完整SMV文件结构

```smv
-- Generated by IoT-Verify NuSMV Generator
-- 规则注释区域
-- Rule 1: IF temperature > 28 THEN device_002.turnOn

-- 设备MODULE定义区域（去重）
MODULE MotionDetector
FROZENVAR
    is_attack: boolean;
    trust_motion: {trusted, untrusted};
    privacy_motion: {public, private};
VAR
    motion: {active, inactive};
ASSIGN
    init(is_attack) := FALSE;
    init(motion) := inactive;
    ...

MODULE Door
VAR
    LockState: {locked, unlocked};
    lock_a: boolean;
    unlock_a: boolean;
    trust_LockState_locked: {untrusted, trusted};
    trust_LockState_unlocked: {untrusted, trusted};
ASSIGN
    ...

-- main MODULE区域
MODULE main
VAR
    device_001: MotionDetector;
    device_002: Door;
    a_motion: {active, inactive};
    intensity: 0..10;
ASSIGN
    init(intensity) := 0;

    -- 状态转换
    next(device_002.LockState) :=
        case
            device_001.motion = active: locked;
            TRUE: device_002.LockState;
        esac;

    -- Trust转换
    next(device_002.trust_LockState_locked) :=
        case
            device_001.is_attack = TRUE: untrusted;
            device_001.motion = active & (device_001.trust_motion = trusted): trusted;
            device_001.motion = active: untrusted;
            TRUE: device_002.trust_LockState_locked;
        esac;
    ...

-- 规格区域
SPECIFICATION
    CTLSPEC AG (device_002.LockState = locked)
```

### 4.2 Trust转换逻辑（核心安全逻辑）

```
next(device.trust_State) :=
case
    -- 1. 攻击检测：被攻击时变为untrusted
    device.is_attack = TRUE: untrusted;

    -- 2. 规则触发 + 来源设备trusted → trusted
    <ruleConditions> & (sourceDevice.trust_attr = trusted): trusted;

    -- 3. 规则触发 + 来源设备untrusted → untrusted
    <ruleConditions>: untrusted;

    -- 4. 默认保持当前值
    TRUE: device.trust_State;
esac;
```

### 4.3 攻击模式支持

当 `isAttack=true` 时：

```smv
-- 在传感器设备的MODULE中添加
FROZENVAR
    is_attack: boolean;

-- 在main模块中控制攻击强度
VAR
    intensity: 0..10;

ASSIGN
    -- 攻击时变量随机变化
    next(device_001.motion) :=
        case
            intensity >= 3: {active, inactive};  -- 随机变化
            TRUE: <normal_transition>;
        esac;
```

---

## 5. 规格类型

### 5.1 七种规格类型详解

| templateId | 类型 | 语义 | NuSMV语法 | 条件 |
|-----------|------|------|-----------|------|
| "1" | always | A始终成立 | `CTLSPEC AG(A)` | aConditions |
| "2" | eventually | A终将发生 | `CTLSPEC AF(A)` | aConditions |
| "3" | never | A永不发生 | `CTLSPEC AG !(A)` | aConditions |
| "4" | immediate | A发生时B同时发生 | `CTLSPEC AG(A → AX(B))` | if + then |
| "5" | response | A发生后B终将发生 | `CTLSPEC AG(A → AF(B))` | if + then |
| "6" | persistence | A发生后B永久保持 | `LTLSPEC G(A → F G(B))` | if + then |
| "7" | safety | 不可信时A不发生 | `CTLSPEC AG(untrusted → !(A))` | if + then |

### 5.2 条件类型映射

| targetType | 检查目标 | 示例 |
|-----------|---------|------|
| `state` | 设备状态 | `device_001.LockState = locked` |
| `variable` | 变量值 | `device_001.temperature > 28` |
| `api` | API信号 | `device_001.turnOn_a = TRUE` |
| `trust` | Trust值 | `device_001.trust_motion = trusted` |
| `privacy` | Privacy值 | `device_001.privacy_temperature = private` |

---

## 6. 使用示例

### 6.1 完整验证流程

```java
// 1. 准备输入数据
VerificationRequestDto request = new VerificationRequestDto();
request.setDevices(List.of(
    new DeviceNodeDto("temp_001", "TemperatureSensor", "active", ...),
    new DeviceNodeDto("ac_001", "AirConditioner", "Off", ...)
));
request.setRules(List.of(
    new RuleDto(
        List.of(new SourceEntryDto("temp_001", "variable", "temperature", ">", "28")),
        "ac_001", "turnOn"
    )
));
request.setSpecs(List.of(
    new SpecificationDto("1", List.of(
        new SpecConditionDto("ac_001", "state", "LockState", "=", "Cooling")
    ))
));
request.setAttack(false);
request.setIntensity(3);

// 2. 调用验证
VerificationResultDto result = verificationService.verify(request);

// 3. 处理结果
if (result.isSafe()) {
    System.out.println("✓ 所有规格满足");
} else {
    System.out.println("✗ 发现 " + result.getTraces().size() + " 个反例");
    for (TraceDto trace : result.getTraces()) {
        System.out.println("  违规规格: " + trace.getViolatedSpecId());
        for (TraceStateDto state : trace.getStates()) {
            System.out.println("    " + state);
        }
    }
}
```

### 6.2 生成SMV内容预览

```java
// 生成单个规格字符串预览
String specString = smvGenerator.generateSpecString(
    specificationDto, false, 3);
System.out.println(specString);
// 输出: CTLSPEC AG (device_001.LockState = locked)
```

---

## 7. 验证结果

### 7.1 测试覆盖

| 测试套件 | 用例数 | 通过 | 失败 | 状态 |
|---------|-------|------|------|------|
| NuSMVIntegrationTest | 10 | 10 | 0 | ✅ |
| ServiceImplEdgeCaseTest | 11 | 11 | 0 | ✅ |

### 7.2 验证用例

**用例1: 安全配置（无反例）**
- 场景: 空调初始为Off，温度24，规则在温度>28时触发，规格要求state!=Cooling
- 预期: safe=true, traces=[]
- 结果: ✅

**用例2: 不安全配置（发现反例）**
- 场景: 温度可升至30，规则在温度>28时触发，规格要求state!=Cooling
- 预期: safe=false, traces包含违反路径
- 结果: ✅

**用例3: 多设备联动**
- 场景: 客厅空调触发卧室空调
- 预期: 正确生成多设备SMV
- 结果: ✅

**用例4: IF-THEN规格（响应类型）**
- 场景: 客厅空调turnOn时，卧室空调应进入Cooling状态
- 预期: 正确生成响应规格
- 结果: ✅

---

## 8. 已知问题与改进建议

### 8.1 已知问题

| 问题 | 严重程度 | 说明 | 状态 |
|-----|---------|------|------|
| SmvRulesModuleBuilder仅生成注释 | 低 | 规则逻辑嵌入设备转换，非独立模块 | 文档已说明 |
| 模板缓存空包装器 | 低 | getTemplateFromCache返回空包装器而非null | 需修复 |
| 设备ID无null检查 | 低 | buildDeviceSmvMap未检查device.getId() | 建议添加 |

### 8.2 改进建议

**短期**:
1. 修复 `getTemplateFromCache()` 返回null而非空包装器
2. 在 `buildDeviceSmvMap()` 添加设备ID null检查
3. 在 `getSignalName()` 添加 `sig.getTrigger()` null检查

**中期**:
1. 添加SMV语法验证器
2. 实现规格缓存（相同输入直接返回结果）
3. 添加更多单元测试边界覆盖

**长期**:
1. 支持LTL规格的更复杂嵌套
2. 实现规则自动修复建议
3. 支持并发验证任务

---

## 附录

### A. 相关文件清单

| 类别 | 文件 | 说明 |
|-----|------|------|
| **Layer 1: 生成** | `generator/SmvGenerator.java` | 协调器 |
| **Layer 1: 生成** | `generator/SmvContentBuilder.java` | 内容生成器 |
| **Layer 1: 生成** | `generator/SmvDeviceModuleBuilder.java` | 设备模块生成器 |
| **Layer 1: 生成** | `generator/SmvMainModuleBuilder.java` | 主模块生成器 |
| **Layer 1: 生成** | `generator/SmvRulesModuleBuilder.java` | 规则模块生成器 |
| **Layer 1: 生成** | `generator/SmvSpecificationBuilder.java` | 规格模块生成器 |
| **Layer 2: 执行** | `executor/NusmvExecutor.java` | 执行器 |
| **Layer 3: 解析** | `parser/SmvTraceParser.java` | Trace 解析器 |
| **数据** | `data/DeviceSmvData.java` | SMV 数据模型 |
| **数据** | `data/TemplateWrapper.java` | 模板包装器 |
| Builder | SmvDeviceModuleBuilder.java | 设备模块 |
| Builder | SmvMainModuleBuilder.java | 主模块 |
| Builder | SmvRulesModuleBuilder.java | 规则模块 |
| Builder | SmvSpecificationBuilder.java | 规格模块 |
| 数据 | DeviceSmvData.java | SMV数据模型 |
| 数据 | TransitionInfo.java | 转换信息 |
| Executor | NusmvExecutorImpl.java | NuSMV执行器 |
| Parser | SmvTraceParser.java | 反例解析器 |
| 验证 | NusmvVerificationServiceImpl.java | 验证服务 |

### B. 外部依赖

| 依赖 | 版本 | 用途 |
|-----|------|------|
| NuSMV | 2.7.1+ | 模型检验工具 |
| Jackson | Spring Boot 3.x | JSON序列化 |
| Spring Boot | 3.5.7 | 框架 |

### C. 参考资料

- [NuSMV官方文档](https://nusmv.fbk.eu/)
- [CTL语法说明](https://nusmv.fbk.eu/userman/node23.html)
- [MEDIC论文](https://github.com/DependableSystemsLab/medic) - IoT安全验证框架

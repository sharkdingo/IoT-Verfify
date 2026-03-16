# IoT-Verify Backend - User Guide

## 1. Overview

IoT-Verify backend is a formal verification platform for IoT device configurations. It helps you verify that your smart home or IoT system behaves correctly and securely.

**Key Capabilities**:
- **Verify device interaction rules** using temporal logic (CTL/LTL)
- **Simulate device behavior** with random execution traces
- **Detect security vulnerabilities** with attack mode
- **AI-powered assistance** for rule recommendations and natural language interaction

**Architecture**: REST API → NuSMV Model Checker → Verification Results

**Use Cases**:
- Smart home safety verification (e.g., "AC never overheats")
- Security testing (e.g., "untrusted devices can't control locks")
- Behavior simulation (e.g., "what happens over 50 time steps?")

---

## 2. Quick Start

Get running in 5 minutes:

```bash
# 1. Start required services and create database
docker run -d -p 3306:3306 -e MYSQL_ROOT_PASSWORD=password \
  -e MYSQL_DATABASE=iot_verify mysql:8.0 \
  --character-set-server=utf8mb4 --collation-server=utf8mb4_unicode_ci

docker run -d -p 6379:6379 redis:alpine

# Or if using local MySQL, create database manually:
# mysql -u root -p -e "CREATE DATABASE iot_verify CHARACTER SET utf8mb4 COLLATE utf8mb4_unicode_ci;"

# 2. Configure environment
export DB_PASSWORD="password"
export JWT_SECRET="your-secret-key-here-min-256-bits"
export VOLCENGINE_API_KEY="your-api-key"
export NUSMV_PATH="/path/to/NuSMV"  # Required for verification

# 3. Start backend
cd backend
mvn spring-boot:run

# 4. Test with example request
curl -X POST http://localhost:8080/api/auth/register \
  -H "Content-Type: application/json" \
  -d '{"phone":"13800138000","password":"password123","username":"testuser"}'
```

**Note**: The default DB URL expects database `iot_verify` to exist. Docker command above creates it automatically.

---

## 3. Prerequisites & Installation

### Required

- **MySQL 8.0+**: Database for storing templates, rules, verification results
  - Create database: `CREATE DATABASE iot_verify CHARACTER SET utf8mb4;`

- **NuSMV 2.6+**: Formal verification engine
  - Download: [NuSMV official site](http://nusmv.fbk.eu/)
  - **Version requirement**: NuSMV 2.6-2.7 (NOT nuXmv - incompatible)
  - Installation paths:
    - Windows: `D:/NuSMV/NuSMV-2.7.1-win64/NuSMV-2.7.1-win64/bin/NuSMV.exe`
    - Linux: `/usr/local/bin/NuSMV`
    - macOS: `/usr/local/bin/NuSMV`

- **Java 17+**: Runtime environment

### Optional

- **Redis 6.0+**: JWT token blacklist (fail-open mode - app continues if unavailable)

### For AI Features

- **Volcengine Ark API Key**: Required for AI assistant and rule recommendations

### Installation

```bash
cd backend
mvn clean install -DskipTests
```

---

## 4. Configuration

### Environment Variables

| Variable | Required | Default | Description |
|----------|----------|---------|-------------|
| **Database** | | | |
| `DB_URL` | Yes | `jdbc:mysql://localhost:3306/iot_verify...` | MySQL connection string |
| `DB_USERNAME` | Yes | `root` | Database username |
| `DB_PASSWORD` | Yes | `sharkdingo123` | Database password |
| `JPA_SHOW_SQL` | No | `false` | Log SQL statements |
| **Server** | | | |
| `SERVER_PORT` | No | `8080` | Backend server port |
| **Auth** | | | |
| `JWT_SECRET` | Yes | (default) | JWT signing key (256+ bits) |
| `JWT_EXPIRATION` | No | `86400000` | JWT token expiration in ms (default 24h) |
| **Redis** | | | |
| `REDIS_HOST` | No | `localhost` | Redis host |
| `REDIS_PORT` | No | `6379` | Redis port |
| `REDIS_PASSWORD` | No | _(empty)_ | Redis password |
| `REDIS_DATABASE` | No | `0` | Redis database index |
| **CORS** | | | |
| `CORS_ORIGINS` | No | `http://localhost:3000,http://localhost:3001` | Allowed origins (comma-separated) |
| **NuSMV** | | | |
| `NUSMV_PATH` | Yes | (OS-specific) | Path to NuSMV executable |
| `NUSMV_TIMEOUT_MS` | No | `120000` | NuSMV execution timeout (ms) |
| `NUSMV_MAX_CONCURRENT` | No | `6` | Max concurrent NuSMV processes |
| `NUSMV_PREFIX` | No | _(empty)_ | Command prefix (e.g. `wine` on Linux) |
| `NUSMV_ACQUIRE_PERMIT_TIMEOUT_MS` | No | `10000` | Concurrency permit acquire timeout (ms) |
| **Fix** | | | |
| `FIX_TIMEOUT_MS` | No | `300000` | Fix overall timeout in ms (soft deadline) |
| `FIX_MAX_ATTEMPTS` | No | `20` | Max NuSMV calls per fix strategy |
| `FIX_MAX_REFINE_ATTEMPTS` | No | `10` | Max refinement loop iterations (§5.3) |
| `FIX_MAX_CANDIDATES_PER_RULE` | No | `5` | Max candidate fixes per rule |
| **AI (Volcengine Ark)** | | | |
| `VOLCENGINE_API_KEY` | For AI | `your_api_key_here` | Volcengine Ark API key |
| `VOLCENGINE_MODEL_ID` | No | `ep-20251125202752-bhwbw` | Ark model endpoint ID |
| `VOLCENGINE_BASE_URL` | No | `https://ark.cn-beijing.volces.com` | Ark API base URL |
| `ARK_TIMEOUT_MINUTES` | No | `5` | AI request timeout (minutes) |
| **Thread Pools** | | | |
| `THREAD_POOL_{NAME}_{PARAM}` | No | (see below) | 5 pools: `CHAT`, `VERIFICATION_TASK`, `SYNC_VERIFICATION`, `SYNC_SIMULATION`, `SIMULATION_TASK`. Each has `CORE`, `MAX`, `QUEUE`, `AWAIT` params. Example: `THREAD_POOL_CHAT_CORE=10` |

### Configuration File

Minimal `application.yaml`:

```yaml
spring:
  datasource:
    url: ${DB_URL:jdbc:mysql://localhost:3306/iot_verify?useSSL=false&serverTimezone=Asia/Shanghai&characterEncoding=utf-8&allowPublicKeyRetrieval=true}
    username: ${DB_USERNAME:root}
    password: ${DB_PASSWORD:sharkdingo123}
  data:
    redis:
      host: ${REDIS_HOST:localhost}
      port: ${REDIS_PORT:6379}

jwt:
  secret: ${JWT_SECRET:iot-verify-secret-key-must-be-at-least-256-bits-long-for-hs256}
  expiration: ${JWT_EXPIRATION:86400000}

cors:
  allowed-origins: ${CORS_ORIGINS:http://localhost:3000,http://localhost:3001}

nusmv:
  path: ${NUSMV_PATH:D:/NuSMV/NuSMV-2.7.1-win64/NuSMV-2.7.1-win64/bin/NuSMV.exe}
  timeout-ms: ${NUSMV_TIMEOUT_MS:120000}
  max-concurrent: ${NUSMV_MAX_CONCURRENT:6}
  command-prefix: ${NUSMV_PREFIX:}
  acquire-permit-timeout-ms: ${NUSMV_ACQUIRE_PERMIT_TIMEOUT_MS:10000}

fix:
  fix-timeout-ms: ${FIX_TIMEOUT_MS:300000}
  max-attempts: ${FIX_MAX_ATTEMPTS:20}
  max-refine-attempts: ${FIX_MAX_REFINE_ATTEMPTS:10}
  max-candidates-per-rule: ${FIX_MAX_CANDIDATES_PER_RULE:5}

volcengine:
  ark:
    api-key: ${VOLCENGINE_API_KEY:your_api_key_here}
    model-id: ${VOLCENGINE_MODEL_ID:ep-20251125202752-bhwbw}
    base-url: ${VOLCENGINE_BASE_URL:https://ark.cn-beijing.volces.com}
    timeout-minutes: ${ARK_TIMEOUT_MINUTES:5}

# Thread pools (all optional, shown with defaults)
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

**Note**: Database tables are auto-created on first run (Hibernate `ddl-auto: update`).

### Starting the Backend

```bash
# Development mode
mvn spring-boot:run

# Production mode
java -jar target/Iot-Verify-0.0.1-SNAPSHOT.jar
```

---

## 5. API Input Formats

This section explains the data structures you'll use when calling the verification API.

### 5.1 Device Templates

**What**: Define device types with states, variables, and APIs.

**API Format** (POST /api/board/templates):

```json
{
  "name": "Air Conditioner",
  "manifest": {
    "Name": "Air Conditioner",
    "Description": "Smart AC with cooling/heating modes",
    "InternalVariables": [],
    "ImpactedVariables": ["temperature", "humidity"],
    "Modes": ["HvacMode"],
    "InitState": "off",
    "WorkingStates": [
      {
        "Name": "cool",
        "Dynamics": [
          {"VariableName": "temperature", "ChangeRate": "-1"}
        ],
        "Invariant": "true",
        "Trust": "trusted",
        "Privacy": "private"
      },
      {
        "Name": "off",
        "Dynamics": [],
        "Invariant": "true",
        "Trust": "trusted",
        "Privacy": "private"
      }
    ],
    "APIs": [
      {
        "Name": "cool",
        "StartState": "",
        "EndState": "cool",
        "Trigger": null,
        "Signal": true
      },
      {
        "Name": "off",
        "StartState": "",
        "EndState": "off",
        "Trigger": null,
        "Signal": true
      }
    ]
  }
}
```

**Important**: POST /api/board/templates requires a wrapper object with:
- `name` (required, ≤100 chars): Template display name
- `manifest` (required): The actual template definition (shown above)

**Manifest Field Explanations**:
- `WorkingStates`: Device operational states with dynamics (how variables change)
- `APIs`: Actions that trigger state transitions
- `ImpactedVariables`: Environment variables this device affects
- `Trust`: Security level (`trusted`, `untrusted`)
- `Privacy`: Privacy level (`public`, `private`)

**Template Management**:
- Default templates loaded from `resources/deviceTemplate/*.json` on user registration
- Reload endpoint: `POST /api/board/templates/reload` (resets to defaults)
- Custom templates validated for NuSMV compatibility (identifier rules, no reserved words)

### 5.2 Device Instances (for Verification)

**What**: Concrete device instances for verification requests.

**Note**: This section covers `DeviceVerificationDto` used in verification API calls. For canvas operations (adding devices to the board UI), see `/api/board/nodes` which uses a different structure with position/width/height fields.

**Structure** (for POST /api/verify):

```json
{
  "varName": "ac_living_room",
  "templateName": "Air Conditioner",
  "state": "off",
  "variables": [
    {
      "name": "temperature",
      "value": "24",
      "trust": "trusted"
    }
  ],
  "privacies": [
    {
      "name": "temperature",
      "privacy": "private"
    }
  ]
}
```

**Important**:
- `varName`: Used for device references in rules/specs (must be unique across all devices)
- `templateName`: Must exist in current user's template table
- `state`: Must be a valid state from the template's WorkingStates
- `variables`: Initial values for impacted variables with trust levels
- `privacies`: Privacy levels for variables (only used when `enablePrivacy: true`)

### 5.3 Rules

**What**: IFTTT automation rules (IF conditions THEN command).

**Structure**:

```json
{
  "conditions": [
    {
      "deviceName": "temp_sensor",
      "attribute": "temperature",
      "relation": ">",
      "value": "30"
    }
  ],
  "command": {
    "deviceName": "ac_living_room",
    "action": "cool"
  }
}
```

**Valid Relations**: `=`, `!=`, `>`, `<`, `>=`, `<=`, `in`, `not in`

**Examples**:
- "If temperature > 30, turn on AC"
- "If motion detected AND time > 22:00, turn off lights"
- "If door opens, send notification"

### 5.4 Specifications

**What**: Temporal logic properties to verify.

**7 Template Types**:

| Template ID | Pattern | CTL/LTL | Meaning | Conditions Used |
|-------------|---------|---------|---------|-----------------|
| 1 | AG(A) or AG(IF→THEN) | CTL | A always holds / IF implies THEN | `aConditions` OR (`ifConditions` + `thenConditions`) |
| 2 | AF(A) | CTL | A eventually happens | `aConditions` |
| 3 | AG(!A) | CTL | A never happens | `aConditions` |
| 4 | AG(IF→AX(THEN)) | CTL | THEN immediately follows IF | `ifConditions` + `thenConditions` |
| 5 | AG(IF→AF(THEN)) | CTL | THEN eventually follows IF | `ifConditions` + `thenConditions` |
| 6 | G(IF→F G(THEN)) | **LTL** | IF leads to persistent THEN | `ifConditions` + `thenConditions` |
| 7 | AG(!(body)) | CTL | Safety (negated untrusted/attack conditions) | `aConditions` |

**Structure**:

```json
{
  "id": "spec_1",
  "templateId": "1",
  "templateLabel": "AG(A)",
  "aConditions": [
    {
      "deviceId": "ac_living_room",
      "targetType": "state",
      "key": "state",
      "relation": "!=",
      "value": "error"
    }
  ],
  "ifConditions": [],
  "thenConditions": []
}
```

**Condition Fields**:
- `deviceId`: Device varName (must match a device in the request)
- `targetType`: `"state"`, `"variable"`, `"api"`, `"trust"`, or `"privacy"`
- `key`: Depends on targetType:
  - `state`: state name (e.g., "cool", "off")
  - `variable`: variable name (e.g., "temperature")
  - `api`: API name (e.g., "turnOn")
  - `trust`: trust attribute (e.g., "trust_Mode_state")
  - `privacy`: privacy attribute (e.g., "privacy_variable")
- `relation`: `=`, `!=`, `>`, `<`, `>=`, `<=`, `in`, `not in` (aliases: `EQ`, `NEQ`, `GT`, `LT`, `GTE`, `LTE`, `IN`, `NOT_IN`)
- `value`: Expected value

**Examples**:

**Template 1 (Always)**: "AC is never off"

```json
{
  "id": "spec_always",
  "templateId": "1",
  "templateLabel": "AG(A)",
  "aConditions": [{"deviceId": "ac_1", "targetType": "state", "key": "state", "relation": "!=", "value": "off"}],
  "ifConditions": [],
  "thenConditions": []
}
```

**Template 4 (Immediate)**: "After door opens, alarm turns on immediately"

```json
{
  "id": "spec_immediate",
  "templateId": "4",
  "templateLabel": "AG(IF→AX(THEN))",
  "aConditions": [],
  "ifConditions": [{"deviceId": "door_1", "targetType": "state", "key": "state", "relation": "=", "value": "open"}],
  "thenConditions": [{"deviceId": "alarm_1", "targetType": "state", "key": "state", "relation": "!=", "value": "off"}]
}
```

**Template 6 (Persistence - LTL)**: "If temperature > 30, AC eventually stays in cool mode"
```json
{
  "id": "spec_persistence",
  "templateId": "6",
  "templateLabel": "G(IF→F G(THEN))",
  "aConditions": [],
  "ifConditions": [{"deviceId": "sensor_1", "targetType": "variable", "key": "temperature", "relation": ">", "value": "30"}],
  "thenConditions": [{"deviceId": "ac_1", "targetType": "state", "key": "state", "relation": "=", "value": "cool"}]
}
```

**Template 7 (Safety)**: "Temperature never exceeds 35 degrees"

```json
{
  "id": "spec_safety",
  "templateId": "7",
  "templateLabel": "AG(!(body))",
  "aConditions": [{"deviceId": "sensor_1", "targetType": "variable", "key": "temperature", "relation": ">", "value": "35"}],
  "ifConditions": [],
  "thenConditions": []
}
```

**Note**: Template 7 negates the condition, so this checks that temperature never exceeds 35. Use variable conditions for safety properties to avoid state validation issues.

### 5.5 Complete Verification Request

**Structure**:

```json
{
  "devices": [ /* DeviceVerificationDto array */ ],
  "rules": [ /* RuleDto array */ ],
  "specs": [ /* SpecificationDto array */ ],
  "isAttack": false,
  "intensity": 3,
  "enablePrivacy": false
}
```

**Attack Mode**:
- `isAttack: true`: Simulates adversarial behavior
- `intensity`: Controls attack strength (0 = minimal, 50 = maximum)
- Use case: Test system resilience against malicious devices

**Privacy Mode**:
- `enablePrivacy: true`: Adds privacy dimension to verification
- Checks if private data leaks to public channels

---

## 6. API Endpoints

### 6.1 Authentication

All endpoints (except `/api/auth/register` and `/api/auth/login`) require JWT authentication:

```bash
Authorization: Bearer <token>
```

**Endpoints**:

```
POST /api/auth/register  - Register new user
POST /api/auth/login     - Login (returns JWT token)
POST /api/auth/logout    - Logout (blacklists token)
```

**Usage**:

```bash
# Login
TOKEN=$(curl -X POST http://localhost:8080/api/auth/login \
  -H "Content-Type: application/json" \
  -d '{"phone":"13800138000","password":"password123"}' \
  | jq -r '.data.token')

# Use token in subsequent requests
curl -H "Authorization: Bearer $TOKEN" ...
```

### 6.2 Device Management

```
GET    /api/board/templates           - List device templates
POST   /api/board/templates           - Create custom template
DELETE /api/board/templates/{id}      - Delete template
POST   /api/board/templates/reload    - Reset to default templates

GET    /api/board/nodes                - List device instances
POST   /api/board/nodes                - Save device instances
GET    /api/board/edges                - List device connections
POST   /api/board/edges                - Save device connections

GET    /api/board/layout               - Get board layout
POST   /api/board/layout               - Save board layout
GET    /api/board/active               - Get active board state
POST   /api/board/active               - Save active board state
```

### 6.3 Rules & Specifications

```
GET    /api/board/rules                - List automation rules
POST   /api/board/rules                - Save rules
GET    /api/board/rules/recommend      - AI-powered rule recommendations
POST   /api/board/rules/check-duplicate - Check for duplicate rules
POST   /api/board/devices/recommend    - AI-powered device recommendations

GET    /api/board/specs                - List specifications
POST   /api/board/specs                - Save specifications
```

### 6.4 Verification & Simulation

```
POST   /api/verify                              - Synchronous verification
POST   /api/verify/async                        - Async verification (returns taskId)
GET    /api/verify/tasks/{id}                   - Get verification task status
GET    /api/verify/tasks/{id}/progress          - Get verification progress (0-100)
POST   /api/verify/tasks/{id}/cancel            - Cancel verification task

POST   /api/simulate                             - Synchronous simulation
POST   /api/simulate/async                       - Async simulation (returns taskId)
GET    /api/simulate/tasks/{id}                  - Get simulation task status
GET    /api/simulate/tasks/{id}/progress         - Get simulation progress (0-100)
POST   /api/simulate/tasks/{id}/cancel           - Cancel simulation task

POST   /api/simulate/traces                      - Simulate and save
GET    /api/simulate/traces                      - List saved simulations
GET    /api/simulate/traces/{id}                 - Get simulation details
DELETE /api/simulate/traces/{id}                 - Delete simulation

GET    /api/verify/traces                       - List verification traces
GET    /api/verify/traces/{id}                  - Get trace details
DELETE /api/verify/traces/{id}                  - Delete trace
GET    /api/verify/traces/{id}/fault-rules      - Fault localization
POST   /api/verify/traces/{id}/fix              - Fix recommendations
```

**Fix API Details**:

`GET /api/verify/traces/{id}/fault-rules` — Fast fault localization (no NuSMV invocation). Returns which rules were triggered in the counterexample.

Response: `Result<List<FaultRuleDto>>`

| Field | Type | Description |
|-------|------|-------------|
| `ruleIndex` | int | Rule index in the verification request's rule list (stable key) |
| `ruleId` | Long? | Rule database ID (null for unsaved rules) |
| `ruleString` | String | Human-readable rule description |
| `triggerStep` | int | Counterexample step where this rule was triggered |
| `targetDevice` | String | Target device of the rule command |
| `targetAction` | String | Target API/action of the rule command |
| `conflicting` | boolean | Whether this rule conflicts with another triggered rule |
| `conflictWithRuleIndex` | Integer? | Index of the conflicting rule |
| `reason` | String | Explanation of why the rule was identified as a fault |

`POST /api/verify/traces/{id}/fix` — Fix recommendations (may invoke NuSMV multiple times, up to `fix.fix-timeout-ms`).

Request body (`FixRequestDto`, **optional** — omit or send `null` for defaults):

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `strategies` | List\<String\>? | `["parameter","condition","disable"]` | Fix strategies to attempt, in order |
| `preferredRanges` | Map\<String, PreferredRange\>? | null | Per-parameter preferred value ranges. Keys: `r{ruleIdx}_c{condIdx}` (e.g. `r0_c1`). Values: `{lower: int, upper: int}` (inclusive, lower ≤ upper) |

Response: `Result<FixResultDto>`

| Field | Type | Description |
|-------|------|-------------|
| `traceId` | Long | ID of the analyzed trace |
| `violatedSpecId` | String | Spec ID that was violated (from trace) |
| `fixable` | boolean | Whether at least one fix suggestion was found |
| `faultRules` | List\<FaultRuleDto\> | Fault-localized rules (same schema as above) |
| `suggestions` | List\<FixSuggestionDto\> | Verified fix proposals |
| `summary` | String | Human-readable summary (includes timeout/drift warnings if applicable) |
| `unusedPreferredRangeKeys` | List\<String\>? | `preferredRanges` keys that did not match any parameterizable condition |

`FixSuggestionDto` fields:

| Field | Type | Description |
|-------|------|-------------|
| `strategy` | String | `"parameter"`, `"condition"`, or `"disable"` |
| `description` | String | Human-readable fix description |
| `parameterAdjustments` | List? | §5.1: threshold changes (`ruleIndex`, `conditionIndex`, `attribute`, `relation`, `originalValue`, `newValue`, `lowerBound`, `upperBound`) |
| `conditionAdjustments` | List? | §5.2: condition changes (`ruleIndex`, `conditionIndex`, `action`=remove/add, `attribute`, `description`, `deviceName`, `relation`, `value`) |
| `disabledRuleIndices` | List\<Integer\>? | Rule indices to disable (for "disable" strategy) |
| `verified` | boolean | Whether the fix was re-verified with NuSMV |

**Important**: Verification and simulation use **different base paths**:
- **Verification**: `/api/verify/tasks/{id}`
- **Simulation**: `/api/simulate/tasks/{id}`

**Sync vs Async**:

| Mode | Use Case | Response | Polling Path |
|------|----------|----------|--------------|
| Sync Verify | Small models (<10 devices) | Immediate result | N/A |
| Async Verify | Large models, long-running | `taskId` | `/api/verify/tasks/{id}` |
| Sync Simulate | Small models, quick preview | Immediate result | N/A |
| Async Simulate | Large simulations | `taskId` | `/api/simulate/tasks/{id}` |
| Simulate+Save | Persist simulation trace | `SimulationTraceDto` | N/A |

### 6.5 AI Assistant

```
GET    /api/chat/sessions              - List chat sessions
POST   /api/chat/sessions              - Create new session
GET    /api/chat/sessions/{sessionId}/messages - Get message history
POST   /api/chat/completions           - Send message (SSE stream)
DELETE /api/chat/sessions/{sessionId}         - Delete session
```

**SSE Streaming**:

```bash
curl -X POST http://localhost:8080/api/chat/completions \
  -H "Authorization: Bearer $TOKEN" \
  -H "Accept: text/event-stream" \
  -d '{"sessionId":"123","content":"Add a thermostat"}' \
  --stream
```

**Response Format** (JSON chunks, no [DONE] marker):

```
data: {"content":"I'll add a thermostat for you..."}
data: {"content":" Let me configure it."}
data: {"content":"","command":{"type":"REFRESH_DATA","payload":{"target":"device_list"}}}
(stream ends via connection close)
```

**Note**: Backend sends JSON objects (`StreamResponseDto`) and ends stream with `emitter.complete()`. There is **no** `[DONE]` termination frame.

---

## 7. NuSMV Verification Module

**What is NuSMV?**

NuSMV is a formal verification tool for finite-state systems. It checks temporal logic properties (CTL/LTL) and provides counterexamples when properties are violated.

**How It Works**:

1. Backend generates SMV model file from your devices/rules/specs
2. NuSMV executable verifies the model
3. Results parsed and returned as JSON

**Key Features**:

- **Attack Mode**: Simulates adversarial device behavior
- **Privacy Verification**: Checks for data leakage
- **Counterexamples**: Shows violation traces step-by-step
- **User Isolation**: Each user has separate template/verification space

**Understanding Results**:

```json
{
  "safe": false,
  "specResults": [true, false, true],
  "traces": [
    {
      "specIndex": 1,
      "states": [
        {"step": 0, "ac_living_room.state": "off", "temperature": "30"},
        {"step": 1, "ac_living_room.state": "cool", "temperature": "29"}
      ]
    }
  ]
}
```

- `safe: true`: All specifications satisfied ✓
- `safe: false`: At least one specification violated
- `traces`: Counterexample traces showing how violations occur

**Detailed Documentation**: See [NuSMV_Module_Documentation.md](NuSMV_Module_Documentation.md) for:
- SMV file structure and syntax
- CTL/LTL specification details
- Trace parsing format
- Validation rules (P1-P5)
- Advanced features

---

## 8. AI Assistant Module

**What is the AI Assistant?**

Natural language interface powered by Volcengine Ark AI with tool-based function calling for device operations and intelligent rule recommendations.

**Capabilities**:

**Board Management**:
- "Show me all devices on the board"
- "What's the current system state?"

**Device Operations**:
- "Add a thermostat to the living room"
- "Delete the bedroom light"
- "Find all temperature sensors"

**Rule Management**:
- "Create a rule: if temperature > 30, turn on AC"
- "List all automation rules"
- "Recommend rules for my devices" ← **AI-powered intelligent suggestions**

**Verification & Simulation**:
- "Verify my system configuration"
- "Run a simulation for 10 steps"
- "Show me the last verification trace"
- "Fix the violated specification in trace #5" ← **fault localization + fix suggestions**

**Template Management**:
- "List available device templates"
- "Add a custom smoke detector template"

**AI Rule Recommendations**:

Analyzes device capabilities (APIs, variables, states) and suggests rules based on:
- Security scenarios (gas leak detection, smoke alarms)
- Energy saving (auto-off when absent)
- Comfort (temperature/humidity control)
- Automation (motion sensors, door triggers)

Validates recommendations against actual device capabilities and returns structured suggestions with confidence scores.

**Configuration**:
- Requires `VOLCENGINE_API_KEY` environment variable
- Model: `ep-20251125202752-bhwbw` (configurable in `application.yaml`)
- Timeout: 5 minutes per request

---

## 9. Common Workflows

### Workflow 1: Verify a Simple Thermostat Rule

```bash
# 1. Login
TOKEN=$(curl -X POST http://localhost:8080/api/auth/login \
  -H "Content-Type: application/json" \
  -d '{"phone":"13800138000","password":"password123"}' \
  | jq -r '.data.token')

# 2. Create verification request
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [
      {
        "varName": "thermostat_1",
        "templateName": "Thermostat",
        "state": "auto;auto",
        "variables": [{"name": "temperature", "value": "22", "trust": "trusted"}]
      }
    ],
    "rules": [
      {
        "conditions": [{"deviceName": "thermostat_1", "attribute": "temperature", "relation": ">", "value": "25"}],
        "command": {"deviceName": "thermostat_1", "action": "cool"}
      }
    ],
    "specs": [
      {
        "id": "spec_1",
        "templateId": "3",
        "templateLabel": "AG(!A)",
        "aConditions": [{"deviceId": "thermostat_1", "targetType": "variable", "key": "temperature", "relation": ">", "value": "30"}],
        "ifConditions": [],
        "thenConditions": []
      }
    ],
    "isAttack": false,
    "intensity": 0,
    "enablePrivacy": false
  }'

# 3. Check result
# safe: true → System is safe
# safe: false → Check traces for violations
```

### Workflow 2: Test Attack Scenarios

```bash
# Enable attack mode with intensity 10
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [...],
    "rules": [...],
    "specs": [...],
    "isAttack": true,
    "intensity": 10,
    "enablePrivacy": false
  }'
```

### Workflow 3: Fix a Violated Specification

```bash
# 1. Run verification and get a trace with violation
TRACE_ID=$(curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{ ... }' | jq -r '.data.traces[0].id')

# 2. Fault localization (fast, no NuSMV)
curl -H "Authorization: Bearer $TOKEN" \
  http://localhost:8080/api/verify/traces/$TRACE_ID/fault-rules

# 3. Fix recommendations (may take up to fix.fix-timeout-ms)
curl -X POST http://localhost:8080/api/verify/traces/$TRACE_ID/fix \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "strategies": ["parameter", "condition", "disable"],
    "preferredRanges": {
      "r0_c1": {"lower": 20, "upper": 30}
    }
  }'

# Response includes:
# - faultRules: which rules caused the violation
# - suggestions: verified fix proposals (parameter/condition/disable)
# - summary: includes timeout/drift warnings if applicable
```

### Workflow 4: Use AI Assistant

```bash
# 1. Create chat session
SESSION_ID=$(curl -X POST http://localhost:8080/api/chat/sessions \
  -H "Authorization: Bearer $TOKEN" | jq -r '.data.id')

# 2. Send message
curl -X POST http://localhost:8080/api/chat/completions \
  -H "Authorization: Bearer $TOKEN" \
  -H "Accept: text/event-stream" \
  -d "{\"sessionId\":\"$SESSION_ID\",\"content\":\"Add a thermostat and recommend rules\"}" \
  --stream
```

---

## 10. Troubleshooting

### Error: "Template not found"

```json
{"code": 500, "message": "[MULTIPLE_DEVICES_FAILED] Cannot generate SMV model: templates not found for ac_1(template=Air Conditioner), sensor_2(template=TemperatureSensor)"}
```

**Cause**: One or more devices reference templates that don't exist in user's template table

**Solution**:
1. Check available templates: `GET /api/board/templates`
2. Reload default templates: `POST /api/board/templates/reload`
3. Create custom template: `POST /api/board/templates`

### Error: "Ambiguous device reference"

```json
{"code": 500, "message": "[AMBIGUOUS_DEVICE_REFERENCE] Ambiguous device reference 'Thermostat': candidates [thermostat_1, thermostat_2]"}
```

**Cause**: Multiple devices with same template name, rule/spec doesn't specify `varName`

**Solution**: Use unique `varName` in rules/specs instead of `templateName`

### Error: "NuSMV execution failed"

**Synchronous verification** returns 200 with `safe: false`:

```json
{
  "code": 200,
  "data": {
    "safe": false,
    "traces": [],
    "specResults": [],
    "checkLogs": ["NuSMV execution failed: <error details>"]
  }
}
```

**Asynchronous verification** task status shows `FAILED`:

```json
{
  "status": "FAILED",
  "errorMessage": "NuSMV execution failed: NuSMV exited with code 1: <output details>"
}
```

**Cause**: NuSMV not found, incorrect path, or execution error

**Solution**:
1. Verify NuSMV installed: `nusmv -version` (should show 2.6+)
2. Set correct path: `export NUSMV_PATH=/path/to/nusmv`
3. Check version compatibility (NOT nuXmv)
4. Review error details in `checkLogs` for specific issues

### Error: "Connection to Redis failed"

```
Unable to connect to Redis at localhost:6379
```

**Cause**: Redis not running (optional service)

**Solution**:
- **Option 1**: Start Redis: `redis-server` or `docker run -d -p 6379:6379 redis:alpine`
- **Option 2**: Continue without Redis (fail-open mode - JWT blacklist disabled)

### Error: "JWT token expired"

```json
{"code": 401, "message": "Token expired"}
```

**Solution**: Login again to get new token

### Error: "Verification timeout"

**Synchronous verification** returns 200 with `safe: false`:

```json
{
  "code": 200,
  "data": {
    "safe": false,
    "traces": [],
    "specResults": [],
    "checkLogs": ["Verification timed out"]
  }
}
```

**Asynchronous verification** task status shows `FAILED`:

```json
{
  "status": "FAILED",
  "errorMessage": "NuSMV execution failed: NuSMV execution timed out after 120000ms"
}
```

**Cause**: Model too complex or timeout too short

**Solution**:
1. Use async verification: `POST /api/verify/async`
2. Increase timeout: `export NUSMV_TIMEOUT_MS=300000` (5 minutes)
3. Simplify model (fewer devices/rules)

---

## License

MIT License

# CLAUDE.md - IoT-Verify Backend

## Project Overview

IoT smart home simulation and formal verification platform using NuSMV model checking.
Reference project: `D:\MEDIC-test\MEDIC-test` (MEDIC — the original research prototype). Key differences:
- MEDIC uses pre-defined device templates with fixed rule files; this project uses user-input device instances via REST API.
- MEDIC generates SMV from `Scenario` objects parsed from text files; this project generates from `DeviceVerificationDto` + `RuleDto` + `SpecificationDto`.
- MEDIC's `ScenarioSMVGeneration` is a single 1165-line class; this project splits into `SmvGenerator` + 4 module builders + `DeviceSmvDataFactory`.

## Tech Stack

- Java 17 + Spring Boot 3.x
- MySQL + Redis (token blacklist)
- JWT authentication (BCrypt passwords)
- NuSMV 2.x for formal verification (tested 2.5–2.7, incompatible with nuXmv)
- Volcengine Ark AI (chat assistant with SSE streaming)

## Package Structure

```
cn.edu.nju.Iot_Verify/
├── controller/          # REST API endpoints (Result<T> wrapper)
├── service/             # Business logic interfaces
│   └── impl/            # Service implementations
├── component/
│   ├── nusmv/           # NuSMV verification engine
│   │   ├── generator/   # SMV model generation
│   │   │   ├── SmvGenerator.java          # Orchestrator
│   │   │   ├── SmvModelValidator.java     # Pre-generation validation (P1-P5)
│   │   │   ├── PropertyDimension.java     # TRUST/PRIVACY enum
│   │   │   ├── data/    # DeviceSmvData, DeviceSmvDataFactory
│   │   │   └── module/  # SmvDeviceModuleBuilder, SmvMainModuleBuilder, SmvRuleCommentWriter, SmvSpecificationBuilder
│   │   ├── executor/    # NusmvExecutor (process execution + per-spec parsing)
│   │   └── parser/      # SmvTraceParser (counterexample → TraceStateDto)
│   └── aitool/          # AI tool integration (add/delete/search nodes)
├── client/              # ArkAiClient (Volcengine Ark AI SDK wrapper)
├── dto/                 # Data transfer objects (by domain: auth, board, chat, device, rule, spec, simulation, trace, verification)
├── po/                  # JPA entities (13 tables + DeviceEdgeId composite key)
├── repository/          # Spring Data JPA repositories (13)
├── security/            # JWT filter, @CurrentUser resolver, UserContextHolder, SecurityConfig
├── configure/           # NusmvConfig, ThreadConfig (chatExecutor + verificationTaskExecutor), WebConfig
                         # SimulationServiceImpl uses its own simulationExecutor (fixed 4 threads)
├── exception/           # BaseException hierarchy + GlobalExceptionHandler
└── util/
    ├── mapper/          # PO ↔ DTO mappers (manual, not MapStruct): UserMapper, DeviceNodeMapper, DeviceEdgeMapper, RuleMapper, SpecificationMapper, ChatMapper, TraceMapper, VerificationTaskMapper, SimulationTraceMapper
    ├── JsonUtils.java   # JSON serialization helpers
    ├── JwtUtil.java     # JWT token generation/validation
    ├── FunctionParameterSchema.java  # AI function parameter schema builder
    └── LevenshteinDistanceUtil.java  # Edit distance (used by AI tools)
```

## Build & Run

```bash
cd backend
mvn compile          # Compile
mvn spring-boot:run  # Run (requires MySQL + Redis)
mvn test             # Run tests
```

Test workflow: `powershell -File test_workflow.ps1` (end-to-end API test, requires running server)

## Configuration

Key config in `src/main/resources/application.yaml`:
- `spring.datasource.*` — MySQL connection
- `spring.data.redis.*` — Redis connection (token blacklist)
- `jwt.secret` / `jwt.expiration` — JWT settings
- `nusmv.path` — NuSMV executable path (OS-specific)
- `nusmv.command-prefix` — Optional prefix (e.g. `wsl` on Windows)
- `nusmv.timeout-ms` — Execution timeout (default 120000)
- `volcengine.ark.*` — AI chat API settings
- `cors.allowed-origins` — CORS allowed origins (used by SecurityConfig)
- `server.port` — HTTP port (default 8080)

## Key Conventions

- Controllers return `Result<T>` wrapper. Use `Result.success()` for void responses (never `success(null)`).
- Controller `@CurrentUser` parameter is always named `userId`.
- Service interfaces in `service/`, implementations in `service/impl/`.
- Controllers never expose PO objects — always map to DTOs.
- CORS is configured only in `SecurityConfig` (not WebConfig).
- JSON serialization: `JsonUtils.toJson()` for objects, `JsonUtils.toJsonOrEmpty()` for lists.
- Device templates are in `src/main/resources/deviceTemplate/`.
- `ValidationException` uses HTTP 422 (not 400). Handler and exception code are aligned.
- `SmvGenerationException` has a dedicated handler in `GlobalExceptionHandler` that includes `errorCategory`. Error categories include `TEMPLATE_NOT_FOUND`, `ILLEGAL_TRIGGER_ATTRIBUTE`, `INVALID_STATE_FORMAT`, `ENV_VAR_CONFLICT`, `TRUST_PRIVACY_CONFLICT`, etc.
- `SmvModelValidator` runs before SMV text generation. Hard validations throw `SmvGenerationException`; soft validations (unknown user variables, stateless device with state) only log warnings.
- SSE endpoints (e.g. `/api/chat/completions`) return `SseEmitter` directly, not wrapped in `Result<T>`.
- Exception hierarchy: `BaseException(code, message)` → `BadRequestException(400)`, `UnauthorizedException(401)`, `ForbiddenException(403)`, `ResourceNotFoundException(404)`, `ConflictException(409)`, `ValidationException(422)`, `InternalServerException(500)` → `SmvGenerationException`, `ServiceUnavailableException(503)`.

## NuSMV Verification Flow

```
VerificationRequestDto (devices, rules, specs, isAttack, intensity, enablePrivacy)
  → SmvGenerator.generate()
    → DeviceSmvDataFactory.buildDeviceSmvMap() — merge user device instances with templates
    → SmvRuleCommentWriter.build(rules) — rule comments
    → SmvDeviceModuleBuilder.build(smv, isAttack, intensity, enablePrivacy) — per-device MODULE definitions
    → SmvMainModuleBuilder.build(..., enablePrivacy) — main MODULE (instances, ASSIGN, transitions)
    → SmvSpecificationBuilder.build(...) — CTLSPEC / LTLSPEC
    → Write .smv file to temp dir
  → NusmvExecutor.execute(smvFile) → NusmvResult (per-spec pass/fail + counterexample)
  → SmvTraceParser.parseCounterexampleStates() — parse trace into TraceStateDto list
  → VerificationResultDto (safe, traces, specResults, checkLogs, nusmvOutput)
```

## SMV Generation Details (vs MEDIC-test)

### Device Template Structure (DeviceManifest)

JSON templates in `src/main/resources/deviceTemplate/` define:
- `modes`: list of mode names (e.g. `["MachineState"]`, `["LockState", "DoorState"]`)
- `workingStates`: list of `{name, dynamics[]}` — semicolon-separated multi-mode states (e.g. `"locked;closed"`)
- `apis`: list of `{name, startState, endState, signal}` — actions that change state
- `transitions`: list of `{name, trigger{attribute,relation,value}, endState, signal}` — auto-transitions
- `internalVariables`: list of `{name, values[], lowerBound, upperBound, isInside, trust, privacy, impactedVariables[]}`

### SMV MODULE Generation (SmvDeviceModuleBuilder)

Corresponds to MEDIC's `outModule()`. For each unique device template:
1. `FROZENVAR is_attack: boolean;` (if attack mode)
2. `FROZENVAR trust_<state>: {trusted, untrusted};` for sensors (no APIs)
3. `FROZENVAR privacy_<state>: {private, public};` for sensors (if `enablePrivacy=true`)
4. `VAR <mode>: {state1, state2, ...};` for each mode
5. `VAR <api>_a: boolean;` for signal APIs
6. `VAR <var>: {values} | lower..upper;` for internal variables (attack mode expands sensor numeric ranges by 20%, min +10)
7. `VAR <var>_rate: -1..1;` for impacted variables
8. `VAR trust_<mode>_<state>: {trusted, untrusted};` for non-sensor devices
9. `VAR privacy_<mode>_<state>: {private, public};` for non-sensor devices (if `enablePrivacy=true`)
10. `VAR trust_<var>: {trusted, untrusted};` for variable-level trust
11. `VAR privacy_<var>: {private, public};` for variable-level privacy (if `enablePrivacy=true`)

### Main MODULE Generation (SmvMainModuleBuilder)

Corresponds to MEDIC's `outMain()`. Generates:
1. `FROZENVAR intensity: 0..50;` (if attack mode, frozen — matches MEDIC)
2. Device instance declarations: `<varName>: <ModuleName>;`
3. Environment variable declarations: `a_<varName>: type;` (attack mode expands numeric ranges)
4. Environment variable init value validation (clamp to range, enum membership check)
5. `init(intensity)` computation (sum of `toint(device.is_attack)`, no `next()` needed for FROZENVAR)
6. State transitions via `next(<var>.<mode>)` with rule conditions + API matching
7. Environment variable transitions (sensor assignments, numeric rate-based)
8. API signal transitions (`next(<var>.<api>_a)`)
9. Trust propagation: `next(<var>.trust_<mode>_<state>)` — transitive from rule condition sources (AND logic, stricter than MEDIC's OR)
10. Privacy propagation: `next(<var>.privacy_<mode>_<state>)` — transitive from rule condition sources (only if `enablePrivacy=true`)
11. Content privacy transitions (only if `enablePrivacy=true`)
12. Variable rate transitions and internal variable transitions

Key method: `getStateForMode(multiModeState, modeIndex)` — splits semicolon-separated state strings by mode index.

### Specification Generation (SmvSpecificationBuilder)

7 spec template types (templateId):
- `"1"` always: `CTLSPEC AG(A)`
- `"2"` eventually: `CTLSPEC AF(A)`
- `"3"` never: `CTLSPEC AG !(A)`
- `"4"` immediate: `CTLSPEC AG(IF → AX(THEN))`
- `"5"` response: `CTLSPEC AG(IF → AF(THEN))`
- `"6"` persistence: `LTLSPEC G(IF → F G(THEN))`
- `"7"` safety (trust-based): `CTLSPEC AG(untrusted → !(A))`

Condition types (`targetType`): `state`, `variable`, `api`, `trust`, `privacy`.

### Trace Parsing (SmvTraceParser)

Parses NuSMV counterexample output. Supports both formats:
- Old: `State 1.1:` / New (NuSMV 2.7.1): `-> State: 1.1 <-`
- Extracts `<deviceVarName>.<attribute> = <value>` per state

### Key Differences from MEDIC

| Aspect | MEDIC | This Project |
|--------|-------|-------------|
| Device source | Pre-loaded JSON templates | User-input DeviceVerificationDto + DB templates |
| Variable naming | `deviceName.replace(" ","").toLowerCase()` | `DeviceSmvDataFactory.toVarName()` (safe identifier) |
| Rule source | Parsed from text file (ifttt.txt) | `RuleDto` from REST API |
| Spec source | Hard-coded important devices | `SpecificationDto` from REST API |
| Privacy flag | `now == 3` global flag | `enablePrivacy` request parameter (default false) |
| Trust condition joining | OR (`\|`) — any trusted source propagates | AND (`&`) — all sources must be trusted |
| Trust init | `FROZENVAR` for sensors, `VAR` for actuators | Same pattern |
| Attack model | `FROZENVAR is_attack` + `intensity: 0..50` | Same + sensor numeric range expansion (+20%, min +10) |
| Env var init validation | None | Clamp to range + enum membership check |
| getModeIndexOfState | Counts leading semicolons | Multi-strategy: mode name match → semicolon split → state list lookup |

## API Endpoints

- `POST /api/auth/register|login|logout` — Authentication
- `GET|POST /api/board/nodes|edges|rules|specs|layout|active|templates` — Board CRUD
- `DELETE /api/board/templates/{id}` — Delete custom template
- `POST /api/board/templates/reload` — Reload built-in templates from resources
- `POST /api/verify` — Synchronous verification
- `POST /api/verify/async` — Async verification (returns taskId)
- `GET /api/verify/tasks/{id}` — Task status
- `GET /api/verify/tasks/{id}/progress` — Task progress (0-100%)
- `POST /api/verify/tasks/{id}/cancel` — Cancel task
- `GET /api/verify/traces` — User's all traces
- `GET|DELETE /api/verify/traces/{id}` — Single trace
- `POST /api/verify/simulate` — Random simulation N steps (not persisted)
- `POST /api/verify/simulations` — Simulate and persist
- `GET /api/verify/simulations` — User's all simulation traces (summary)
- `GET /api/verify/simulations/{id}` — Single simulation trace (detail)
- `DELETE /api/verify/simulations/{id}` — Delete simulation trace
- `GET|POST /api/chat/sessions` — Chat sessions (list / create)
- `DELETE /api/chat/sessions/{sessionId}` — Delete chat session
- `GET /api/chat/sessions/{sessionId}/messages` — Chat history
- `POST /api/chat/completions` — SSE streaming chat

## Database Tables (13)

`user`, `device_node`, `device_edge`, `rules`, `specification`, `board_layout`, `board_active`, `device_templates`, `verification_task`, `trace`, `simulation_trace`, `chat_session`, `chat_message`

All tables auto-created by Hibernate (`ddl-auto: update`).

# CLAUDE.md - IoT-Verify Backend

## Project Overview

IoT smart home simulation and formal verification platform using NuSMV model checking. User-defined device instances, rules, and specifications via REST API.

## Tech Stack

- Java 17 + Spring Boot 3.x
- MySQL + Redis (token blacklist, fail-open)
- JWT authentication (BCrypt)
- NuSMV 2.6+ (incompatible with nuXmv)
- Volcengine Ark AI (SSE streaming chat)

## Package Structure

```
cn.edu.nju.Iot_Verify/
├── controller/          # REST API (Result<T> wrapper)
├── service/impl/        # Business logic
├── component/
│   ├── nusmv/           # NuSMV verification
│   │   ├── generator/   # SMV model generation (SmvGenerator + 4 builders + validator)
│   │   ├── executor/    # Process execution
│   │   └── parser/      # Counterexample parsing
│   └── aitool/          # AI tool integration (25 tools)
├── client/              # ArkAiClient wrapper
├── dto/po/repository/   # Data layer
├── security/            # JWT + auth
├── configure/           # Config + thread pools + ProductionSafetyCheck
├── exception/           # Exception hierarchy
└── util/                # Mappers, JsonUtils, JwtUtil
```

## Build & Run

```bash
cd backend
mvn compile          # Compile
mvn spring-boot:run  # Run (requires MySQL; Redis optional)
mvn test             # Run tests
```

## Configuration

Key settings in `application.yaml`:
- `spring.datasource.*` — MySQL connection
- `spring.data.redis.*` — Redis (fail-open when unavailable)
- `jwt.secret` / `jwt.expiration` — JWT settings
- `nusmv.path` — NuSMV executable path
- `nusmv.timeout-ms` — Execution timeout (default 120s)
- `nusmv.max-concurrent` — Global concurrency cap
- `volcengine.ark.*` — AI chat API settings
- `cors.allowed-origins` — CORS origins (comma-separated)

**Production Safety**: `ProductionSafetyCheck` refuses startup in prod/production profile if JWT secret, DB password, or Ark API key are insecure/missing.

## Key Conventions

**API & Controllers**
- Controllers return `Result<T>` wrapper. Use `Result.success()` for void responses.
- `@CurrentUser` parameter always named `userId`.
- Never expose PO objects — always map to DTOs.
- SSE endpoints return `SseEmitter` directly (not wrapped in `Result<T>`).

**Exception Handling**
- `ValidationException` → HTTP 422
- `SmvGenerationException` includes `errorCategory` in response data
- `ServiceUnavailableException` → HTTP 503 (executor saturation)
- `GlobalExceptionHandler` masks internal error messages for security

**NuSMV Generation**
- Identifier sanitization: `DeviceSmvDataFactory.sanitizeSmvToken()` escapes reserved words, removes spaces, handles digit prefixes
- Device resolution: prefer `varName`, allow `templateName` only when unique
- Template validation: `addDeviceTemplate()` runs probe generation before saving
- Debug artifacts: `model.smv`, `request.json`, `output.txt`, `result.json` retained in temp dir

**Security & Concurrency**
- Thread pool context propagation: deep-copy `Authentication`, `UserContextHolder`, `MDC`
- Async task safety: atomic conditional UPDATE queries prevent TOCTOU races
- Redis fail-open: logout revocation degrades gracefully when Redis unavailable
- `@Transactional(readOnly = true)` on all read-only service methods

**Database**
- `device_node` uses composite PK `(id, user_id)` for user isolation
- Entity indexes: `device_edge(user_id)`, `verification_task(user_id)`, `simulation_task(user_id)`
- Unique constraint: `device_templates(user_id, name)`

## NuSMV Verification Flow

```
VerificationRequestDto → SmvGenerator.generate()
  → DeviceSmvDataFactory.buildDeviceSmvMap() (merge user devices + templates)
  → SmvModelValidator.validate() (P1-P5 checks)
  → SmvDeviceModuleBuilder + SmvMainModuleBuilder + SmvSpecificationBuilder
  → Write .smv + request.json to temp dir
→ NusmvExecutor.execute() → NusmvResult (per-spec pass/fail + counterexample)
  → Save output.txt
→ SmvTraceParser.parseCounterexampleStates() → TraceStateDto list
→ VerificationResultDto (safe, traces, specResults, checkLogs, nusmvOutput)
  → Save result.json
```

**SMV Generation Key Points**
- Device templates in `src/main/resources/deviceTemplate/` define modes, states, APIs, transitions, internal variables
- `SmvDeviceModuleBuilder`: generates MODULE per template (FROZENVAR for sensors, VAR for actuators, trust/privacy propagation)
- `SmvMainModuleBuilder`: generates main MODULE (device instances, env vars, state transitions, trust/privacy propagation)
- `SmvSpecificationBuilder`: 7 spec templates (always, eventually, never, immediate, response, persistence, safety)
- Attack mode: `FROZENVAR is_attack` + `intensity: 0..50` + proportional sensor range expansion
- Trust propagation: AND logic (all sources must be trusted)
- Privacy: optional via `enablePrivacy` flag

**Trace Parsing**
- Supports multiple NuSMV output formats: `State 1.1:`, `-> State: 1.1 <-`, `State: 1.1`, and variants
- Extracts `<deviceVarName>.<attribute> = <value>` per state

## API Endpoints

**Auth**: `POST /api/auth/register|login|logout`

**Board**: `GET|POST /api/board/nodes|edges|rules|specs|layout|active|templates`, `DELETE /api/board/templates/{id}`, `POST /api/board/templates/reload`

**Verification**:
- Sync: `POST /api/verify`
- Async: `POST /api/verify/async`, `GET /api/verify/tasks/{id}`, `GET /api/verify/tasks/{id}/progress`, `POST /api/verify/tasks/{id}/cancel`
- Traces: `GET /api/verify/traces`, `GET|DELETE /api/verify/traces/{id}`

**Simulation**:
- Sync: `POST /api/verify/simulate`
- Async: `POST /api/verify/simulate/async`, `GET /api/verify/simulations/tasks/{id}`, `GET /api/verify/simulations/tasks/{id}/progress`, `POST /api/verify/simulations/tasks/{id}/cancel`
- Traces: `POST|GET /api/verify/simulations`, `GET|DELETE /api/verify/simulations/{id}`

**Chat**: `GET|POST /api/chat/sessions`, `DELETE /api/chat/sessions/{sessionId}`, `GET /api/chat/sessions/{sessionId}/messages`, `POST /api/chat/completions` (SSE)

## Database

14 tables: `user`, `device_node`, `device_edge`, `rules`, `specification`, `board_layout`, `board_active`, `device_templates`, `verification_task`, `simulation_task`, `trace`, `simulation_trace`, `chat_session`, `chat_message`

Auto-created by Hibernate (`ddl-auto: update`).

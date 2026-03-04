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
│   │   │   ├── SmvBoundsUtils.java        # Shared numeric-bound utility (resolveEffectiveUpperBound)
│   │   │   ├── SmvRelationUtils.java      # Shared relation normalization (EQ/NEQ/GT/GTE/LT/LTE/IN/NOT_IN)
│   │   │   ├── PropertyDimension.java     # TRUST/PRIVACY enum
│   │   │   ├── data/    # DeviceSmvData, DeviceSmvDataFactory
│   │   │   └── module/  # SmvDeviceModuleBuilder, SmvMainModuleBuilder, SmvRuleCommentWriter, SmvSpecificationBuilder
│   │   ├── executor/    # NusmvExecutor (process execution + per-spec parsing)
│   │   └── parser/      # SmvTraceParser (counterexample → TraceStateDto)
│   └── aitool/          # AI tool integration (25 tools across 7 categories: board, node, rule, simulation, spec, template, verification)
├── client/              # ArkAiClient (Volcengine Ark AI SDK wrapper)
├── dto/                 # Data transfer objects (by domain: auth, board, chat, device, rule, spec, simulation, trace, verification)
├── po/                  # JPA entities (14 tables + DeviceEdgeId/DeviceNodeId composite keys; DeviceNodePo uses @IdClass(DeviceNodeId) for user-scoped node isolation)
├── repository/          # Spring Data JPA repositories (14)
├── security/            # JWT filter, @CurrentUser resolver, UserContextHolder, SecurityConfig
├── configure/           # NusmvConfig, ThreadConfig, ThreadPoolConfig, WebConfig, ProductionSafetyCheck
                         # All executors are centrally managed in configure/ (chat, verificationTask, syncVerification, syncSimulation, simulationTask)
                         # ProductionSafetyCheck: @PostConstruct guard — in prod/production profile, refuses startup if JWT secret is null/blank/insecure-default, DB password is insecure default, or Ark API key is null/blank/placeholder
├── exception/           # BaseException hierarchy + GlobalExceptionHandler
└── util/
    ├── mapper/          # PO ↔ DTO mappers (manual, not MapStruct): UserMapper, DeviceNodeMapper, DeviceEdgeMapper, RuleMapper, SpecificationMapper, ChatMapper, TraceMapper, VerificationTaskMapper, SimulationTaskMapper, SimulationTraceMapper
    ├── JsonUtils.java   # JSON serialization helpers
    ├── JwtUtil.java     # JWT token generation/validation
    ├── FunctionParameterSchema.java  # AI function parameter schema builder
    └── LevenshteinDistanceUtil.java  # Edit distance (used by AI tools)
```

## Build & Run

```bash
cd backend
mvn compile          # Compile
mvn spring-boot:run  # Run (requires MySQL; Redis optional — fail-open for logout revocation)
mvn test             # Run tests (pom.xml configures surefire with -Djdk.attach.allowAttachSelf=true -XX:+EnableDynamicAgentLoading for JDK 17 Mockito/ByteBuddy compatibility)
```

Test workflow: `powershell -File test_workflow.ps1` (end-to-end API test, requires running server)

## Configuration

Key config in `src/main/resources/application.yaml`:
- `spring.datasource.*` — MySQL connection
- `spring.data.redis.*` — Redis connection (token blacklist: SHA-256 hashed keys, fail-open degradation — logout revocation ineffective when Redis is down (logged-out tokens remain valid until expiry), throttled error logging with consecutive-failure alerting at threshold 10; requires `commons-pool2` for Lettuce connection pooling)
- `jwt.secret` / `jwt.expiration` — JWT settings (supports `${JWT_SECRET:default}` pattern)
- `nusmv.path` — NuSMV executable path (OS-specific); `@NotBlank` validated at startup
- `nusmv.command-prefix` — Optional prefix (e.g. `wsl` on Windows)
- `nusmv.timeout-ms` — Execution timeout (default 120000); validated at startup via `@Min(100)` on `NusmvConfig`
- `nusmv.max-concurrent` — Global NuSMV concurrency cap shared by verification/simulation
- `nusmv.acquire-permit-timeout-ms` — Timeout for waiting NuSMV execution permit
- `thread-pool.*` — Executor sizing and queue limits (sync executors use small queues for fast-fail)
- `volcengine.ark.*` — AI chat API settings (including configurable `timeout-minutes` via `ARK_TIMEOUT_MINUTES`)
- `cors.allowed-origins` — CORS allowed origins, comma-separated (SecurityConfig trims whitespace around delimiters)
- `server.port` — HTTP port (default 8080)
- **Production safety**: `ProductionSafetyCheck` — when `spring.profiles.active` includes `prod`/`production`, startup fails if `jwt.secret` is null/blank/insecure-default, `spring.datasource.password` is the insecure default, or `volcengine.ark.api-key` is null/blank/placeholder (`JWT_SECRET` / `DB_PASSWORD` / `VOLCENGINE_API_KEY`). `PRODUCTION_MODE` is removed; profile detection is unified on Spring profiles. Local dev (no profile) always starts normally.

## Key Conventions

- Controllers return `Result<T>` wrapper. Use `Result.success()` for void responses (never `success(null)`).
- Controller `@CurrentUser` parameter is always named `userId`.
- Service interfaces in `service/`, implementations in `service/impl/`.
- Controllers never expose PO objects — always map to DTOs.
- CORS is configured only in `SecurityConfig` (not WebConfig).
- `@Value` annotations reference property keys without inline defaults — `application.yaml` is the single source of truth for default values. Exception: `ProductionSafetyCheck` uses `@Value("${key:}")` (empty-string default) so that missing properties don't crash injection before `@PostConstruct` can report the violation. `@ConfigurationProperties` field defaults are acceptable when consistent with YAML (e.g., `ThreadPoolConfig`).
- JSON serialization: `JsonUtils.toJson()` for objects, `JsonUtils.toJsonOrEmpty()` for lists.
- Device templates are in `src/main/resources/deviceTemplate/`.
- `ValidationException` uses HTTP 422 (not 400). Handler and exception code are aligned.
- `SmvGenerationException` has a dedicated handler in `GlobalExceptionHandler` that includes `data.errorCategory` (and keeps `[errorCategory]` prefix in message for compatibility). Common categories include `TEMPLATE_NOT_FOUND`, `TEMPLATE_LOAD_ERROR`, `MANIFEST_PARSE_ERROR`, `ILLEGAL_TRIGGER_ATTRIBUTE`, `ILLEGAL_TRIGGER_RELATION`, `INVALID_STATE_FORMAT`, `ENV_VAR_CONFLICT`, `AMBIGUOUS_DEVICE_REFERENCE`, `TRUST_PRIVACY_CONFLICT`, `INVALID_BUILDER_INPUT`, etc.
- `SmvModelValidator` runs before SMV text generation. Hard validations throw `SmvGenerationException`; soft validations (unknown user variables, stateless device with state) only log warnings.
- Rule/spec device resolution is strict: prefer `varName`, allow `templateName` only when uniquely matched; ambiguous matches throw `AMBIGUOUS_DEVICE_REFERENCE`.
- NuSMV identifier sanitization is centralized in `DeviceSmvDataFactory.sanitizeSmvToken()` — removes spaces, replaces non-alphanumeric chars with `_`, prepends `_` if digit-prefixed, and escapes reserved words case-insensitively (including `W`) by prepending `_`. Device IDs converted by `toVarName()` follow the same safety constraints.
- Template NuSMV pre-check: `BoardStorageServiceImpl.addDeviceTemplate()` validates the manifest and runs a probe `SmvGenerator.generate()` before saving; failures return 400 (invalid template) or 500 (infrastructure). Temp SMV files are cleaned up in `finally`.
- `DeviceSmvDataFactory.loadManifest()` returns `null` for null `templateName` or missing DB template (caller `buildDeviceSmvMap()` logs warning and skips the device). On actual errors: `BaseException` re-thrown, JSON parse → `MANIFEST_PARSE_ERROR`, other → `TEMPLATE_LOAD_ERROR`.
- `getModeIndexOfState()` uses exact-match or `mode + "_"` prefix matching (not `contains()`), preventing false positives like mode "on" matching state "offline".
- `GlobalExceptionHandler` masks internal messages: `IllegalArgumentException` → generic "Invalid request parameter" (400), `IllegalStateException` → "Internal server error" (500), `DataIntegrityViolationException` → "Data conflict, the resource may already exist" (409).
- `JwtUtil.@PostConstruct` warns if JWT secret is still the insecure default when a production profile (`prod`/`production`) is active (case-insensitive matching via `toLowerCase()`). `ProductionSafetyCheck` hard-fails startup if JWT secret is null, blank, or starts with the insecure default prefix; also catches insecure DB password and null/blank/placeholder API key. `JwtUtil` provides a WARN-level defense-in-depth log.
- `JwtAuthenticationFilter` wraps `getUserIdFromToken()` in try-catch — malformed tokens are treated as unauthenticated (no 500).
- Thread pool context propagation: `ThreadConfig.TaskDecorator` deep-copies `Authentication` (new `UsernamePasswordAuthenticationToken` + new `ArrayList` for authorities), `UserContextHolder.userId`, and `MDC` context map into child threads; `finally` clears all three.
- Async task safety: `completeTask`/`failTask` use atomic conditional UPDATE queries (`WHERE status <> CANCELLED`) instead of check-then-save, eliminating TOCTOU race conditions. `handleCancellation` uses `cancelTaskIfStillActive` (`WHERE status IN (PENDING, RUNNING)`) to prevent overwriting COMPLETED/FAILED with CANCELLED. Repository methods return `int` (affected rows); 0 means task was already cancelled/finished.
- `@Transactional(readOnly = true)` on all read-only service methods: `BoardStorageServiceImpl` (`getNodes`, `getEdges`, `getSpecs`, `getRules`, `getActive`, `getDeviceTemplates`), `VerificationServiceImpl` (`getTask`, `getTaskProgress`, `getUserTraces`, `getTrace`), `SimulationServiceImpl` (`getTask`, `getTaskProgress`, `getUserSimulations`, `getSimulation`), `ChatServiceImpl` (`getUserSessions`, `getHistory`).
- `TransactionTemplate` used in `VerificationServiceImpl.saveTraces()` and `ChatServiceImpl.processStreamChat()` (initial save, tool loop saves, final save) to wrap saves that can't use `@Transactional` due to Spring proxy limitations.
- Redis consecutive-failure alerting: `RedisTokenBlacklistService` tracks consecutive check/blacklist failures via `AtomicInteger`; logs ERROR every 10 consecutive failures (`% ALERT_THRESHOLD`) to detect persistent Redis degradation without going silent after the first alert.
- Request validation: `@NotEmpty` on devices lists (rejects both null and empty), `@Size(max=10000)` on chat content, `@NotNull` on all `@RequestBody` parameters in `BoardStorageController` (enforced via class-level `@Validated`).
- `DELETE /api/verify/traces/{id}` returns 404 (via `ResourceNotFoundException`) if trace not found (previously silent 200).
- Entity indexes: `device_edge(user_id)`, `verification_task(user_id)`, `simulation_task(user_id)`. Unique constraint: `device_templates(user_id, name)` — requires no duplicate data before first deployment.
- `SmvSpecificationBuilder.build()` accepts `enablePrivacy` parameter; when privacy specs are encountered with `enablePrivacy=false`, they are skipped with a `CTLSPEC FALSE` placeholder (defense-in-depth, upstream `validateNoPrivacySpecs` is the primary guard).
- `DeviceSmvDataFactory.computeIdentifiers()` guards digit-prefixed identifiers and checks NuSMV reserved words on `result` (varName), `base` (moduleName prefix from templateName), and `suffix` before building module names.
- Chat history (`getHistory`) filters out tool-role messages, assistant tool-call-request messages, and adjacent "Calling tool..." placeholders before returning to frontend.
- `device_node` table uses composite PK `(id, user_id)` — different users can have nodes with the same ID. Existing databases need manual `ALTER TABLE` to add `user_id` to the primary key.
- Sync verification/simulation unwrap `ExecutionException` and rethrow `SmvGenerationException` so `errorCategory` is preserved in API responses.
- SSE endpoints (e.g. `/api/chat/completions`) return `SseEmitter` directly, not wrapped in `Result<T>`.
- Exception hierarchy: `BaseException(code, message)` → `BadRequestException(400)`, `UnauthorizedException(401)`, `ForbiddenException(403)`, `ResourceNotFoundException(404)`, `ConflictException(409)`, `ValidationException(422)`, `InternalServerException(500)` → `SmvGenerationException`, `ServiceUnavailableException(503)`.
- Sync verification (`/api/verify`) and sync simulation (`/api/verify/simulate`) now throw `ServiceUnavailableException(503)` when their executors are saturated.
- Async verification (`/api/verify/async`) and async simulation (`/api/verify/simulate/async`) throw `ServiceUnavailableException` on `TaskRejectedException` (thread pool full), returning 503 via `GlobalExceptionHandler`. Controllers return `Result<Long>` (not `ResponseEntity`).
- Chat completion (`/api/chat/completions`) throws `ServiceUnavailableException(503)` when `chatExecutor` is saturated.
- Sync request timeout path uses `future.cancel(true)` and `ThreadPoolExecutor.purge()` to reduce cancelled-task buildup in queue.
- Debug artifacts in temp dir: `request.json` is saved right after `model.smv` generation (verify/sim); `output.txt` is NuSMV raw output; `result.json` is saved when a result object is produced. Temp directories (`nusmv_*`) are retained for post-mortem debugging (not deleted after each run).

## 2026-03-03 Sync Notes

### NuSMV Generation Fixes
- Identifier sanitization is now reserved-word aware (case-insensitive): `DeviceSmvDataFactory.sanitizeSmvToken()` escapes NuSMV reserved words by prepending `_` (including `W`), and still handles spaces/invalid chars/digit prefixes.
- `DeviceSmvDataFactory.toVarName()` now also defends digit-prefixed IDs and reserved words, so spec/device identifiers cannot generate illegal NuSMV symbols.
- Trust/privacy pipeline is now defense-in-depth:
  - normalize on ingestion via `normalizeTrustPrivacy()` (trim + lowercase),
  - validate enum legality in `SmvModelValidator.validatePropertyValues()` (instance values, content privacy, manifest variable trust/privacy, workingState privacy),
  - normalize again at emit time in `SmvDeviceModuleBuilder.appendInitialProperty()`.
- Content privacy emit has null fallback: `SmvDeviceModuleBuilder.appendAssignments()` writes `public` when `ci.getPrivacy()==null`, then normalizes before SMV output.
- Numeric upper-bound expansion formula is centralized in `SmvBoundsUtils.resolveEffectiveUpperBound()` and shared by:
  - device/module numeric declarations,
  - main env declarations + init validation,
  - transition clamp ranges.
- `resolveEffectiveUpperBound()` now defensively clamps negative `intensity` to `0` (generator entry still clamps to `0..50`).
- A10 range safety is closed in transitions: `SmvMainModuleBuilder` clamps numeric next-candidates with `max(lower, min(upper, expr))` in WITH-rate/no-rate branches, including boundary branches and internal-variable branches.
- `SmvSpecificationBuilder.build()` now takes 5th parameter `enablePrivacy`; when privacy specs leak through with `enablePrivacy=false`, they are skipped with a `CTLSPEC FALSE` placeholder (defense-in-depth, upstream `validateNoPrivacySpecs` is the primary guard).
- Regression tests were extended in `SmvGeneratorFixesTest` for:
  - WITH-rate extreme-NCR boundary clamp,
  - internal-variable boundary clamp,
  - `SmvBoundsUtils` edge cases (`range=0`, negative intensity).

### Backend Hardening (Security, Thread Safety, Data Integrity)
- **Production safety guard**: `ProductionSafetyCheck` (@PostConstruct) — when `spring.profiles.active` includes `prod`/`production`, refuses startup if `jwt.secret` is null/blank/insecure-default, `spring.datasource.password` is the insecure default, or `volcengine.ark.api-key` is null/blank/placeholder (`JWT_SECRET` / `DB_PASSWORD` / `VOLCENGINE_API_KEY`). `PRODUCTION_MODE` has been removed; all production config validation is centralized in `ProductionSafetyCheck`. Additionally, `JwtUtil.@PostConstruct` logs WARN if the default JWT secret is active in production profile (defense-in-depth); profile matching is case-insensitive (`toLowerCase()`).
- **Exception handler hardening**: `IllegalArgumentException` → masked generic message (400), `IllegalStateException` → "Internal server error" (500), new `DataIntegrityViolationException` → 409 CONFLICT.
- **Thread pool context propagation**: `ThreadConfig.TaskDecorator` deep-copies `Authentication` (new `UsernamePasswordAuthenticationToken` + new `ArrayList<>` for authorities), `UserContextHolder.userId`, and `MDC` context map into child threads. Prevents cross-task mutation pollution.
- **Async task TOCTOU elimination**: `completeTask`/`failTask` replaced check-then-save with atomic conditional UPDATE queries (`WHERE status <> CANCELLED`). `handleCancellation` replaced stale entity `save()` with `cancelTaskIfStillActive` (`WHERE status IN (PENDING, RUNNING)`) to prevent overwriting COMPLETED/FAILED with CANCELLED. Repository methods `completeTaskIfNotCancelled` / `failTaskIfNotCancelled` / `cancelTaskIfStillActive` return `int` (0 = already cancelled/finished). `@Modifying(clearAutomatically = true)` ensures stale persistence context is cleared after JPQL UPDATE. `TransactionTemplate` used for trace saving in `VerificationServiceImpl` and chat message saving in `ChatServiceImpl.processStreamChat()`.
- **Redis resilience**: `RedisTokenBlacklistService` tracks consecutive failures via `AtomicInteger`; logs ERROR every 10 consecutive failures (`failures % ALERT_THRESHOLD == 0`) — periodic, not one-shot.
- **Request validation tightened**: `@NotEmpty` on devices lists (rejects `[]`), `@Size(max=10000)` on chat content, `@NotNull` on all `@RequestBody` in `BoardStorageController` (enforced via class-level `@Validated`).
- **Read-only transactions**: `@Transactional(readOnly = true)` added to all read-only service methods across `BoardStorageServiceImpl`, `VerificationServiceImpl`, `SimulationServiceImpl`, and `ChatServiceImpl` (`getUserSessions`, `getHistory`).
- **Entity indexes**: `device_edge(user_id)`, `verification_task(user_id)`, `simulation_task(user_id)`. Unique constraint: `device_templates(user_id, name)`.
- **DTO progress field**: `VerificationTaskDto.progress` and `SimulationTaskDto.progress` exposed to API (additive, backward-compatible).
- **VerificationTaskDto consistency**: Added `@NoArgsConstructor`, `@AllArgsConstructor`, `@JsonInclude(NON_NULL)` to match `SimulationTaskDto` (null fields omitted from JSON).
- **AI tool safety**: `AiToolManager.execute()` has catch-all safety net returning generic `"Tool execution failed due to an internal error"` (never leaks `e.getMessage()`). `AddTemplateTool` pre-computes `tolerantMapper` in `@PostConstruct`. `AddNodeTool` uses null-safe numeric parsing (`parseDoubleOrNull`/`parseIntOrNull`) — JSON `null`, non-numeric strings, and empty strings all yield `null`, correctly triggering `NodeServiceImpl` default values instead of silently converting to 0.
- **ArkAiClient timeout**: configurable via `volcengine.ark.timeout-minutes` / `ARK_TIMEOUT_MINUTES` (default 5).
- **JsonUtils**: registered `JavaTimeModule`, added `fromJsonToStringList()` / `fromJsonList()` helpers.
- **Delete trace 404**: `VerificationServiceImpl.deleteTrace()` now throws `ResourceNotFoundException` for missing traces (was silent 200).
- **Async controller pattern**: `VerificationController.verifyAsync()` and `SimulationController.simulateAsync()` return `Result<Long>` (not `ResponseEntity<Result<Long>>`); `TaskRejectedException` throws `ServiceUnavailableException` handled by `GlobalExceptionHandler`.
- **Temp file retention**: `cleanupTempFile()` in both `VerificationServiceImpl` and `SimulationServiceImpl` is intentionally a no-op — `nusmv_*` temp directories are kept for post-mortem debugging.
- **Surefire JVM args**: `pom.xml` configures `maven-surefire-plugin` with `-Djdk.attach.allowAttachSelf=true -XX:+EnableDynamicAgentLoading` to fix Mockito/ByteBuddy `MockMaker` initialization failures on JDK 17.
- **Server error message suppression**: `application.yaml` sets `server.error.include-message: never` and `include-binding-errors: never` to prevent Spring's `/error` endpoint from leaking internal exception messages.
- **SecurityConfig ObjectMapper**: `SecurityFilterChain` uses Spring-managed `ObjectMapper` (injected via `@RequiredArgsConstructor`) instead of `new ObjectMapper()`, inheriting `JavaTimeModule` and other registered modules.
- **ArkAiClient ObjectMapper**: Uses Spring-managed `ObjectMapper` via constructor injection (was `new ObjectMapper()` field initializer), ensuring consistent serialization configuration with the rest of the application.
- **ArkAiClient parse logging**: `parseToolMessage()` and `parseAssistantToolCalls()` now log at DEBUG level on JSON parse fallback (was silent `catch (Exception ignore)`), improving observability for structured format parsing failures. Both methods use `content.stripLeading().startsWith("{")` pre-check (tolerant of leading whitespace/newlines) to skip JSON parsing for plain text messages, avoiding unnecessary exception overhead in high-volume history conversion.

## 2026-03-04 Sync Notes

### Stateless Device Empty InitState Fix
- 16 no-mode sensor templates (Weather, Clock, Temperature Sensor, Humidity Sensor, etc.) have `"InitState": ""`. Previously `NodeServiceImpl.getInitStateFromTemplate()` returned the empty string as-is, resulting in `state=""` persisted to DB. When the frontend subsequently saved the board via `POST /api/board/nodes`, `DeviceNodeDto.state`'s `@NotBlank` validation rejected it (400).
- **`NodeServiceImpl.getInitStateFromTemplate()`**: now checks `isBlank()` after reading `InitState`; empty/blank values fall back to `HARD_FALLBACK_STATE` (`"Working"`). Log message corrected from `"does not contain InitState"` to `"has missing or blank InitState"`.
- **`DeviceNodeMapper.toDto()`**: sanitizes blank/null `state` to `"Working"` (`FALLBACK_STATE`) on read, preventing historical dirty data from triggering `@NotBlank` validation on subsequent GET → POST round-trips.
- 3 new unit tests in `NodeServiceImplMutationTest`: empty InitState, normal InitState, missing InitState key.

### Device Template Fix
- **Sprinkler Controller.json**: API definitions had erroneous key `"s"` instead of `"Assignments"` (2 occurrences fixed).

## NuSMV Verification Flow

```
VerificationRequestDto (devices, rules, specs, isAttack, intensity, enablePrivacy)
  → SmvGenerator.generate()
    → DeviceSmvDataFactory.buildDeviceSmvMap() — merge user device instances with templates
    → SmvModelValidator.validate() — hard checks (P1 trigger attribute/relation, P2 state format, P3 env conflicts, P4 property value legality, P5 trust/privacy consistency)
    → SmvRuleCommentWriter.build(rules) — rule comments
    → SmvDeviceModuleBuilder.build(smv, isAttack, intensity, enablePrivacy) — per-device MODULE definitions
    → SmvMainModuleBuilder.build(..., enablePrivacy) — main MODULE (instances, ASSIGN, transitions)
    → SmvSpecificationBuilder.build(...) — CTLSPEC / LTLSPEC
    → Write .smv file to temp dir
  → Save request snapshot to `request.json` in same temp dir (after model generation)
  → NusmvExecutor.execute(smvFile) → NusmvResult (per-spec pass/fail + counterexample)
    → Save NuSMV raw output to `output.txt` in same temp dir
  → SmvTraceParser.parseCounterexampleStates() — parse trace into TraceStateDto list
  → VerificationResultDto (safe, traces, specResults, checkLogs, nusmvOutput)
  → Save wrapped response to `result.json` when result object exists
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
2. `FROZENVAR trust_<var>: {trusted, untrusted};` for sensor internal variables (sensor trust is inherent — frozen)
3. `FROZENVAR privacy_<var>: {public, private};` for sensor internal variables (if `enablePrivacy=true`)
4. `FROZENVAR privacy_<content>: {public, private};` for content with `IsChangeable=false` (if `enablePrivacy=true`)
5. `VAR <mode>: {state1, state2, ...};` for each mode
6. `VAR <api>_a: boolean;` for signal APIs
7. `VAR <var>: {values} | lower..upper;` for internal variables (attack mode expands sensor numeric ranges proportionally: `expansion=(upper-lower)/5*intensity/50`)
8. `VAR <var>_rate: <min..max>;` for impacted variables (derived from `Dynamics.ChangeRate`, fallback `-10..10`)
9. `VAR trust_<mode>_<state>: {trusted, untrusted};` for non-sensor (actuator) devices — trust propagated via rules, must be VAR
10. `VAR trust_<var>: {trusted, untrusted};` for non-sensor (actuator) variable-level trust
11. `VAR privacy_<mode>_<state>: {private, public};` for non-sensor (actuator) devices (if `enablePrivacy=true`)
12. `VAR privacy_<var>: {private, public};` for non-sensor (actuator) variable-level privacy (if `enablePrivacy=true`)
13. `VAR privacy_<content>: {public, private};` for content with `IsChangeable=true` (if `enablePrivacy=true`)

### Main MODULE Generation (SmvMainModuleBuilder)

Corresponds to MEDIC's `outMain()`. Generates:
1. `FROZENVAR intensity: 0..50;` (if attack mode, frozen — matches MEDIC)
2. Device instance declarations: `<varName>: <ModuleName>;`
3. Environment variable declarations: `a_<varName>: type;` (attack mode expands numeric ranges)
4. Environment variable init value validation (clamp to range, enum membership check)
5. `init(intensity)` computation (sum of `toint(device.is_attack)`, no `next()` needed for FROZENVAR)
6. State transitions via `next(<var>.<mode>)` with rule conditions + API matching (self-target conditions auto downgrade to current-state reads to avoid recursive `next(...)` definitions)
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

Spec fail-closed behavior:
- General invalid spec conditions degrade to `CTLSPEC FALSE -- invalid spec: ...`.
- Ambiguous device reference (`AMBIGUOUS_DEVICE_REFERENCE`) is treated as a hard generation error, not degraded.

### Trace Parsing (SmvTraceParser)

Parses NuSMV counterexample output. Supports both formats:
- Old: `State 1.1:` / New (NuSMV 2.7.1): `-> State: 1.1 <-`
- Extracts `<deviceVarName>.<attribute> = <value>` per state

### Key Differences from MEDIC

| Aspect | MEDIC | This Project |
|--------|-------|-------------|
| Device source | Pre-loaded JSON templates | User-input DeviceVerificationDto + DB templates |
| Variable naming | `deviceName.replace(" ","").toLowerCase()` | `DeviceSmvDataFactory.toVarName()` (safe identifier); mode/state names cleaned via `sanitizeSmvToken()` |
| Rule source | Parsed from text file (ifttt.txt) | `RuleDto` from REST API |
| Spec source | Hard-coded important devices | `SpecificationDto` from REST API |
| Privacy flag | `now == 3` global flag | `enablePrivacy` request parameter (default false) |
| Trust condition joining | OR (`\|`) — any trusted source propagates | AND (`&`) — all sources must be trusted |
| Trust init | `FROZENVAR` for sensors, `VAR` for actuators | Same pattern |
| Attack model | `FROZENVAR is_attack` + `intensity: 0..50` | Same + proportional sensor numeric range expansion (`expansion=range/5*intensity/50`) |
| Env var init validation | None | Clamp to range + enum membership check |
| getModeIndexOfState | Counts leading semicolons | Multi-strategy: semicolon split → state list lookup → mode name exact/prefix match (no substring `contains()`) |

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
- `POST /api/verify/simulate/async` — Async simulation (returns taskId)
- `GET /api/verify/simulations/tasks/{id}` — Simulation task status
- `GET /api/verify/simulations/tasks/{id}/progress` — Simulation task progress (0-100%)
- `POST /api/verify/simulations/tasks/{id}/cancel` — Cancel simulation task
- `POST /api/verify/simulations` — Simulate and persist
- `GET /api/verify/simulations` — User's all simulation traces (summary)
- `GET /api/verify/simulations/{id}` — Single simulation trace (detail)
- `DELETE /api/verify/simulations/{id}` — Delete simulation trace
- `GET|POST /api/chat/sessions` — Chat sessions (list / create)
- `DELETE /api/chat/sessions/{sessionId}` — Delete chat session
- `GET /api/chat/sessions/{sessionId}/messages` — Chat history
- `POST /api/chat/completions` — SSE streaming chat

## Database Tables (14)

`user`, `device_node`, `device_edge`, `rules`, `specification`, `board_layout`, `board_active`, `device_templates`, `verification_task`, `simulation_task`, `trace`, `simulation_trace`, `chat_session`, `chat_message`

All tables auto-created by Hibernate (`ddl-auto: update`).

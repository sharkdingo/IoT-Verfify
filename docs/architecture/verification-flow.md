# Verification Flow

End-to-end path of a verification request: from the REST call, through SMV generation
and NuSMV execution, to a parsed result with counterexample traces and optional
auto-fix.

Request/response field contract → [../api/verification.md](../api/verification.md).
SMV generation internals → [nusmv-model.md](nusmv-model.md).

Verified against code on 2026-07-05. Source: `controller/VerificationController.java`,
`controller/SimulationController.java`, `service/impl/VerificationServiceImpl.java`,
`service/impl/SimulationServiceImpl.java`, `component/nusmv/`.

---

## Pipeline

```
User: devices + rules + at least one spec (+ isAttack, intensity, enablePrivacy)
        │  POST /api/verify   (VerificationRequestDto)
        ▼
VerificationController.verify(userId, request)
        ▼
VerificationServiceImpl.doVerify()
        │
        ├─ [1] SmvGenerator.generate(...)          → model.smv (+ request.json)
        │        DeviceSmvDataFactory → SmvModelValidator (P1–P5)
        │        → SmvRuleCommentWriter → SmvDeviceModuleBuilder
        │        → SmvMainModuleBuilder → SmvSpecificationBuilder
        │
        ├─ [2] NusmvExecutor.execute(smvFile)      → run NuSMV, per-spec true/false + counterexample
        │        (semaphore-bounded, timeout-guarded)
        │
        └─ [3] SmvTraceParser.parseCounterexampleStates(...)  → List<TraceStateDto>
        ▼
VerificationResultDto { safe, specResults, traces, checkLogs, nusmvOutput,
disabledRuleCount, skippedSpecCount }
        │
        ├─ all emitted specs pass → safe: true
        └─ a violation    → counterexample trace(s) saved + optional auto-fix
```

- **[1] Generation** turns the request plus the user's device templates into a `.smv`
  model. Validation (P1–P5) runs before any text is emitted — see
  [spec-templates.md](spec-templates.md) for the rules and
  [nusmv-model.md](nusmv-model.md) for the builders and identifier handling.
  The REST DTO rejects empty `specs` before this stage; generator-level skipped specs
  still surface through `skippedSpecCount` and `[spec-skipped]` logs.
- **[2] Execution** invokes NuSMV as a subprocess through `NusmvExecutor`, which bounds
  concurrency with a semaphore (`NUSMV_MAX_CONCURRENT`) and enforces `NUSMV_TIMEOUT_MS`.
  Output parsing depends on NuSMV's standard English output format (2.6–2.7; not
  nuXmv).
- **[3] Parsing** converts the NuSMV counterexample text into `TraceStateDto` objects.

When a violation is found, the trace is persisted automatically (no `saveTrace` flag),
and the client can then request fault localization and fixes — see
[auto-fix.md](auto-fix.md).

---

## Sync vs async vs simulation

| Mode | Endpoint | Returns | When |
| :--- | :--- | :--- | :--- |
| Sync verify | `POST /api/verify` | `VerificationResultDto` | Small models, immediate result |
| Async verify | `POST /api/verify/async` | `taskId` (Long) | Large models; poll status/progress, cancellable |
| Simulation | `POST /api/simulate` | `SimulationResultDto` | Observe N random steps; no spec checking, not persisted |
| Saved simulation | `POST /api/simulate/traces` | `SimulationTraceDto` | Synchronous simulation plus persisted history entry |
| Async simulation | `POST /api/simulate/async` | `taskId` (Long) | Runs on the simulation task pool; completed tasks persist a trace and expose `simulationTraceId` |

Async tasks run on a dedicated thread pool; status transitions
(`complete`/`fail`/`cancel`) are atomic conditional updates to avoid TOCTOU races (see
`CHANGELOG.md`, 2026-03-03). Progress is exposed 0–100 via
`GET /api/verify/tasks/{id}/progress` and
`GET /api/simulate/tasks/{id}/progress`.

Simulation history is intentionally separate from verification traces. A plain
`POST /api/simulate` response is transient, while `POST /api/simulate/traces` and
completed async simulation tasks store `SimulationTrace` rows that the frontend can
list, replay, and delete through the history panel.

Full endpoint list: [../api/rest-endpoints.md](../api/rest-endpoints.md). Field-level
shapes: [../api/verification.md](../api/verification.md).

---

## Counterexample trace structure

_Migrated from the former `NuSMV_Module_Documentation.md` §8._

When NuSMV reports a spec as false, it emits a counterexample (a violating execution
path). `SmvTraceParser` parses it into structured data.

### Raw NuSMV counterexample format

The example below matches the `isAttack=true, intensity=50, enablePrivacy=true` scenario
from the complete SMV example in [nusmv-model.md](nusmv-model.md).

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

### Parsed TraceStateDto structure

In `TraceDeviceDto`, `state` is the current state value and `mode` is the state-machine
name. The old `newState` field was removed in favor of `state` + `mode`; historical JSON
is mapped automatically via `@JsonAlias("newState")`.

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

### Parsing and filtering/routing rules

- Multiple NuSMV state-line formats are accepted: `State X.Y:` (old), `-> State: X.Y <-`
  (new), and variants such as `State: X.Y` and `-> State X.Y <-`; the regex tolerates
  optional whitespace and separators.
- `device.var = value` matches a device internal variable; `a_varName = value` and other
  bare variables (such as `intensity = value`) match environment/global variables.
- `TraceDeviceDto.templateName` and `TraceDeviceDto.deviceLabel` are auto-filled; state
  names are matched back via `DeviceSmvData.states`.
- `*_rate` and `*_a` control variables are **filtered out** and do not enter the output.
- `is_attack` **is kept** in the output, so the frontend can show which devices were
  attacked along the counterexample path.
- `trust_` prefix routing: entries matching the `mode_state` format go into
  `trustPrivacy[]` (with `trust` as a boolean); all others go into `variables[].trust` (a
  string).
- `privacy_` prefix: all entries go into `privacies[]` (with the prefix stripped from the
  entry name).
- Bare variables (`intensity`, `a_*`) go into `envVariables[]`.
- Multi-mode devices are first collected into temporary `__mode__*` variables, then the
  final `state`/`mode` is back-filled during the `finalizeModeStates()` phase.
- Incremental parsing: only changed variables are emitted (NuSMV prints only the changes).

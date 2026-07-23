# Acceptance Demo: Night-Watch Repair Loop

This runbook exercises the main IoT-Verify product loop with one deliberately unsafe,
repairable smart-home scene. It is designed for an acceptance demonstration, not as a
claim that one scenario covers every possible template or formal property.

The canonical scene file is
[`../examples/acceptance-demo-scene.json`](../examples/acceptance-demo-scene.json).
It contains four device instances, two shared environment values, three automation
rules, and five formal specifications.

For a deterministic multi-violation repair demonstration, use
[`../examples/multi-violation-repair-scene.json`](../examples/multi-violation-repair-scene.json).
It keeps the same four default-template devices and rule chain but marks the shared motion
source as `untrusted`. Its baseline emits five specifications, with two violations: the
camera `Never` property and the untrusted-labelled event safety property. The first rule is
the shared root cause; removing it is forward-verified against all five specifications and
leaves the remaining two response rules intact.

For additional default-template examples covering fire evacuation, first-match rule
priority, and RFID trust/privacy attack propagation, see
[Additional Default-Template Scenarios](default-template-scenarios.md).

All four device types (`Motion Detector`, `Camera`, `Alarm`, and `Light`) are built-in
default templates. The demo does not require creating or editing a custom template.
The standard scene file still embeds exact template snapshots because version 4 scene
JSON is self-contained and must support lossless export/import; import matches those
snapshots to the existing defaults instead of creating duplicate device types. If a
default template was edited before the demo, reset it to the project default first so
the import preview can truthfully confirm semantic equality.

## What the demo proves

- Manual authoring, AI-assisted authoring, and standard scene JSON can describe the
  same user-level devices, environment, automations, and specifications.
- Standard JSON import is a full-scene replacement with an explicit impact preview.
- Simulation produces an animatable model trajectory. It is not a prediction of the
  physical home.
- Baseline verification checks all five submitted specifications on a complete model:
  four are satisfied and one is violated.
- The counterexample identifies the camera-photo automation and can be replayed on the
  Board timeline.
- Attack modeling with budget `1` exposes additional untrusted-source and compromised-
  automation-link failures while the camera-sensitivity property remains satisfied.
- Automatic fix can forward-verify permanent removal of the camera-photo rule. Applying
  that suggestion is a destructive Board mutation and requires confirmation; the next
  baseline verification satisfies all five emitted properties.

## Scene semantics

### Device instances

| Device type | Instance label | Initial runtime |
| --- | --- | --- |
| Motion Detector | Hall Motion Sensor | Stateless; shared `motion` reading |
| Camera | Hall Camera | `on`, trusted control source, private sensitivity |
| Alarm | Hall Alarm | `off`, trusted control source, public sensitivity |
| Light | Hall Light | `off`, trusted control source, public sensitivity |

The default node dimensions are `176 x 128`.

### Environment Pool

| Name | Value | Source label | Sensitivity label |
| --- | --- | --- | --- |
| `motion` | `active` | `trusted` | `private` |
| `illuminance` | `20` | `untrusted` | `public` |

### Automation chain

1. When `Hall Motion Sensor.motion = active`, command `Hall Camera.take photo`.
2. When the observable `Hall Camera.take photo` event occurs, command
   `Hall Alarm.siren`.
3. When the observable `Hall Alarm.siren` event occurs, command `Hall Light.on`.

The execution order is significant and is preserved by scene import/export.

### Formal specifications

| Template | User-level property | Baseline result before repair |
| --- | --- | --- |
| Never (`3`) | Hall Camera must never be in `taking photo` | Violated |
| Immediate (`4`) | A camera-photo event must make Hall Alarm `siren` next | Satisfied |
| Immediate (`4`) | An alarm-siren event must make Hall Light `on` next | Satisfied |
| Always (`1`) | Hall Camera state sensitivity remains `private` | Satisfied |
| Untrusted-labelled event safety (`7`) | A camera photo must not be controlled by an untrusted source | Satisfied without attack; violated on an admissible budget-one attack branch |

## Build route 1: standard scene JSON

1. Open the Board and choose **Import Scene**.
2. Select `docs/examples/acceptance-demo-scene.json`.
3. Review the full-replacement impact. The incoming scene must show `4` devices, `2`
   environment values, `3` rules, and `5` specifications.
4. Confirm **Import and replace**.
5. Check that the Board shows four instances and three rule-derived links.

Export the Board immediately after import. Re-importing that export should preserve the
same semantic scene and rule/specification order without carrying persistence ids.

## Build route 2: manual authoring

Start from an empty Board and reproduce the tables above in this order:

1. Add the four device instances with the listed labels and runtime values.
2. In the Environment Pool, set `motion` and `illuminance` to the exact values and
   labels above.
3. Add the three rules in the listed execution order. API-event sources have no
   relation or value; `motion` is a value condition using `=` and `active`.
4. Add the five specifications with structured conditions. Do not enter a raw NuSMV
   formula; the visible formula is a preview derived from the template and conditions.
5. Export the result and compare the user-level semantics with the canonical file.
   System-assigned device/specification ids may differ and are not user semantics.

Use the duplicate check while creating a second copy of the first rule, then cancel the
save. Optionally run the explicit AI similarity check to demonstrate that its answer is
advisory rather than proof of conflict freedom.

## Build route 3: AI

### AI Scene panel

Set the limits to `4` devices, `3` rules, and `5` specifications, then use this request:

```text
Use defaults: Motion Detector/Hall Motion Sensor, Camera/Hall Camera, Alarm/Hall Alarm,
Light/Hall Light. Env motion=active trusted/private; illuminance=20 untrusted/public.
Rules: motion active -> camera take photo; camera take-photo API -> alarm siren;
alarm-siren API -> light on. Specs: T3 never camera taking photo; T4 camera API -> alarm
siren; T4 alarm API -> light on; T1 camera state privacy private; T7 camera taking photo
not untrusted-controlled. Full-replacement, unverified draft only.
```

This compact prompt is 499 ASCII characters. The recommendation contract now permits up
to 2,000 characters, so an acceptance operator may use a more natural expanded request;
the compact form remains useful for repeatable demonstrations.

Do not use the `4 / 2 / 3 / 5` counts alone as evidence that the draft is equivalent to
the canonical scene. Accept the draft only if the preview also shows all four exact
device type/instance pairs, both Environment Pool values with their source and
sensitivity labels, the three rule source types and execution order, and the five
template/condition combinations listed above. No filtered or adjusted item may remove
or change a required semantic element. AI output is nondeterministic: backend validation
makes a kept draft structurally importable, but it does not prove that every provider
response is semantically identical to this fixture. Regenerate a mismatching draft or
use the canonical JSON route for deterministic acceptance results.

### AI assistant demonstration

A single assistant message may request the complete scene. The backend continues tool
planning while calls or results are changing, and the frontend shows the accumulating
execution trace throughout the request. A fixed five-round product limit is not part of
the flow.

For a more deterministic checkpointed demonstration, optionally issue separate messages to:

1. create the four exact device instances;
2. set the two Environment Pool values and create the three exact rules using the device
   references returned by `board_overview`;
3. create the five structured specifications; and
4. call `board_overview` and summarize what was actually persisted.

Splitting the request is useful only when the demonstrator wants to inspect persisted
state between stages. It is not required to bypass an assistant planning limit, and each
tool mutation remains independently committed rather than forming one atomic transaction.

## Execute the acceptance flow

The exact result counts below apply to the canonical scene and to a manual or AI-built
scene only after the semantic review above confirms equivalence. A structurally valid AI
draft can produce different verification counts when it chooses different conditions,
scopes, or initial runtime values; that is a different model, not a checker failure.

### 1. Baseline simulation and animation

Run synchronous simulation with:

- steps: `6`
- attack modeling: off (`attackScenario.mode = NONE`)
- privacy propagation: on

Expected: a saved, animatable trajectory containing the stages `Hall Camera = taking
photo`, `Hall Alarm = siren`, and `Hall Light = on`. Use play/pause, state buttons, the
range control, and Run History to replay it. Describe it as one model trajectory, not a
real-world forecast.

### 2. Baseline verification and counterexample animation

Run synchronous verification with attack off, budget `0`, and privacy on.

For the canonical scene, the expected complete result is:

- requested/emitted specifications: `5 / 5`
- disabled rules: `0`
- skipped specifications: `0`
- satisfied: `4`
- violated: `1`

For the multi-violation JSON variant, the same completeness checks apply, but the result is
`3` satisfied and `2` violated. Select the **Never camera taking photo** trace for automatic
repair. Do not apply the second old trace after the first repair: applying the root-rule
removal changes the board and makes the earlier trace stale; re-run verification to obtain
fresh traces.

Open the **Never camera taking photo** violation. Its counterexample reaches Hall Camera
`taking photo`, and the transition identifies the first camera-photo automation as the
localized rule. Its canonical name is **When hall motion is active, take a camera photo**;
the multi-violation variant prefixes it with **When an untrusted hall motion signal is
active**. Replay the counterexample animation and inspect the user-facing rule/device labels;
the actual checked expression belongs under technical details.

### 3. Attack/privacy contrast

Before applying a repair, run verification again with attack modeling on, budget `1`,
and privacy on.

The exact attack counts in this section belong to the canonical scene. For the
multi-violation variant, attack mode is an optional additional experiment; use the
baseline traces for repair and do not infer a fixed attack violation count from the
canonical example.

Expected: all five properties are emitted; four have counterexamples. In addition to the
original camera-photo violation, an admissible compromised sensor branch violates the
untrusted-source safety property, and compromised automation-link branches violate the
two immediate-response properties. The camera sensitivity property remains satisfied.
This is verification over modeled budget-one attack choices, not a claim that an attack
will occur.

### 4. Automatic fix and apply

Return to the baseline violation trace and request automatic fix. Select the verified
`remove` suggestion for the first camera-photo automation. In the canonical scene it is
**When hall motion is active, take a camera photo**; in the multi-violation variant it is
**When an untrusted hall motion signal is active, take a camera photo**.

The **condition adjustment** strategy may correctly finish without a suggestion for this
violation. The property forbids the camera's resulting `taking photo` state, while condition
adjustment can only change when the existing automation triggers; it cannot change that
command result. The UI therefore reports "no condition adjustment passed full-model
rechecking" rather than treating the strategy as not run. This is not a verification or
transport failure, and it does not imply that the other strategies have no proposal.

The suggestion means permanent rule removal, not temporary disablement. Confirm
**Remove Rules and Apply** only after reviewing the exact rule. The server recomputes the
candidate, verifies every submitted specification on the current complete model, checks
for Board drift, and writes only if that result still matches.

Expected after apply:

- rules: `2`
- the camera-photo rule is absent;
- the camera/alarm/light devices and all five specifications remain;
- a new baseline verification emits `5` properties and reports `5` satisfied, `0`
  violated, `0` skipped, and `0` disabled rules.

Passing means the five emitted model properties hold after this explicit removal. It is
not a guarantee about unmodeled physical behavior.

## Extended UI coverage

Use the same Board to demonstrate these secondary features without changing the core
expected verification counts until the repair step:

- move and resize a device, zoom/pan the canvas, and reload to show layout persistence;
- inspect device type versus device instance labels and runtime trust/privacy fields;
- inspect the Environment Pool and reset one value only after showing the consequences;
- open rule/specification recommendation panels and show kept/filtered/truncated details;
- submit async simulation/verification, inspect task progress, and replay saved history;
- export the scene before repair and after repair to show the exact rule difference;
- use AI assistant list/overview tools, while keeping raw NuSMV output and persistence ids
  in technical/debug surfaces only.

## Automated evidence

The real-NuSMV regression includes a strategy-specific repair matrix. Every row starts from a
complete model with exactly one counterexample, parses an animatable trace, localizes a rule,
requires the requested strategy attempt to report `VERIFIED`, applies the concrete suggestion,
and verifies the complete repaired model again:

| Strategy | Deliberately unsafe scene | Required concrete edit | Repaired result |
| --- | --- | --- | --- |
| `parameter` | Temperature `>= 28` heats the room while the policy requires `off` below `35` and `heat` from `35` | Move that threshold from `28` to `35` | `2 / 2` specifications satisfied; `0` disabled rules; `0` skipped specifications |
| `condition` | A cold-room rule heats while a separate occupancy sensor reports `absent` | Add `occupied = present` to the heating rule | `1 / 1` specification satisfied; `0` disabled rules; `0` skipped specifications |
| `remove` | Hall motion commands a privacy-forbidden camera photo | Permanently remove the camera-photo automation | `5 / 5` specifications satisfied; `0` disabled rules; `0` skipped specifications |

An additional interaction regression combines all three strategies on one trace. An early
`temperature >= 28 -> heat` rule conflicts with an occupancy-aware low-temperature policy,
while `temperature <= 35 -> off` and `temperature >= 36 -> heat` retain the intended hysteresis.
The default request returns independently verified parameter, condition, and removal suggestions.
The parameter search must reject `28 -> 36` because it would duplicate the existing high-temperature
rule, continue to the persistable `28 -> 37` edit, and apply that signed suggestion successfully.
With an unresolved `UNKNOWN_SPEC`, the same regression requires parameter and condition to report
`SKIPPED_NO_SPEC` while removal remains `VERIFIED`.

Four additional real-NuSMV edge cases exercise interactions that isolated strategy fixtures miss:

- an inverse `<=` cooling boundary rejects the duplicate `<= 14` edit, continues to `<= 13`,
  and verifies parameter, occupancy-guard, and removal repairs against a `>= 15 -> off`
  hysteresis rule;
- two same-command heating rules demonstrate command priority: only the executed rule is
  localized, but coordinated parameter and condition edits cover the dormant backup rule,
  while destructive repair proves that neither single removal works and returns `[0, 1]`;
- a natural environment-only temperature violation localizes no automation and requires all
  strategies to report `SKIPPED_NO_FAULT_RULES` instead of fabricating a repair;
- a `temperature >= 100` trigger at the manifest upper bound has no legal parameter repair,
  yet the default request still completes condition and removal strategies and verifies both.

These scenarios deliberately include closing hysteresis rules. A threshold that safely starts
heating or cooling is not sufficient by itself: device modes persist, so the environment can
later re-enter the forbidden region unless another rule exits that mode. Every expected repair
is therefore applied to the original rules and checked again against the complete model.

The same test class also runs random simulation, budget-one attack verification, and the
additional default-template scenario matrix:

```bash
cd backend
mvn -Dtest=AcceptanceDemoScenarioNusmvTest test
```

The test is skipped only when the NuSMV executable is unavailable.

The browser acceptance regression exercises all three rows and the combined-response case through scene import, the live REST
API, the Board verification UI, repair application, persistence reload, and a new verification.
It also repeats the redundant same-command scenario independently for parameter, condition,
and removal, requiring all two-item signed operations to survive apply and database reload
before the complete model is verified again.
The parameter and condition fixtures are generated in memory from the exact bundled template
snapshots so the browser path tests the real import contract without adding test-only device
capabilities:

```bash
cd frontend
npx playwright test e2e/board-full-flow.spec.ts --grep "finds and applies|persists every item in a coordinated|imports the acceptance scene"
```

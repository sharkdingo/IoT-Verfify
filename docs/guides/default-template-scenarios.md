# Additional Default-Template Scenarios

These scenes exercise default templates beyond the night-watch acceptance demo. Each
file is a standard version 4 `iot-verify.board-scene` document that can be imported from
the Board without creating or editing a custom template.

Verified against code and real NuSMV on 2026-07-13. Sources:
`scripts/generate-default-template-scenes.mjs`, the bundled manifests under
`backend/src/main/resources/deviceTemplate/`, and
`AcceptanceDemoScenarioNusmvTest`.

The files are generated from the current bundled template manifests by
`scripts/generate-default-template-scenes.mjs`. Do not hand-edit copied manifests inside
the JSON files. Change the user-level scene definition in the generator and rerun it so
the embedded snapshots remain exact, self-contained import dependencies.

## Expected checks

The counts below are deterministic for the generated files and were verified with real
NuSMV. `Baseline` and `attack` show satisfied/violated specification counts.

| Scene | Devices / environment / rules / specs | Baseline | Attack budget 1 | Verified repair |
| :--- | :--- | :--- | :--- | :--- |
| [Fire evacuation](../examples/default-fire-evacuation-scene.json) | `4 / 2 / 3 / 5` | `4 / 1` | `1 / 4` | Remove the alarm-to-door unlock rule; then `5 / 0` |
| [Climate conflict](../examples/default-climate-conflict-scene.json) | `2 / 2 / 2 / 4` | `2 / 2` | `1 / 3` | Remove the first hot-room heating rule; then `4 / 0` |
| [RFID access](../examples/default-rfid-access-scene.json) | `3 / 0 / 2 / 5` | `5 / 0` | `2 / 3` | No baseline violation to repair |

Every baseline and attack run emits all requested properties with zero disabled rules
and zero skipped specifications. Simulation produces an animatable trajectory for each
scene. These results describe the formal model, not guaranteed physical-home behavior.

## Fire evacuation

Default templates: `Smoke Sensor`, `Alarm`, `Door`, and `Light`.

The trusted `smoke = detected` reading sounds the alarm. The observable alarm event then
unlocks the front door and turns on the exit light. The intentionally violated property
says the front door must never become unlocked; the two response properties, the alarm
trust property, and its public-sensitivity property hold in the baseline model.

The counterexample reaches `Front Door = unlocked`. Automatic repair considers the full
rule chain but forward verification accepts only removal of **When the alarm sounds,
unlock the front door for evacuation**. The alarm and exit-light behavior remain, and
all five properties pass after applying that removal.

## Climate conflict

Default templates: `Temperature Sensor` and `Air Conditioner`.

Both rules use `temperature >= 28` and target the same air-conditioner mode. The unsafe
heating rule is deliberately first, followed by the cooling rule. Board rule order is
execution priority: for one target setting, the first matching command wins. Therefore
the baseline reaches `HvacMode = heat`; both the immediate-cooling property and the
never-heat-while-hot property fail.

This scene makes order visible instead of describing the two rules as an unspecified
conflict. Removing the first heating rule leaves the cooling rule authoritative, and all
four properties pass. The temperature is labelled private household telemetry so this
scene tests rule priority independently from an unrelated sensitivity-label violation.

## RFID access

Default templates: `Door RFID`, `Door`, and `Alarm`.

The badge reader uses a device-local `RFID` value, not an Environment Pool value. Its
initial value is `authorized`, trusted, and private. An authorized reading unlocks the
door; a `not authorized` reading sounds the alarm. All five baseline properties pass.

With attack budget `1`, admissible compromised-reader or automation-link branches expose
three counterexamples: the authorized response can be disrupted, an unauthorized state
can coexist with an already unlocked door, and an unlock can carry an untrusted control
label. The privacy property and unauthorized-alarm response remain satisfied. This is a
modeled attack-space result, not a statement that a physical badge will be compromised.

## Reproduce

Regenerate the scene JSON after a bundled template changes:

```bash
node scripts/generate-default-template-scenes.mjs
```

Run the real-NuSMV regression for the original acceptance scene and all three additional
scenes:

```bash
cd backend
mvn -Dtest=AcceptanceDemoScenarioNusmvTest test
```

On Windows, if Maven and the temporary directory are on different drives and Surefire
rejects its manifest classpath before running any test, use the equivalent non-forked
command:

```bash
mvn -DforkCount=0 -Dtest=AcceptanceDemoScenarioNusmvTest test
```

For a UI check, import a file, review the explicit full-replacement preview, run
synchronous simulation and play the timeline, then run baseline and budget-one attack
verification. Apply only the two removals named above; do not treat attack findings as
ordinary baseline repair requests.

import fs from 'node:fs'
import path from 'node:path'
import { fileURLToPath } from 'node:url'

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..')
const templateDir = path.join(repoRoot, 'backend', 'src', 'main', 'resources', 'deviceTemplate')
// Defaults to the shipped fixtures; an explicit argument lets a check regenerate into a temp
// directory and diff, without a failed run leaving the committed scenes half-rewritten.
const outputDir = process.argv[2]
  ? path.resolve(process.argv[2])
  : path.join(repoRoot, 'docs', 'examples')

const loadTemplate = (name) => {
  const manifest = JSON.parse(fs.readFileSync(path.join(templateDir, `${name}.json`), 'utf8'))
  if (manifest.Name !== name) {
    throw new Error(`Template file ${name}.json declares Name=${manifest.Name}`)
  }
  return { name, manifest }
}

const device = (id, templateName, label, x, y, runtime = {}) => ({
  id,
  templateName,
  label,
  position: { x, y },
  ...runtime,
  width: 176,
  height: 128
})

const valueSource = (fromId, fromApi, relation, value) => ({
  fromId,
  fromApi,
  itemType: 'variable',
  relation,
  value
})

const apiSource = (fromId, fromApi) => ({ fromId, fromApi, itemType: 'api' })

/**
 * A `variable` condition must say which of two questions it asks, so `variableSource` is a required
 * positional argument rather than an option: `environment` reads the shared pool value ("did this
 * actually happen in the home"), `reported` reads what this device said. They diverge once the device
 * is compromised, so there is no safe default and every writer rejects a missing value. Passing it for
 * a non-variable target, or omitting it for a variable one, throws here rather than emitting a scene
 * the importer will refuse.
 */
const condition = (deviceId, targetType, key, relation, value, propertyScope, variableSource) => {
  if (targetType === 'variable' && !variableSource) {
    throw new Error(`condition(${deviceId}, ${key}): a variable condition requires variableSource `
      + `('environment' for the value in the home, 'reported' for what this device said)`)
  }
  if (targetType !== 'variable' && variableSource) {
    throw new Error(`condition(${deviceId}, ${key}): variableSource is only valid for variable conditions`)
  }
  return {
    deviceId,
    targetType,
    key,
    ...(propertyScope ? { propertyScope } : {}),
    ...(variableSource ? { variableSource } : {}),
    relation,
    value
  }
}

const aSpec = (templateId, aConditions) => ({
  templateId,
  aConditions,
  ifConditions: [],
  thenConditions: []
})

const implicationSpec = (templateId, ifConditions, thenConditions) => ({
  templateId,
  aConditions: [],
  ifConditions,
  thenConditions
})

/**
 * A scene may define its own device type instead of reusing a bundled manifest. The
 * away-mode presentation scene needs an occupancy signal that actually evolves, so it
 * declares `occupancy` as a shared environment variable (`IsInside: false`, `Reads: true`).
 * A device-local variable would be frozen at its initial value for the whole run, which
 * would make any repair conditioned on it unreachable — a repair that silently disables
 * the rule it claims to keep.
 */
const occupancySensorTemplate = {
  name: 'Occupancy Sensor',
  manifest: {
    Name: 'Occupancy Sensor',
    Description: 'Reports whether a resident is present, as a shared environment reading',
    InternalVariables: [
      {
        Name: 'occupancy',
        Description: 'Whether a resident is currently present',
        IsInside: false,
        Reads: true,
        FalsifiableWhenCompromised: true,
        Trust: 'trusted',
        Privacy: 'private',
        Values: ['present', 'absent']
      }
    ],
    ImpactedVariables: [],
    Modes: [],
    InitState: '',
    WorkingStates: [],
    Transitions: [],
    APIs: []
  }
}

const scenes = [
  {
    file: 'default-fire-evacuation-scene.json',
    templateNames: ['Alarm', 'Door', 'Light', 'Smoke Sensor'],
    devices: [
      device('smoke_1', 'Smoke Sensor', 'Kitchen Smoke Sensor', 70, 120),
      device('alarm_1', 'Alarm', 'Whole-home Alarm', 330, 40, {
        state: 'off', currentStateTrust: 'trusted', currentStatePrivacy: 'public'
      }),
      device('door_1', 'Door', 'Front Door', 590, 40, {
        state: 'locked', currentStateTrust: 'trusted', currentStatePrivacy: 'private'
      }),
      device('light_1', 'Light', 'Exit Light', 590, 220, {
        state: 'off', currentStateTrust: 'trusted', currentStatePrivacy: 'public'
      })
    ],
    environmentVariables: [
      { name: 'illuminance', value: '20', trust: 'untrusted', privacy: 'public' },
      { name: 'smoke', value: 'detected', trust: 'trusted', privacy: 'public' }
    ],
    rules: [
      {
        name: 'When kitchen smoke is detected, sound the whole-home alarm',
        sources: [valueSource('smoke_1', 'smoke', '=', 'detected')],
        toId: 'alarm_1',
        toApi: 'siren'
      },
      {
        name: 'When the alarm sounds, unlock the front door for evacuation',
        sources: [apiSource('alarm_1', 'siren')],
        toId: 'door_1',
        toApi: 'unlock'
      },
      {
        name: 'When the alarm sounds, turn on the exit light',
        sources: [apiSource('alarm_1', 'siren')],
        toId: 'light_1',
        toApi: 'on'
      }
    ],
    specs: [
      implicationSpec('4',
        [condition('smoke_1', 'variable', 'smoke', '=', 'detected', null, 'environment')],
        [condition('alarm_1', 'mode', 'AlertState', '=', 'siren')]),
      implicationSpec('4',
        [condition('alarm_1', 'api', 'siren', '=', 'TRUE')],
        [condition('light_1', 'mode', 'SwitchState', '=', 'on')]),
      aSpec('3', [condition('door_1', 'state', 'state', '=', 'unlocked')]),
      aSpec('7', [condition('alarm_1', 'mode', 'AlertState', '=', 'siren')]),
      aSpec('1', [condition('alarm_1', 'privacy', 'AlertState', '=', 'public', 'state')])
    ]
  },
  {
    file: 'default-climate-conflict-scene.json',
    templateNames: ['Air Conditioner', 'Temperature Sensor'],
    devices: [
      device('temperature_1', 'Temperature Sensor', 'Living-room Temperature Sensor', 90, 120),
      device('ac_1', 'Air Conditioner', 'Living-room Air Conditioner', 430, 120, {
        state: 'auto', currentStateTrust: 'trusted', currentStatePrivacy: 'private'
      })
    ],
    environmentVariables: [
      { name: 'humidity', value: '50', trust: 'untrusted', privacy: 'public' },
      { name: 'temperature', value: '30', trust: 'trusted', privacy: 'private' }
    ],
    rules: [
      {
        name: 'Unsafe conflicting rule: when the room is hot, heat the living room',
        sources: [valueSource('temperature_1', 'temperature', '>=', '28')],
        toId: 'ac_1',
        toApi: 'heat'
      },
      {
        name: 'When the room is hot, cool the living room',
        sources: [valueSource('temperature_1', 'temperature', '>=', '28')],
        toId: 'ac_1',
        toApi: 'cool'
      }
    ],
    specs: [
      implicationSpec('4',
        [condition('temperature_1', 'variable', 'temperature', '>=', '28', null, 'environment')],
        [condition('ac_1', 'mode', 'HvacMode', '=', 'cool')]),
      aSpec('3', [
        condition('temperature_1', 'variable', 'temperature', '>=', '28', null, 'environment'),
        condition('ac_1', 'mode', 'HvacMode', '=', 'heat')
      ]),
      aSpec('1', [condition('ac_1', 'privacy', 'HvacMode', '=', 'private', 'state')]),
      aSpec('7', [condition('ac_1', 'mode', 'HvacMode', '=', 'heat')])
    ]
  },
  {
    file: 'default-away-mode-unlock-scene.json',
    templateNames: ['Alarm', 'Door', 'Light', 'Motion Detector'],
    extraTemplates: [occupancySensorTemplate],
    devices: [
      device('occupancy_1', 'Occupancy Sensor', 'Resident Presence Sensor', 70, 60),
      device('motion_1', 'Motion Detector', 'Porch Motion Detector', 70, 280),
      device('alarm_1', 'Alarm', 'Entry Alarm', 360, 40, {
        state: 'off', currentStateTrust: 'trusted', currentStatePrivacy: 'public'
      }),
      device('door_1', 'Door', 'Front Door', 360, 240, {
        state: 'locked', currentStateTrust: 'trusted', currentStatePrivacy: 'private'
      }),
      device('light_1', 'Light', 'Porch Light', 360, 430, {
        state: 'off', currentStateTrust: 'trusted', currentStatePrivacy: 'public'
      })
    ],
    environmentVariables: [
      { name: 'occupancy', value: 'absent', trust: 'trusted', privacy: 'private' },
      { name: 'motion', value: 'inactive', trust: 'trusted', privacy: 'private' },
      // `illuminance` is required because the Light template impacts it, but the template declares
      // it `Reads: false`, so no rule or specification in this scene can observe it. It is here to
      // satisfy environment coverage, not because the demo reasons about light levels.
      { name: 'illuminance', value: '20', trust: 'untrusted', privacy: 'public' }
    ],
    rules: [
      {
        name: 'When nobody is home, arm the entry alarm',
        sources: [valueSource('occupancy_1', 'occupancy', '=', 'absent')],
        toId: 'alarm_1',
        toApi: 'strobe'
      },
      {
        name: 'When porch motion is detected, unlock the front door for convenience',
        sources: [valueSource('motion_1', 'motion', '=', 'active')],
        toId: 'door_1',
        toApi: 'unlock'
      },
      {
        name: 'When porch motion is detected, turn on the porch light',
        sources: [valueSource('motion_1', 'motion', '=', 'active')],
        toId: 'light_1',
        toApi: 'on'
      }
    ],
    specs: [
      implicationSpec('4',
        [condition('occupancy_1', 'variable', 'occupancy', '=', 'absent', null, 'environment')],
        [condition('alarm_1', 'mode', 'AlertState', '=', 'strobe')]),
      implicationSpec('4',
        [condition('motion_1', 'variable', 'motion', '=', 'active', null, 'environment')],
        [condition('light_1', 'mode', 'SwitchState', '=', 'on')]),
      aSpec('3', [
        condition('occupancy_1', 'variable', 'occupancy', '=', 'absent', null, 'environment'),
        condition('door_1', 'mode', 'LockState', '=', 'unlocked')
      ]),
      implicationSpec('5',
        [
          condition('occupancy_1', 'variable', 'occupancy', '=', 'absent', null, 'environment'),
          condition('door_1', 'mode', 'LockState', '=', 'unlocked')
        ],
        [condition('door_1', 'mode', 'LockState', '=', 'locked')]),
      aSpec('7', [condition('door_1', 'mode', 'LockState', '=', 'unlocked')]),
      aSpec('1', [condition('door_1', 'privacy', 'LockState', '=', 'private', 'state')])
    ]
  },
  {
    file: 'default-rfid-access-scene.json',
    templateNames: ['Alarm', 'Door', 'Door RFID'],
    devices: [
      // `Door RFID` declares Modes, so the codec requires an explicit state
      // (`assertSceneDeviceRuntimeShape`) — omitting it regenerated an unimportable scene. The state
      // must also be `authorized`: the scene's whole point is that a badge already scanned, and
      // `ScanState`'s first working state is not that. This was fixed in the fixture by hand once
      // (3712d73) and the generator kept overwriting it.
      //
      // The `RFID` entry stays, even though the state declares a `Dynamics` value for it, because an
      // instance entry is the ONLY channel for a variable's trust label: `Dynamic` carries no trust,
      // and a state's `Trust` never reaches a state-determined variable. Dropping it as "redundant"
      // left `init(trust_RFID) := untrusted` (the template default) as the model's single difference,
      // which refutes this scene's trust specification at baseline — the very property it exists to
      // demonstrate. Its `value` is not a second source of truth: `canonicalizeVariables` overwrites
      // it with the state-declared value, which is what it already holds.
      device('rfid_1', 'Door RFID', 'Front-door Badge Reader', 80, 120, {
        state: 'authorized', currentStateTrust: 'trusted', currentStatePrivacy: 'private',
        variables: [{ name: 'RFID', value: 'authorized', trust: 'trusted' }],
        privacies: [{ name: 'RFID', privacy: 'private' }]
      }),
      device('door_1', 'Door', 'Front Door', 370, 70, {
        state: 'locked', currentStateTrust: 'trusted', currentStatePrivacy: 'private'
      }),
      device('alarm_1', 'Alarm', 'Entry Alarm', 370, 250, {
        state: 'off', currentStateTrust: 'trusted', currentStatePrivacy: 'public'
      })
    ],
    environmentVariables: [],
    rules: [
      {
        name: 'When the badge is authorized, unlock the front door',
        sources: [valueSource('rfid_1', 'RFID', '=', 'authorized')],
        toId: 'door_1',
        toApi: 'unlock'
      },
      {
        name: 'When the badge is not authorized, sound the entry alarm',
        sources: [valueSource('rfid_1', 'RFID', '=', 'not authorized')],
        toId: 'alarm_1',
        toApi: 'siren'
      }
    ],
    specs: [
      implicationSpec('4',
        [condition('rfid_1', 'variable', 'RFID', '=', 'authorized', null, 'reported')],
        [condition('door_1', 'mode', 'LockState', '=', 'unlocked')]),
      implicationSpec('4',
        [condition('rfid_1', 'variable', 'RFID', '=', 'not authorized', null, 'reported')],
        [condition('alarm_1', 'mode', 'AlertState', '=', 'siren')]),
      aSpec('3', [
        condition('rfid_1', 'variable', 'RFID', '=', 'not authorized', null, 'reported'),
        condition('door_1', 'mode', 'LockState', '=', 'unlocked')
      ]),
      aSpec('7', [condition('door_1', 'mode', 'LockState', '=', 'unlocked')]),
      aSpec('1', [condition('rfid_1', 'privacy', 'RFID', '=', 'private', 'variable')])
    ]
  },

  // Comprehensive elderly care apartment scenario - multi-dimensional blind spot probe
  // Targets: Template 6 (LTL), environment vs reported divergence, pure environment specs,
  // custom template validation, multi-parameter joint solving, IN/NOT_IN relations
  {
    file: 'elderly-care-comprehensive-scene.json',
    // Device selection is cost-driven. A device contributes roughly
    // `modes + signalAPIs + 2 * workingStates` state variables (a `trust_` and a `privacy_` per
    // working state), so actuators are expensive and stateless sensors are free. `Home Mode` is
    // the one costly device kept on purpose: it is the only bundled template that is multi-mode,
    // content-capable, and auto-returns to idle, which is what lets it be a repeatable chain hub.
    // Air Conditioner (28) and Thermostat (40) are deliberately absent — see the guide.
    templateNames: ['Illuminance Sensor', 'Light', 'Motion Detector', 'Door', 'Window',
      'Alarm', 'Camera', 'Air Quality Monitor', 'Air Purifier', 'Home Mode', 'Mobile Phone',
      'Clock'],
    extraTemplates: [
      // A custom name, not `HeartRateMonitor`: the domain and rate below disagree with that
      // template, and P5 rejects two declarers of one shared name whose range or
      // `NaturalChangeRate` differ. `[-1, 1]` is MEDIC's integer baseline and halves this
      // variable's branching factor against the old `[-2, 2]`.
      {
        name: 'Vital Signs Monitor',
        manifest: {
          Name: 'Vital Signs Monitor',
          Description: 'Wearable vital-signs monitor with graded alert states',
          InternalVariables: [
            {
              Name: 'heartRate',
              IsInside: false,
              Reads: true,
              LowerBound: 50,
              UpperBound: 150,
              NaturalChangeRate: '[-1, 1]',
              FalsifiableWhenCompromised: true,
              Trust: 'trusted',
              Privacy: 'private'
            }
          ],
          Modes: ['MonitorMode'],
          InitState: 'normal',
          WorkingStates: [
            {
              Name: 'normal',
              Dynamics: [],
              Description: 'Normal heart rate range (60-100 bpm)',
              Trust: 'trusted',
              Privacy: 'public'
            },
            {
              Name: 'alert',
              Dynamics: [],
              Description: 'Abnormal heart rate detected',
              Trust: 'trusted',
              Privacy: 'public'
            },
            {
              Name: 'emergency',
              Dynamics: [],
              Description: 'Critical heart rate',
              Trust: 'trusted',
              Privacy: 'public'
            }
          ],
          Transitions: [
            {
              Name: 'High heart rate alert',
              StartState: 'normal',
              EndState: 'alert',
              Trigger: { Attribute: 'heartRate', Relation: '>', Value: '100' }
            },
            {
              Name: 'Low heart rate alert',
              StartState: 'normal',
              EndState: 'alert',
              Trigger: { Attribute: 'heartRate', Relation: '<', Value: '60' }
            },
            {
              Name: 'Critical high heart rate',
              StartState: 'alert',
              EndState: 'emergency',
              Trigger: { Attribute: 'heartRate', Relation: '>', Value: '130' }
            },
            // Bounded at 130, not `>= 60`: an unbounded recovery guard also held at 131, so
            // `alert` could nondeterministically fall back to `normal` instead of escalating and
            // the emergency chain became unreliable rather than unreachable.
            {
              Name: 'Return to normal',
              StartState: 'alert',
              EndState: 'normal',
              Trigger: { Attribute: 'heartRate', Relation: '<=', Value: '100' }
            }
          ],
          APIs: [
            {
              Name: 'signal_anomaly',
              StartState: 'normal',
              EndState: 'emergency',
              Trigger: null,
              Signal: true,
              Description: 'Resident-pressed panic button, straight to emergency'
            }
          ]
        }
      },
      // `bedOccupancy`, not `occupancy`: the away-mode scene's `Occupancy Sensor` declares
      // `occupancy` as {present, absent}, and one board carrying both would be an enum conflict.
      // Stateless (no Modes, no WorkingStates), so it costs no state variables and carries no
      // instance `state` — the codec rejects one on a stateless device.
      {
        name: 'Bed Occupancy Sensor',
        manifest: {
          Name: 'Bed Occupancy Sensor',
          Description: 'Under-mattress presence sensor for night-time bed exit',
          InternalVariables: [
            {
              Name: 'bedOccupancy',
              Description: 'Whether the resident is currently in bed',
              IsInside: false,
              Reads: true,
              Values: ['occupied', 'empty'],
              FalsifiableWhenCompromised: true,
              Trust: 'trusted',
              Privacy: 'private'
            }
          ],
          Modes: [],
          WorkingStates: [],
          Transitions: [],
          APIs: []
        }
      }
    ],
    // Laid out in four columns left to right — sensing, hub, responders, outward — so each rule
    // chain reads as one horizontal path on the canvas instead of a sensor row fanning into an
    // actuator row. Edges are drawn per (rule, source) with no role filtering, so a path is
    // visible exactly when one device is both some rule's target and another rule's source.
    devices: [
      // Column 1 — sensing. All stateless, so none carries an instance `state` and none
      // contributes a state variable.
      device('bed_sensor', 'Bed Occupancy Sensor', 'Bed Occupancy Sensor', 40, 40),
      device('motion_det', 'Motion Detector', 'Hallway Motion Sensor', 40, 200),
      device('light_sensor', 'Illuminance Sensor', 'Illuminance Sensor', 40, 360),
      device('air_quality', 'Air Quality Monitor', 'Air Quality Monitor', 40, 520),
      device('clock', 'Clock', 'Wall Clock', 40, 680),
      // `vitals` is stateful: MonitorMode drives the escalation chain.
      device('vitals', 'Vital Signs Monitor', 'Wearable Vitals Monitor', 300, 40, {
        state: 'normal', currentStateTrust: 'trusted', currentStatePrivacy: 'private'
      }),
      // Column 2 — the hub. Complete tuple required: partial tuples and wildcards are rejected
      // for an instance `state`. `Home Mode` auto-returns to `;idle`, which is what makes its
      // `State` pulse repeatable and lets it sit in the middle of a chain.
      device('care_hub', 'Home Mode', 'Care Hub', 300, 300, {
        state: 'home;idle', currentStateTrust: 'trusted', currentStatePrivacy: 'private'
      }),
      // Column 3 — responders. Each instance state is pinned to a state its incoming command
      // moves it OUT of: an api signal is `next(mode)=End & mode!=End`, so a device already
      // resting in the command's EndState fires the rule and emits no pulse.
      device('alarm_system', 'Alarm', 'Emergency Alarm', 580, 40, {
        state: 'off', currentStateTrust: 'trusted', currentStatePrivacy: 'public'
      }),
      device('smart_lamp', 'Light', 'Bedside Lamp', 580, 200, {
        state: 'off', currentStateTrust: 'trusted', currentStatePrivacy: 'public'
      }),
      device('door_lock', 'Door', 'Front Door Lock', 580, 360, {
        state: 'locked', currentStateTrust: 'trusted', currentStatePrivacy: 'private'
      }),
      device('window_1', 'Window', 'Electric Window', 580, 520, {
        state: 'closed', currentStateTrust: 'trusted', currentStatePrivacy: 'public'
      }),
      // `off`, against the template's `InitState: 'on'`, so `→ air_purifier.on` actually pulses.
      device('air_purifier', 'Air Purifier', 'Air Purifier', 580, 680, {
        state: 'off', currentStateTrust: 'trusted', currentStatePrivacy: 'public'
      }),
      // `on`, because `take photo` is one of the few APIs carrying a real `StartState` guard
      // (`'on'`). The shipped scene pinned `off` instead, which made the photo rule dead and two
      // specifications about `taking photo` vacuous.
      device('camera_1', 'Camera', 'Hallway Camera', 860, 200, {
        state: 'on', currentStateTrust: 'trusted', currentStatePrivacy: 'private'
      }),
      // Column 4 — outward. The only content source in the scene: `Camera` declares no
      // `Contents`, so a content-carrying command must name this device.
      device('caregiver_phone', 'Mobile Phone', "Caregiver's Phone", 860, 40, {
        state: 'on', currentStateTrust: 'trusted', currentStatePrivacy: 'private'
      })
    ],
    // Exactly the required set: every non-local variable of every device's template, plus every
    // `ImpactedVariables` entry. The board layer would silently reconcile a wrong list, but
    // direct generation is strict — an extra entry is a hard error, and a missing one emits no
    // `init(a_X)` so NuSMV starts it anywhere in its domain. `location` is easy to miss: it comes
    // from `Mobile Phone`, which no rule reads.
    //
    // Values place the home at the moment of the incident, the way the fire-evacuation scene
    // ships `smoke = detected`. `heartRate` starts at 135 so `normal -> alert -> emergency` takes
    // two steps; from a resting 75 at `[-1, 1]` it would need sixty.
    environmentVariables: [
      // 125, not 135: the monitor ships in `normal` and needs one step to escalate, so a value
      // already past its own alert threshold made "reports normal while reading high" true in the
      // initial state and refuted s9 before any automation ran. At 125 the escalation still takes
      // two steps (alert above 100, emergency above 130) because the value may drift up.
      { name: 'heartRate', value: '125', trust: 'trusted', privacy: 'private' },
      { name: 'bedOccupancy', value: 'empty', trust: 'trusted', privacy: 'private' },
      { name: 'motion', value: 'active', trust: 'trusted', privacy: 'private' },
      { name: 'illuminance', value: '10', trust: 'trusted', privacy: 'public' },
      { name: 'time', value: '23', trust: 'trusted', privacy: 'public' },
      { name: 'airQuality', value: '20', trust: 'untrusted', privacy: 'public' },
      { name: 'carbonDioxide', value: '70', trust: 'trusted', privacy: 'public' },
      { name: 'location', value: 'away', trust: 'trusted', privacy: 'private' }
    ],
    rules: [
      // Array order IS execution priority, arbitrated per target mode: the first enabled command
      // branch for a mode wins and the loser cannot even update its trust/privacy labels. Every
      // group of rules sharing a target mode below is ordered deliberately, and the order is
      // called out where it decides an outcome.
      //
      // --- Chain A: vitals escalation. vitals -> alarm -> hub -> door, plus hub -> phone.
      // Four devices in a line on the canvas. Hop 1 uses `mode` (persistent while the monitor
      // stays in emergency); hop 2 uses `api` (the alarm sounding is an event, and the alarm has
      // no auto-return so it pulses exactly once); hop 3 uses `mode` on the hub's `State`, which
      // auto-returns to idle and is therefore repeatable.
      // Hop 0. Without it the monitor could still reach `emergency`, but only by drifting six
      // nondeterministic steps from its initial reading — verification would find the path while a
      // random simulation walk almost never shows it, leaving the flagship chain invisible in the
      // animation. `signal_anomaly` goes `normal -> emergency` in one step, and "out of bed at
      // night with an abnormal reading" is the judgement a real monitor makes.
      {
        name: 'Treat an abnormal reading during a night-time bed exit as an emergency',
        sources: [
          valueSource('vitals', 'heartRate', '>', '120'),
          valueSource('bed_sensor', 'bedOccupancy', '=', 'empty'),
          valueSource('clock', 'time', 'in', '22,23,0,1,2,3,4,5,6')
        ],
        toId: 'vitals',
        toApi: 'signal_anomaly'
      },
      {
        name: 'When vitals reach emergency, sound the alarm',
        sources: [{ fromId: 'vitals', fromApi: 'MonitorMode', itemType: 'mode', relation: '=', value: 'emergency' }],
        toId: 'alarm_system',
        toApi: 'siren'
      },
      {
        name: 'When the alarm sounds, have the care hub raise an alert',
        sources: [apiSource('alarm_system', 'siren')],
        toId: 'care_hub',
        toApi: 'send alert message'
      },
      {
        name: 'While the care hub is raising an alert, unlock the front door for responders',
        sources: [{ fromId: 'care_hub', fromApi: 'State', itemType: 'mode', relation: '=', value: 'sendingAlertMessage' }],
        toId: 'door_lock',
        toApi: 'unlock'
      },
      // The content pair is legal only because `upload to cloud` declares `AcceptsContent` and
      // the named content item exists on `contentDevice`'s own template. It is cross-device by
      // design: `Camera` declares no `Contents`, so the phone is the scene's only content source.
      // Content feeds the privacy dimension only — it contributes nothing to trust.
      {
        name: "While the care hub is raising an alert, upload the resident's photo to the caregiver",
        sources: [{ fromId: 'care_hub', fromApi: 'State', itemType: 'mode', relation: '=', value: 'sendingAlertMessage' }],
        toId: 'caregiver_phone',
        toApi: 'upload to cloud',
        contentDevice: 'caregiver_phone',
        content: 'photo'
      },
      // --- Chain B: night-time bed exit. bed/clock -> lamp -> camera -> hub.
      // `time` never wraps (rate `'1'` is `0..1` and the clamp saturates), and rule conditions are
      // AND-only, so a 22:00-06:00 window is one `in` condition rather than two comparisons.
      {
        name: 'When the resident leaves the bed at night, light the way',
        sources: [
          valueSource('bed_sensor', 'bedOccupancy', '=', 'empty'),
          valueSource('clock', 'time', 'in', '22,23,0,1,2,3,4,5,6')
        ],
        toId: 'smart_lamp',
        toApi: 'on'
      },
      {
        name: 'When the bedside lamp comes on, have the hallway camera take a photo',
        sources: [apiSource('smart_lamp', 'on')],
        toId: 'camera_1',
        toApi: 'take photo'
      },
      {
        name: 'When the camera takes a photo, have the care hub send it',
        sources: [apiSource('camera_1', 'take photo')],
        toId: 'care_hub',
        toApi: 'send photo',
        contentDevice: 'caregiver_phone',
        content: 'photo'
      },
      // --- Chain C: ventilation. air quality -> window -> purifier.
      // `open` precedes `close` below, and the two are made mutually exclusive by the extra
      // air-quality condition on the closing rule. Without that the earlier rule would win the
      // shared `WindowState` mode whenever both held, and venting would be unreachable at night —
      // exactly the silent shadowing this scene exists to make visible.
      {
        name: 'When the air is stale, open the window',
        sources: [valueSource('air_quality', 'carbonDioxide', '>', '60')],
        toId: 'window_1',
        toApi: 'open'
      },
      {
        name: 'When the window opens, run the air purifier',
        sources: [apiSource('window_1', 'open')],
        toId: 'air_purifier',
        toApi: 'on'
      },
      {
        name: 'Close the window at night once the air is fresh again',
        sources: [
          valueSource('clock', 'time', 'in', '22,23,0,1,2,3,4,5,6'),
          valueSource('air_quality', 'carbonDioxide', '<=', '60')
        ],
        toId: 'window_1',
        toApi: 'close'
      },
      // --- The intentional defect. Not labelled unsafe, because a household would install it:
      // "turn the lamp off when nobody is moving" is ordinary energy saving. It shares
      // `SwitchState` with chain B's lamp rule and sits AFTER it, so it loses the arbitration
      // while the night rule holds — and the moment motion stops during a night-time bed exit it
      // is the rule that wins, darkening the room the resident is walking through.
      {
        name: 'Turn the lamp off when there is no movement',
        sources: [valueSource('motion_det', 'motion', '=', 'inactive')],
        toId: 'smart_lamp',
        toApi: 'off'
      }
    ],
    // Each entry names the question it asks and whether it is expected to hold. A property that
    // cannot fail is not a passing check, so the ones that are unfalsifiable by construction are
    // labelled as such rather than counted as coverage. Exactly one privacy condition appears
    // here on purpose: a single one forces privacy modelling on for the whole run, which is the
    // largest single cost in the model after device count.
    specs: [
      // s1 | template 3 | EXPECTED TO FAIL. The lamp must never be off while the resident is
      // walking at night. The energy-saving rule shares `SwitchState` with the night rule and
      // sits after it, so it wins the moment motion stops — this is the counterexample the scene
      // exists to produce, and the trace shows which rule won the arbitration.
      aSpec('3', [
        condition('bed_sensor', 'variable', 'bedOccupancy', '=', 'empty', null, 'environment'),
        condition('clock', 'variable', 'time', 'in', '22,23,0,1,2,3,4,5,6', null, 'environment'),
        condition('smart_lamp', 'state', 'state', '=', 'off')
      ]),
      // s2 | template 5 | expected to hold. Emergency vitals must eventually sound the alarm.
      implicationSpec('5',
        [condition('vitals', 'mode', 'MonitorMode', '=', 'emergency')],
        [condition('alarm_system', 'mode', 'AlertState', '=', 'siren')]
      ),
      // s3 | template 5 | expected to hold, and it is the chain-depth property: the escalation
      // has to reach the door through the alarm and the hub, so it fails if any hop is inert.
      implicationSpec('5',
        [condition('vitals', 'mode', 'MonitorMode', '=', 'emergency')],
        [condition('door_lock', 'mode', 'LockState', '=', 'unlocked')]
      ),
      // s4 | template 4 | expected to hold. The hub raising an alert must unlock the door in the
      // very next state, which pins hop 3 as immediate rather than merely eventual.
      implicationSpec('4',
        [condition('care_hub', 'mode', 'State', '=', 'sendingAlertMessage')],
        [condition('door_lock', 'mode', 'LockState', '=', 'unlocked')]
      ),
      // s5 | template 7 | expected to hold at baseline, to FAIL under attack. `airQuality` ships
      // `untrusted`, so a compromised air monitor is what makes the window open on a lie. Without
      // an untrusted label anywhere in the scene this template can never fail and says nothing.
      aSpec('7', [condition('window_1', 'mode', 'WindowState', '=', 'open')]),
      // s6 | template 4 | expected to hold. Stale air must open the window in the next state.
      // Note the threshold matches the rule exactly: an earlier version of this scene asked about
      // `airQuality < 30` while nothing wrote `airQuality`, so it checked a command and never an
      // effect. `carbonDioxide` has a real writer — the purifier — so this one can be falsified.
      implicationSpec('4',
        [condition('air_quality', 'variable', 'carbonDioxide', '>', '60', null, 'environment')],
        [condition('window_1', 'mode', 'WindowState', '=', 'open')]
      ),
      // s7 | template 5 | expected to hold. The air must eventually become fresh again, which is
      // only true because the purifier drives `carbonDioxide` down. This pins chain C's last hop:
      // it fails if that hop is inert (the failure mode an `api` source hits when its target
      // already sits in the command's end state). Framed as "eventually happens" not "eventually
      // stays" — free `a_carbonDioxide` drift can cancel the purifier's −1, so `AF(≤60)` cannot
      // hold, but `AF EF(≤60)` can.
      implicationSpec('5',
        [condition('air_quality', 'variable', 'carbonDioxide', '>', '60', null, 'environment')],
        [condition('air_quality', 'variable', 'carbonDioxide', '<=', '60', null, 'environment')]
      ),
      // s8 | template 5 | expected to hold. Once the hub has sent a photo it must return to idle
      // at least once; this pins the hub's auto-return, which is what makes it reusable as a chain
      // hop rather than a one-shot. Framed as eventual not persistent for the same reason as s7.
      implicationSpec('5',
        [condition('care_hub', 'mode', 'State', '=', 'sendingPhoto')],
        [condition('care_hub', 'mode', 'State', '=', 'idle')]
      ),
      // s9 | template 3 | expected to hold at baseline, to FAIL under attack. The one property
      // that asks what the device *said* rather than what happened in the home: a monitor
      // reporting a rate outside its own alert band while still claiming `normal` is a sensor
      // lying. `environment` and `reported` diverge exactly when the device is compromised, so
      // this is unfalsifiable without an attacker and is the scene's sharpest security property.
      aSpec('3', [
        condition('vitals', 'variable', 'heartRate', '>', '130', null, 'reported'),
        condition('vitals', 'mode', 'MonitorMode', '=', 'normal')
      ]),
      // s10 | template 3 | expected to hold. "The door must never be unlocked under an untrusted
      // control path" is `AG !(...)`, template 3 — the shipped scene asked this with template 1,
      // which asserts the door is *always* untrusted and failed in the initial state for a reason
      // unrelated to any automation.
      aSpec('3', [condition('door_lock', 'trust', 'LockState', '=', 'untrusted', 'state')]),
      // s11 | template 3 | expected to hold, and the only privacy property in the scene. It reads
      // a *state* label the chain actually writes: the hub sends content, so its `State` privacy
      // must not be *downgraded* to public — `Home Mode` declares every state `Privacy: private`,
      // but `Alarm` declares all its states `Privacy: public`, so chain A's hop 2 (alarm → hub)
      // writes a `public` privacy label to `sendingAlertMessage` via the MEDIC join. Asking for
      // `= private` would fail; asking for `!= public` asserts no downgrade and holds. A variable
      // privacy label would be unfalsifiable — they are frozen (`next(p) := p`) and never written.
      aSpec('3', [condition('care_hub', 'privacy', 'State', '=', 'public', 'state')]),
      // s12 | template 3 | expected to hold. The camera must never record while the resident is in
      // bed during the night window that chain B serves. Reachability of `taking photo` is what
      // makes this non-vacuous, and chain B provides it. Adding the time guard prevents a
      // coincidence the baseline scene does not: free `a_bedOccupancy` could flip back to
      // `occupied` in the same step the camera reaches `takingphoto`, which would make the
      // unguarded form fail on a state the automation never intended.
      aSpec('3', [
        condition('camera_1', 'state', 'state', '=', 'taking photo'),
        condition('bed_sensor', 'variable', 'bedOccupancy', '=', 'occupied', null, 'environment'),
        condition('clock', 'variable', 'time', 'in', '22,23,0,1,2,3,4,5,6', null, 'environment')
      ])
    ]
  }
]

fs.mkdirSync(outputDir, { recursive: true })
for (const definition of scenes) {
  const scene = {
    schema: 'iot-verify.board-scene',
    // 5 since `variableSource` became required on a variable spec condition. Must track
    // `SCENE_FILE_VERSION` in frontend/src/views/board/portableScene.ts: the importer rejects a
    // mismatch outright, so emitting 4 while writing the field produces a file that is valid under
    // neither version.
    version: 5,
    templates: [
      ...definition.templateNames.map(loadTemplate),
      ...(definition.extraTemplates ?? [])
    ],
    devices: definition.devices,
    environmentVariables: definition.environmentVariables,
    rules: definition.rules,
    specs: definition.specs
  }
  // Tab-indented to match the committed scene files. With two spaces this script rewrote every line of
  // all four scenes on each run, so a real one-field change arrived as a 1600-line diff and the generator
  // read as drifted from its own output.
  fs.writeFileSync(path.join(outputDir, definition.file), `${JSON.stringify(scene, null, '\t')}\n`, 'utf8')
}

console.log(`Generated ${scenes.length} default-template scenes in ${outputDir}`)

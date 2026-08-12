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

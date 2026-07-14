import fs from 'node:fs'
import path from 'node:path'
import { fileURLToPath } from 'node:url'

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..')
const templateDir = path.join(repoRoot, 'backend', 'src', 'main', 'resources', 'deviceTemplate')
const outputDir = path.join(repoRoot, 'docs', 'examples')

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

const condition = (deviceId, targetType, key, relation, value, propertyScope) => ({
  deviceId,
  targetType,
  key,
  ...(propertyScope ? { propertyScope } : {}),
  relation,
  value
})

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
        [condition('smoke_1', 'variable', 'smoke', '=', 'detected')],
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
        [condition('temperature_1', 'variable', 'temperature', '>=', '28')],
        [condition('ac_1', 'mode', 'HvacMode', '=', 'cool')]),
      aSpec('3', [
        condition('temperature_1', 'variable', 'temperature', '>=', '28'),
        condition('ac_1', 'mode', 'HvacMode', '=', 'heat')
      ]),
      aSpec('1', [condition('ac_1', 'privacy', 'HvacMode', '=', 'private', 'state')]),
      aSpec('7', [condition('ac_1', 'mode', 'HvacMode', '=', 'heat')])
    ]
  },
  {
    file: 'default-rfid-access-scene.json',
    templateNames: ['Alarm', 'Door', 'Door RFID'],
    devices: [
      device('rfid_1', 'Door RFID', 'Front-door Badge Reader', 80, 120, {
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
        [condition('rfid_1', 'variable', 'RFID', '=', 'authorized')],
        [condition('door_1', 'mode', 'LockState', '=', 'unlocked')]),
      implicationSpec('4',
        [condition('rfid_1', 'variable', 'RFID', '=', 'not authorized')],
        [condition('alarm_1', 'mode', 'AlertState', '=', 'siren')]),
      aSpec('3', [
        condition('rfid_1', 'variable', 'RFID', '=', 'not authorized'),
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
    version: 4,
    templates: definition.templateNames.map(loadTemplate),
    devices: definition.devices,
    environmentVariables: definition.environmentVariables,
    rules: definition.rules,
    specs: definition.specs
  }
  fs.writeFileSync(path.join(outputDir, definition.file), `${JSON.stringify(scene, null, 2)}\n`, 'utf8')
}

console.log(`Generated ${scenes.length} default-template scenes in ${outputDir}`)

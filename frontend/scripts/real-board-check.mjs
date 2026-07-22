import { chromium } from '@playwright/test'
import fs from 'node:fs'
import path from 'node:path'

const apiBase = process.env.REAL_CHECK_API || 'http://127.0.0.1:8080/api'
const appUrl = process.env.REAL_CHECK_APP || 'http://127.0.0.1:3000/#/board'
const outDir = path.resolve('..', 'artifacts', 'playwright-real')
fs.mkdirSync(outDir, { recursive: true })
for (const entry of fs.readdirSync(outDir)) {
  if (entry.endsWith('.png')) {
    fs.rmSync(path.join(outDir, entry))
  }
}

async function request(method, urlPath, body, token, okStatuses = [200]) {
  const res = await fetch(apiBase + urlPath, {
    method,
    headers: {
      ...(body !== undefined ? { 'Content-Type': 'application/json' } : {}),
      ...(token ? { Authorization: `Bearer ${token}` } : {})
    },
    ...(body !== undefined ? { body: JSON.stringify(body) } : {})
  })
  const text = await res.text()
  let json
  try {
    json = text ? JSON.parse(text) : null
  } catch {
    json = { raw: text }
  }
  if (!okStatuses.includes(res.status)) {
    throw new Error(`${method} ${urlPath} HTTP ${res.status}: ${text}`)
  }
  if (json && typeof json.code === 'number' && json.code >= 400) {
    throw new Error(`${method} ${urlPath} result ${json.code}: ${text}`)
  }
  return json ? json.data : null
}

const get = (urlPath, token, ok) => request('GET', urlPath, undefined, token, ok)
const post = (urlPath, body, token, ok) => request('POST', urlPath, body, token, ok)

const valueFor = variable => (
  Array.isArray(variable.Values) && variable.Values.length
    ? String(variable.Values[0])
    : (typeof variable.LowerBound === 'number' ? String(variable.LowerBound) : '0')
)

const localVariablesFor = manifest => (manifest.InternalVariables || [])
  .filter(variable => variable?.IsInside === true)

const varsFor = manifest => localVariablesFor(manifest).map(variable => ({
  name: variable.Name,
  value: valueFor(variable),
  trust: variable.Trust || 'trusted'
}))

const privaciesFor = manifest => [
  ...localVariablesFor(manifest).map(variable => ({ name: variable.Name, privacy: variable.Privacy || 'public' }))
]

const environmentDefinition = (manifest, name) => (
  (manifest.InternalVariables || []).find(variable =>
    variable?.Name === name && variable?.IsInside !== true)
  || (manifest.EnvironmentDomains || []).find(domain => domain?.Name === name)
)

const environmentVariablesFor = templates => {
  const definitions = new Map()
  for (const template of templates) {
    const manifest = template.manifest
    for (const variable of manifest.InternalVariables || []) {
      if (variable?.Name && variable?.IsInside !== true) {
        definitions.set(variable.Name, variable)
      }
    }
    for (const name of manifest.ImpactedVariables || []) {
      const definition = environmentDefinition(manifest, name)
      if (!definition) throw new Error(`Template ${template.name} has no environment domain for ${name}`)
      definitions.set(name, definition)
    }
  }
  return [...definitions.entries()]
    .sort(([left], [right]) => left.localeCompare(right))
    .map(([name, definition]) => ({
      name,
      value: valueFor(definition),
      trust: definition.Trust || 'untrusted',
      privacy: definition.Privacy || 'public'
    }))
}

const hasModes = manifest => Array.isArray(manifest?.Modes) && manifest.Modes.length > 0
const initialState = manifest => hasModes(manifest)
  ? (manifest.InitState || manifest.WorkingStates?.[0]?.Name || '')
  : 'Working'

const nusmvReservedWords = new Set([
  'module', 'var', 'assign', 'init', 'trans', 'define', 'spec', 'ltlspec',
  'invars', 'ivar', 'fairness', 'justice', 'compassion',
  'true', 'false', 'case', 'esac', 'next',
  'ex', 'ax', 'ef', 'af', 'eg', 'ag',
  'e', 'f', 'o', 'g', 'h', 'x', 'y', 'z', 'w', 'a', 'u', 's', 'v', 't',
  'bu', 'ebf', 'abf', 'ebg', 'abg'
])

function normalizeNuSmvDeviceName(name) {
  if (!name) return name
  let normalized = String(name).replace(/[^a-zA-Z0-9_]/g, '_').toLowerCase()
  if (!normalized || /^_+$/.test(normalized)) normalized = 'device_0'
  if (/^\d/.test(normalized)) normalized = `_${normalized}`
  return nusmvReservedWords.has(normalized) ? `_${normalized}` : normalized
}

const modelRule = rule => ({
  ...rule,
  conditions: (rule.conditions || []).map(condition => ({
    ...condition,
    deviceName: normalizeNuSmvDeviceName(condition.deviceName)
  })),
  command: rule.command
    ? {
        ...rule.command,
        deviceName: normalizeNuSmvDeviceName(rule.command.deviceName),
        contentDevice: rule.command.contentDevice
          ? normalizeNuSmvDeviceName(rule.command.contentDevice)
          : rule.command.contentDevice
      }
    : rule.command
})

async function seedScenario() {
  const suffix = String(Date.now()).slice(-8)
  const phone = `138${suffix}`
  const password = 'RealCheck!2026'
  await post('/auth/register', { phone, username: `real${suffix}`, password })
  const auth = await post('/auth/login', { identifier: phone, password })
  const token = auth.token
  const user = { userId: auth.userId, phone: auth.phone, username: auth.username }

  const templates = await get('/board/templates', token)
  const templateByName = new Map(templates.map(template => [template.manifest.Name, template]))
  const template = name => {
    const found = templateByName.get(name)
    if (!found) throw new Error(`Missing template ${name}`)
    return found
  }

  const light = template('Light')
  const door = template('Door')
  const alarm = template('Alarm')
  const thermostat = template('Thermostat')
  const windowShade = template('Window Shade')
  const referencedTemplates = [light, door, alarm, thermostat, windowShade]
  const environmentVariables = environmentVariablesFor(referencedTemplates)
  const templateSnapshots = referencedTemplates.map(({ name, manifest }) => ({ name, manifest }))

  const nodeSpecs = [
    { id: 'node_door_entry', label: 'Entrance_Door_Long_Label_01', template: door, x: -180, y: 110, width: 178, height: 126, state: 'locked' },
    { id: 'node_light_lobby', label: 'Lobby_Light_Ceiling_Extended_Label', template: light, x: 260, y: 190, width: 184, height: 128, state: 'off' },
    { id: 'node_alarm_core', label: 'Alarm_Core_Hallway', template: alarm, x: 720, y: -90, width: 168, height: 120, state: 'off' },
    { id: 'node_thermostat_west', label: 'Thermostat_West_Wing', template: thermostat, x: 1040, y: 420, width: 196, height: 132, state: initialState(thermostat.manifest) },
    { id: 'node_shade_south', label: 'South_Window_Shade', template: windowShade, x: 520, y: 560, width: 164, height: 118, state: 'closed' }
  ]

  const nodes = nodeSpecs.map(node => {
    const modeDevice = hasModes(node.template.manifest)
    return {
      id: node.id,
      templateName: node.template.manifest.Name,
      label: node.label,
      position: { x: node.x, y: node.y },
      state: modeDevice ? node.state : 'Working',
      width: node.width,
      height: node.height,
      ...(modeDevice ? { currentStateTrust: 'trusted' } : {}),
      variables: varsFor(node.template.manifest),
      privacies: privaciesFor(node.template.manifest)
    }
  })

  const rules = [
    {
      conditions: [{ deviceName: 'node_door_entry', attribute: 'state', targetType: 'state', relation: '=', value: 'unlocked' }],
      command: { deviceName: 'node_light_lobby', action: 'on', contentDevice: null, content: null },
      ruleString: 'If the entrance door is unlocked, turn on the lobby light'
    },
    {
      conditions: [{ deviceName: 'node_thermostat_west', attribute: 'state', targetType: 'state', relation: '=', value: initialState(thermostat.manifest) }],
      command: { deviceName: 'node_shade_south', action: 'open', contentDevice: null, content: null },
      ruleString: 'If thermostat is active, open the south shade'
    }
  ]

  const specs = [
    {
      id: 'spec_light_eventually_on',
      templateId: '2',
      templateLabel: 'A will happen later',
      aConditions: [{ id: 'cond_light_on', side: 'a', deviceId: 'node_light_lobby', deviceLabel: 'Lobby_Light_Ceiling_Extended_Label', targetType: 'state', key: 'state', relation: '=', value: 'on' }],
      ifConditions: [],
      thenConditions: [],
      formula: '',
      devices: [{ deviceId: 'node_light_lobby', deviceLabel: 'Lobby_Light_Ceiling_Extended_Label', selectedApis: ['on'] }]
    },
    {
      id: 'spec_alarm_never_siren',
      templateId: '3',
      templateLabel: 'A never happens',
      aConditions: [{ id: 'cond_alarm_siren', side: 'a', deviceId: 'node_alarm_core', deviceLabel: 'Alarm_Core_Hallway', targetType: 'state', key: 'state', relation: '=', value: 'siren' }],
      ifConditions: [],
      thenConditions: [],
      formula: '',
      devices: [{ deviceId: 'node_alarm_core', deviceLabel: 'Alarm_Core_Hallway', selectedApis: ['siren'] }]
    }
  ]

  const layout = {
    canvasPan: { x: 210, y: 130 },
    canvasZoom: 0.82,
    panels: {
      control: { collapsed: false, width: 332, activeSection: 'devices' },
      inspector: { collapsed: false, width: 348, activeSection: 'devices' }
    }
  }

  const replacementPreview = await get('/board/replacement-preview', token)
  await post('/board/batch', {
    impactToken: replacementPreview.impactToken,
    nodes,
    environmentVariables,
    rules,
    specs,
    templateSnapshots
  }, token)
  await post('/board/layout', layout, token)
  const savedLayout = await get('/board/layout', token)

  const simRequest = {
    devices: nodes.map(node => {
      const templateInfo = templateByName.get(node.templateName)
      const modeDevice = hasModes(templateInfo?.manifest)
      return {
        varName: normalizeNuSmvDeviceName(node.id),
        templateName: node.templateName,
        ...(modeDevice ? {
          state: node.state,
          currentStateTrust: node.currentStateTrust
        } : {}),
        variables: node.variables,
        privacies: node.privacies
      }
    }),
    environmentVariables,
    rules: rules.map(modelRule),
    steps: 6,
    attackScenario: { mode: 'NONE', budget: 0, points: [] },
    enablePrivacy: false
  }

  const shortSimulationTrace = await post('/simulate/traces', { ...simRequest, steps: 1 }, token)
  const savedSimulationTrace = await post('/simulate/traces', simRequest, token)
  const longSimulationTrace = await post('/simulate/traces', { ...simRequest, steps: 28 }, token)

  return {
    token,
    user,
    savedLayout,
    savedSimulationTrace,
    shortSimulationTrace,
    longSimulationTrace,
    simulationSummaries: await get('/simulate/traces', token)
  }
}

function rectsOverlap(a, b, gap = 0) {
  return !(!a || !b || a.x + a.width <= b.x + gap || b.x + b.width <= a.x + gap || a.y + a.height <= b.y + gap || b.y + b.height <= a.y + gap)
}

function rectContains(outer, inner, gap = 0) {
  return Boolean(
    outer &&
    inner &&
    inner.x >= outer.x - gap &&
    inner.y >= outer.y - gap &&
    inner.x + inner.width <= outer.x + outer.width + gap &&
    inner.y + inner.height <= outer.y + outer.height + gap
  )
}

async function runUiChecks(seed) {
  const browser = await chromium.launch({ headless: true })
  const context = await browser.newContext({ viewport: { width: 1440, height: 920 }, deviceScaleFactor: 1 })
  await context.addInitScript(({ token, user }) => {
    localStorage.setItem('iot_verify_token', token)
    localStorage.setItem('iot_verify_user', JSON.stringify(user))
    localStorage.setItem('iot_verify_theme', 'light')
    localStorage.setItem('locale', 'en')
  }, { token: seed.token, user: seed.user })

  const page = await context.newPage()
  const failures = []
  const browserEvents = []
  page.on('console', msg => {
    if (['error', 'warning'].includes(msg.type())) {
      browserEvents.push(`${msg.type()}: ${msg.text()}`)
    }
  })
  page.on('pageerror', error => {
    const message = `pageerror: ${error.message}`
    browserEvents.push(message)
    failures.push(message)
  })
  const soft = (condition, message) => { if (!condition) failures.push(message) }
  const box = selector => page.locator(selector).first().boundingBox()
  const isVisible = async selector => {
    try {
      return await page.locator(selector).first().isVisible()
    } catch {
      return false
    }
  }
  const closeIfVisible = async (panelSelector, closeSelector) => {
    if (await isVisible(panelSelector)) {
      await page.locator(closeSelector).first().click({ timeout: 1000 })
      await page.locator(panelSelector).first().waitFor({ state: 'hidden', timeout: 3000 }).catch(() => {})
    }
  }
  const closeFloatingPanels = async () => {
    await closeIfVisible('[data-testid="simulation-timeline"]', '[data-testid="simulation-timeline-close"]')
    await closeIfVisible('[data-testid="simulation-panel"]', '[data-testid="close-simulation-panel"]')
    await closeIfVisible('[data-testid="verification-panel"]', '[data-testid="close-verification-panel"]')
    await closeIfVisible('[data-testid="trace-history-panel"]', '[data-testid="close-history-panel"]')
    await closeIfVisible('[data-testid="rule-recommendation-panel"]', '[data-testid="close-rule-recommendations"]')
    await closeIfVisible('[data-testid="device-recommendation-panel"]', '[data-testid="close-device-recommendations"]')
    await closeIfVisible('[data-testid="spec-recommendation-panel"]', '[data-testid="close-spec-recommendations"]')
  }
  const checkInViewport = (panelBox, label, viewport = { width: 1440, height: 920 }) => {
    soft(Boolean(panelBox), `${label} did not render a measurable box`)
    if (!panelBox) return
    soft(panelBox.x >= -1 && panelBox.y >= -1, `${label} starts outside viewport`)
    soft(panelBox.x + panelBox.width <= viewport.width + 1, `${label} overflows right edge`)
    soft(panelBox.y + panelBox.height <= viewport.height + 1, `${label} overflows bottom edge`)
  }
  const checkNoInlineOverflow = async (selector, label) => {
    const overflowing = await page.locator(selector).evaluateAll(elements =>
      elements
        .map(el => ({
          text: (el.textContent || '').trim(),
          isIcon: el.classList.contains('material-symbols-outlined'),
          visible: (() => {
            const rect = el.getBoundingClientRect()
            return rect.width > 0 && rect.height > 0
          })(),
          overflowX: getComputedStyle(el).overflowX,
          overflowY: getComputedStyle(el).overflowY,
          textOverflow: getComputedStyle(el).textOverflow,
          scrollWidth: el.scrollWidth,
          clientWidth: el.clientWidth,
          scrollHeight: el.scrollHeight,
          clientHeight: el.clientHeight
        }))
        .filter(item => {
          if (item.isIcon || !item.visible || !item.text) return false
          const horizontalOverflow = item.scrollWidth > item.clientWidth + 2
          const verticalOverflow = item.scrollHeight > item.clientHeight + 4
          const handlesHorizontal = item.textOverflow === 'ellipsis' || item.overflowX !== 'visible'
          const handlesVertical = item.overflowY !== 'visible'
          return (horizontalOverflow && !handlesHorizontal) || (verticalOverflow && !handlesVertical)
        })
        .slice(0, 5)
    )
    soft(overflowing.length === 0, `${label} text overflow: ${JSON.stringify(overflowing)}`)
  }
  const openAndCheckFloatingPanel = async ({ open, panel, close, screenshot, label, viewport }) => {
    await closeFloatingPanels()
    await page.locator(open).click()
    await page.waitForSelector(panel, { timeout: 5000 })
    if (screenshot) {
      await page.screenshot({ path: path.join(outDir, screenshot), fullPage: true })
    }
    const panelBox = await box(panel)
    const currentControlBox = await box('[data-testid="control-center"]')
    const currentInspectorBox = await box('[data-testid="system-inspector"]')
    const currentMapBox = await box('[data-testid="canvas-map"]')
    checkInViewport(panelBox, label, viewport || page.viewportSize() || undefined)
    soft(!rectsOverlap(panelBox, currentControlBox, -2), `${label} overlaps control panel`)
    soft(!rectsOverlap(panelBox, currentInspectorBox, -2), `${label} overlaps inspector panel`)
    soft(!currentMapBox || !rectsOverlap(panelBox, currentMapBox, -2), `${label} overlaps canvas map`)
    await checkNoInlineOverflow(`${panel} button, ${panel} label, ${panel} h3`, `${label} controls`)
    await closeIfVisible(panel, close)
  }

  await page.goto(appUrl, { waitUntil: 'networkidle' })
  await page.waitForSelector('[data-testid="board-root"]')
  await page.waitForFunction(() => document.querySelectorAll('.device-node').length >= 5, null, { timeout: 20000 })
  await page.screenshot({ path: path.join(outDir, 'board-desktop-light.png'), fullPage: true })

  soft(await page.evaluate(() => document.documentElement.dataset.theme) === 'light', 'expected light theme')

  const nodeMetrics = await page.evaluate(() => ({
    nodes: document.querySelectorAll('.device-node').length,
    labels: [...document.querySelectorAll('.device-label')].map(el => ({
      text: el.textContent.trim(),
      scrollHeight: el.scrollHeight,
      clientHeight: el.clientHeight,
      scrollWidth: el.scrollWidth,
      clientWidth: el.clientWidth,
      overflow: getComputedStyle(el).overflow,
      title: el.getAttribute('title')
    })),
    states: [...document.querySelectorAll('.device-state-value')].map(el => ({
      text: el.textContent.trim(),
      scrollWidth: el.scrollWidth,
      clientWidth: el.clientWidth,
      overflow: getComputedStyle(el).overflow,
      title: el.parentElement?.getAttribute('title')
    }))
  }))
  soft(nodeMetrics.nodes >= 5, `expected >=5 nodes, got ${nodeMetrics.nodes}`)
  for (const label of nodeMetrics.labels) {
    const clipped = label.scrollHeight > label.clientHeight + 2
      || label.scrollWidth > label.clientWidth + 2
    soft(!clipped || (label.overflow !== 'visible' && label.title === label.text),
      `label overflow is not safely recoverable: ${label.text}`)
  }
  for (const state of nodeMetrics.states) {
    const clipped = state.scrollWidth > state.clientWidth + 2
    soft(!clipped || (state.overflow !== 'visible' && state.title === state.text),
      `state overflow is not safely recoverable: ${state.text}`)
  }

  const controlBox = await box('[data-testid="control-center"]')
  const inspectorBox = await box('[data-testid="system-inspector"]')
  const canvasBox = await box('[data-testid="canvas-board"]')
  const mapBox = await box('[data-testid="canvas-map"]')
  const actionRailBox = await box('.board-floating-actions')
  soft(controlBox && controlBox.width >= 300 && controlBox.width <= 360, `control width unexpected: ${controlBox?.width}`)
  soft(inspectorBox && inspectorBox.width >= 320 && inspectorBox.width <= 370, `inspector width unexpected: ${inspectorBox?.width}`)
  soft(canvasBox && canvasBox.width > 1000, `canvas too narrow: ${canvasBox?.width}`)
  soft(Boolean(mapBox), 'canvas map did not render inside inspector panel')
  soft(!rectsOverlap(mapBox, controlBox, -2), 'canvas map overlaps control panel')
  soft(rectContains(inspectorBox, mapBox, 2), 'canvas map is not contained by inspector panel')
  soft(!rectsOverlap(actionRailBox, inspectorBox, -2), 'floating action rail overlaps inspector panel')
  soft(actionRailBox && actionRailBox.height < 920 * 0.7, `floating action rail too tall: ${actionRailBox?.height}`)
  soft(await page.locator('.board-floating-actions .absolute.-top-1').count() === 0, 'floating action rail still renders an unexplained corner badge')
  const toolRailAudit = await page.locator('.board-floating-actions').evaluate(rail => ({
    role: rail.getAttribute('role'),
    ariaLabel: rail.getAttribute('aria-label'),
    toggle: (() => {
      const button = rail.querySelector('[data-testid="toggle-action-dock"]')
      return button
        ? {
            ariaLabel: button.getAttribute('aria-label'),
            ariaPressed: button.getAttribute('aria-pressed'),
            ariaExpanded: button.getAttribute('aria-expanded'),
            icon: button.querySelector('.material-symbols-outlined')?.textContent?.trim() || ''
          }
        : null
    })(),
    groups: Array.from(rail.querySelectorAll('[role="group"]')).map(group => ({
      testId: group.getAttribute('data-testid'),
      ariaLabel: group.getAttribute('aria-label')
    })),
    buttons: Array.from(rail.querySelectorAll('.board-tool-button')).map(button => ({
      testId: button.getAttribute('data-testid'),
      ariaLabel: button.getAttribute('aria-label'),
      ariaPressed: button.getAttribute('aria-pressed'),
      icon: button.querySelector('.material-symbols-outlined')?.textContent?.trim() || '',
      label: button.querySelector('.board-tool-label')?.textContent?.trim() || '',
      labelVisible: (() => {
        const label = button.querySelector('.board-tool-label')
        if (!label) return false
        const rect = label.getBoundingClientRect()
        return rect.width > 0 && rect.height > 0 && getComputedStyle(label).display !== 'none'
      })()
    }))
  }))
  soft(toolRailAudit.role === 'toolbar', `floating action rail role mismatch: ${toolRailAudit.role}`)
  soft(Boolean(toolRailAudit.ariaLabel), 'floating action rail missing aria-label')
  soft(toolRailAudit.groups.length === 2, `floating action rail expected 2 groups, got ${toolRailAudit.groups.length}`)
  soft(toolRailAudit.groups.some(group => group.testId === 'run-tool-group' && group.ariaLabel), 'run tool group missing accessible name')
  soft(toolRailAudit.groups.some(group => group.testId === 'ai-tool-group' && group.ariaLabel), 'AI tool group missing accessible name')
  soft(toolRailAudit.toggle && toolRailAudit.toggle.ariaLabel && toolRailAudit.toggle.ariaExpanded !== null, `action dock toggle missing aria metadata: ${JSON.stringify(toolRailAudit.toggle)}`)
  soft(toolRailAudit.buttons.length === 8, `floating action rail expected 8 buttons, got ${toolRailAudit.buttons.length}`)
  soft(toolRailAudit.buttons.every(button => button.ariaLabel && button.ariaPressed !== null), `tool buttons missing aria metadata: ${JSON.stringify(toolRailAudit.buttons)}`)
  soft(new Set(toolRailAudit.buttons.map(button => button.icon)).size === toolRailAudit.buttons.length, `tool icons are not visually distinct: ${JSON.stringify(toolRailAudit.buttons.map(button => button.icon))}`)
  soft(toolRailAudit.buttons.every(button => button.labelVisible && button.label), `desktop tool labels are not visible: ${JSON.stringify(toolRailAudit.buttons)}`)
  await checkNoInlineOverflow('.board-floating-actions button', 'floating action buttons')

  for (const section of ['devices', 'templates', 'rules', 'specs']) {
    await page.locator(`[data-testid="control-tab-${section}"]`).click()
    await page.waitForSelector(`[data-testid="control-section-${section}"]`, { timeout: 3000 })
    await checkNoInlineOverflow('[data-testid="control-center"] button, [data-testid="control-center"] label, [data-testid="control-center"] h2, [data-testid="control-center"] h4', `control center ${section}`)
  }
  await page.locator('[data-testid="control-tab-devices"]').click()
  await checkNoInlineOverflow('[data-testid="system-inspector"] h2, [data-testid="system-inspector"] h3, [data-testid="system-inspector"] h4, [data-testid="system-inspector"] span, [data-testid="system-inspector"] p', 'system inspector')
  const inspectorTabAudit = await page.locator('[data-testid^="inspector-tab-"]').evaluateAll(tabs => tabs.map(tab => ({
    testId: tab.getAttribute('data-testid'),
    role: tab.getAttribute('role'),
    ariaSelected: tab.getAttribute('aria-selected'),
    ariaPressed: tab.getAttribute('aria-pressed'),
    text: (tab.textContent || '').trim()
  })))
  soft(inspectorTabAudit.length === 3, `system inspector expected 3 entity tabs, got ${inspectorTabAudit.length}`)
  soft(inspectorTabAudit.every(tab => tab.role === 'tab' && tab.ariaSelected !== null && tab.ariaPressed !== null && tab.text), `system inspector tabs missing semantics: ${JSON.stringify(inspectorTabAudit)}`)
  for (const section of ['rules', 'specs', 'devices']) {
    await page.locator(`[data-testid="inspector-tab-${section}"]`).click()
    await page.waitForSelector(`[data-testid="inspector-section-${section}"]`, { timeout: 3000 })
    await checkNoInlineOverflow(`[data-testid="inspector-section-${section}"] button, [data-testid="inspector-section-${section}"] h3, [data-testid="inspector-section-${section}"] h4, [data-testid="inspector-section-${section}"] p`, `system inspector ${section}`)
  }
  await page.locator('[data-testid="inspector-tab-specs"]').click()
  await page.waitForSelector('[data-testid="inspector-section-specs"]', { timeout: 3000 })
  await page.locator('[data-testid="inspector-add-spec"]').click()
  await page.waitForSelector('[data-testid="control-section-specs"]', { timeout: 3000 })
  await page.locator('[data-testid="inspector-tab-devices"]').click()
  await page.waitForSelector('[data-testid="inspector-section-devices"]', { timeout: 3000 })
  await page.locator('[data-testid="inspector-add-device"]').click()
  await page.waitForSelector('[data-testid="control-section-devices"]', { timeout: 3000 })

  const fallbackIcon = await page.locator('.device-img').first().evaluate(img => {
    img.setAttribute('src', '/assets/definitely-missing-device-icon.svg')
    img.dispatchEvent(new Event('error'))
    return img.getAttribute('src')
  })
  soft(fallbackIcon?.startsWith('data:image/svg+xml;base64,'), `missing device image did not fall back to inline SVG: ${fallbackIcon}`)

  const canvasBeforeFit = await page.locator('.canvas-inner').evaluate(el => getComputedStyle(el).transform)
  await page.locator('[data-testid="canvas-map-fit"]').click()
  await page.waitForTimeout(200)
  const canvasAfterFit = await page.locator('.canvas-inner').evaluate(el => getComputedStyle(el).transform)
  soft(canvasAfterFit !== canvasBeforeFit, 'canvas map fit button did not adjust viewport transform')

  const gridRendering = await page.evaluate(() => {
    const canvas = document.querySelector('[data-testid="canvas-board"]')
    const inner = document.querySelector('.canvas-inner')
    const canvasStyle = canvas ? getComputedStyle(canvas) : null
    const innerStyle = inner ? getComputedStyle(inner) : null
    return {
      canvasBg: canvasStyle?.backgroundImage,
      canvasSize: canvasStyle?.backgroundSize,
      innerBg: innerStyle?.backgroundImage
    }
  })
  soft(gridRendering.canvasBg?.includes('linear-gradient'), 'canvas grid is not painted on the viewport')
  soft(gridRendering.innerBg === 'none', `canvas inner still owns grid background: ${gridRendering.innerBg}`)

  const surfaceColorsLight = await page.evaluate(() => {
    const css = (selector, prop) => getComputedStyle(document.querySelector(selector)).getPropertyValue(prop)
    return {
      controlBg: css('[data-testid="control-center"]', 'background-image') || css('[data-testid="control-center"]', 'background-color'),
      mapBg: css('[data-testid="canvas-map"]', 'background-color')
    }
  })

  await openAndCheckFloatingPanel({
    open: '[data-testid="open-verification-panel"]',
    panel: '[data-testid="verification-panel"]',
    close: '[data-testid="close-verification-panel"]',
    screenshot: 'verification-panel-light.png',
    label: 'verification panel'
  })
  await openAndCheckFloatingPanel({
    open: '[data-testid="open-simulation-panel"]',
    panel: '[data-testid="simulation-panel"]',
    close: '[data-testid="close-simulation-panel"]',
    screenshot: 'simulation-panel-light.png',
    label: 'simulation panel'
  })
  await openAndCheckFloatingPanel({
    open: '[data-testid="open-history-panel"]',
    panel: '[data-testid="trace-history-panel"]',
    close: '[data-testid="close-history-panel"]',
    screenshot: 'history-panel-light.png',
    label: 'history panel'
  })
  await openAndCheckFloatingPanel({
    open: '[data-testid="open-rule-recommendations"]',
    panel: '[data-testid="rule-recommendation-panel"]',
    close: '[data-testid="close-rule-recommendations"]',
    screenshot: 'rule-recommendations-light.png',
    label: 'rule recommendation panel'
  })
  await openAndCheckFloatingPanel({
    open: '[data-testid="open-device-recommendations"]',
    panel: '[data-testid="device-recommendation-panel"]',
    close: '[data-testid="close-device-recommendations"]',
    screenshot: 'device-recommendations-light.png',
    label: 'device recommendation panel'
  })
  await openAndCheckFloatingPanel({
    open: '[data-testid="open-spec-recommendations"]',
    panel: '[data-testid="spec-recommendation-panel"]',
    close: '[data-testid="close-spec-recommendations"]',
    screenshot: 'spec-recommendations-light.png',
    label: 'specification recommendation panel'
  })

  const floatingPanels = [
    {
      open: '[data-testid="open-verification-panel"]',
      panel: '[data-testid="verification-panel"]',
      close: '[data-testid="close-verification-panel"]',
      label: 'verification panel'
    },
    {
      open: '[data-testid="open-simulation-panel"]',
      panel: '[data-testid="simulation-panel"]',
      close: '[data-testid="close-simulation-panel"]',
      label: 'simulation panel'
    },
    {
      open: '[data-testid="open-history-panel"]',
      panel: '[data-testid="trace-history-panel"]',
      close: '[data-testid="close-history-panel"]',
      label: 'history panel'
    },
    {
      open: '[data-testid="open-rule-recommendations"]',
      panel: '[data-testid="rule-recommendation-panel"]',
      close: '[data-testid="close-rule-recommendations"]',
      label: 'rule recommendation panel'
    },
    {
      open: '[data-testid="open-device-recommendations"]',
      panel: '[data-testid="device-recommendation-panel"]',
      close: '[data-testid="close-device-recommendations"]',
      label: 'device recommendation panel'
    },
    {
      open: '[data-testid="open-spec-recommendations"]',
      panel: '[data-testid="spec-recommendation-panel"]',
      close: '[data-testid="close-spec-recommendations"]',
      label: 'specification recommendation panel'
    }
  ]

  await page.setViewportSize({ width: 720, height: 720 })
  await page.waitForTimeout(300)
  const midWidthNavigation = await page.evaluate(() => {
    const rect = selector => {
      const element = document.querySelector(selector)
      if (!element) return null
      const box = element.getBoundingClientRect()
      return { left: box.left, right: box.right, width: box.width, height: box.height }
    }
    const menu = document.querySelector('details.scene-actions-menu')
    return {
      logout: rect('.nav-logout-btn'),
      sceneMenuVisible: Boolean(menu && menu.getClientRects().length),
      visibleFullSceneActions: [...document.querySelectorAll('.scene-action-btn')]
        .filter(element => element.getClientRects().length > 0).length
    }
  })
  soft(midWidthNavigation.logout
    && midWidthNavigation.logout.left >= 0
    && midWidthNavigation.logout.right <= 720,
  `720px navigation logout is outside the viewport: ${JSON.stringify(midWidthNavigation.logout)}`)
  soft(midWidthNavigation.logout?.width >= 44 && midWidthNavigation.logout?.height >= 44,
    `720px navigation logout is below the 44px target: ${JSON.stringify(midWidthNavigation.logout)}`)
  soft(midWidthNavigation.sceneMenuVisible, '720px navigation did not expose the compact scene-actions menu')
  soft(midWidthNavigation.visibleFullSceneActions === 0,
    `720px navigation still renders ${midWidthNavigation.visibleFullSceneActions} full scene actions`)

  await page.setViewportSize({ width: 1100, height: 820 })
  await page.waitForTimeout(300)
  for (const panelConfig of floatingPanels) {
    await openAndCheckFloatingPanel({
      ...panelConfig,
      viewport: { width: 1100, height: 820 },
      label: `${panelConfig.label} at 1100px`
    })
  }
  await page.setViewportSize({ width: 1440, height: 920 })
  await page.waitForTimeout(300)

  await page.locator('[data-testid="open-history-panel"]').click()
  await page.waitForSelector('[data-testid="trace-history-panel"]')
  const historyBox = await box('[data-testid="trace-history-panel"]')
  soft(historyBox && historyBox.x + historyBox.width <= 1440 && historyBox.y >= 0, 'history panel outside viewport')
  soft(!rectsOverlap(historyBox, controlBox, -2), 'history panel overlaps control panel')
  await closeIfVisible('[data-testid="trace-history-panel"]', '[data-testid="close-history-panel"]')

  await page.locator('[data-testid="open-simulation-panel"]').click()
  await page.waitForSelector('[data-testid="simulation-panel"]')
  const simulationPanelBox = await box('[data-testid="simulation-panel"]')
  soft(simulationPanelBox && simulationPanelBox.x + simulationPanelBox.width <= 1440, 'simulation panel outside viewport')
  soft(!rectsOverlap(simulationPanelBox, inspectorBox, -2), 'simulation panel overlaps inspector panel')
  await closeIfVisible('[data-testid="simulation-panel"]', '[data-testid="close-simulation-panel"]')

  const replaySimulationTrace = async (trace, label) => {
    if (!trace) return null
    await closeFloatingPanels()
    await page.locator('[data-testid="open-history-panel"]').click()
    await page.waitForSelector('[data-testid="trace-history-panel"]')
    await page.locator('[data-testid="history-layer-results"]').click()
    await page.waitForSelector('[data-testid="history-result-filter-simulation"]')
    await page.locator('[data-testid="history-result-filter-simulation"]').click()
    const replaySelector = `[data-testid="replay-simulation-trace-${trace.id}"]`
    await page.waitForSelector(replaySelector, { timeout: 10000 })
    await page.locator(replaySelector).click()
    try {
      await page.waitForSelector('[data-testid="simulation-timeline"]', { timeout: 10000 })
      await page.screenshot({ path: path.join(outDir, `simulation-timeline-${label}.png`), fullPage: true })
      const timelineBox = await box('[data-testid="simulation-timeline"]')
      const mapDuringTimelineBox = await box('[data-testid="canvas-map"]')
      soft(timelineBox && timelineBox.y + timelineBox.height <= 920, 'simulation timeline overflows bottom')
      soft(!rectsOverlap(timelineBox, controlBox, -2), 'simulation timeline overlaps control panel')
      soft(!rectsOverlap(timelineBox, inspectorBox, -2), 'simulation timeline overlaps inspector panel')
      soft(!rectsOverlap(mapDuringTimelineBox, timelineBox, -2), 'canvas map overlaps simulation timeline')
      const scroll = await page.locator('[data-testid="simulation-timeline-scroll"]').evaluate(el => ({
        scrollWidth: el.scrollWidth,
        clientWidth: el.clientWidth
      }))
      const stateCount = await page.locator('[data-testid^="simulation-timeline-state-"]').count()
      return { stateCount, scroll }
    } catch (error) {
      await page.screenshot({ path: path.join(outDir, `simulation-timeline-${label}-missing.png`), fullPage: true })
      failures.push(`simulation timeline did not appear for ${label}: ${error.message}`)
      return null
    }
  }

  if (seed.savedSimulationTrace && seed.simulationSummaries.length > 0) {
    const standardTimeline = await replaySimulationTrace(seed.savedSimulationTrace, 'standard-light')
    if (standardTimeline) {
      soft(standardTimeline.stateCount >= 4, `standard timeline has too few states: ${standardTimeline.stateCount}`)
      await page.locator('[data-testid="simulation-timeline-play"]').click()
      await page.waitForFunction(() =>
        document.querySelector('[data-testid="simulation-timeline"]')?.getAttribute('data-selected-state-index') === '1',
        null,
        { timeout: 2500 }
      )
      if (standardTimeline.stateCount > 3) {
        await page.locator('[data-testid="simulation-timeline-state-3"]').click()
        await page.waitForFunction(() =>
          document.querySelector('[data-testid="simulation-timeline"]')?.getAttribute('data-selected-state-index') === '3',
          null,
          { timeout: 1000 }
        )
      }
      await closeIfVisible('[data-testid="simulation-timeline"]', '[data-testid="simulation-timeline-close"]')
    }

    const shortTimeline = await replaySimulationTrace(seed.shortSimulationTrace, 'short-light')
    if (shortTimeline) {
      soft(shortTimeline.stateCount <= 3, `short timeline should remain compact, got ${shortTimeline.stateCount} states`)
      soft(shortTimeline.scroll.scrollWidth <= shortTimeline.scroll.clientWidth + 2, 'short timeline unexpectedly scrolls horizontally')
      await closeIfVisible('[data-testid="simulation-timeline"]', '[data-testid="simulation-timeline-close"]')
    }

    const longTimeline = await replaySimulationTrace(seed.longSimulationTrace, 'long-light')
    if (longTimeline) {
      soft(longTimeline.stateCount > 15, `long timeline should have >15 states, got ${longTimeline.stateCount}`)
      soft(longTimeline.scroll.scrollWidth > longTimeline.scroll.clientWidth + 2, 'long timeline does not expose horizontal scrolling')
      await closeIfVisible('[data-testid="simulation-timeline"]', '[data-testid="simulation-timeline-close"]')
    }
  }

  await page.evaluate(() => {
    localStorage.setItem('iot_verify_theme', 'dark')
    document.documentElement.dataset.theme = 'dark'
    document.documentElement.classList.add('dark')
  })
  await page.waitForTimeout(250)
  await page.screenshot({ path: path.join(outDir, 'board-dark.png'), fullPage: true })
  const darkColors = await page.evaluate(() => {
    const read = (selector, prop = 'backgroundColor') => {
      const el = document.querySelector(selector)
      return el ? getComputedStyle(el)[prop] : null
    }
    return {
      controlBg: read('[data-testid="control-center"]'),
      mapBg: read('[data-testid="canvas-map"]'),
      cardBg: read('.board-card-surface')
    }
  })
  soft(darkColors.controlBg && !/rgb\(255, 255, 255\)/.test(darkColors.controlBg), `dark control panel is white: ${darkColors.controlBg}`)
  soft(darkColors.mapBg && !/rgb\(255, 255, 255\)/.test(darkColors.mapBg), `dark canvas map is white: ${darkColors.mapBg}`)
  await page.locator('[data-testid="open-rule-recommendations"]').click()
  await page.waitForSelector('[data-testid="rule-recommendation-panel"]', { timeout: 5000 })
  await page.screenshot({ path: path.join(outDir, 'rule-recommendations-dark.png'), fullPage: true })
  darkColors.rulePanel = await page.locator('[data-testid="rule-recommendation-panel"]').evaluate(panel => {
    const content = panel.querySelector(':scope > .p-3')
    const title = panel.querySelector('h3')
    const subtitle = panel.querySelector('p')
    return {
      contentBg: content ? getComputedStyle(content).backgroundColor : null,
      titleColor: title ? getComputedStyle(title).color : null,
      subtitleColor: subtitle ? getComputedStyle(subtitle).color : null,
      mapVisible: Boolean(document.querySelector('[data-testid="canvas-map"]')?.getClientRects().length)
    }
  })
  soft(darkColors.rulePanel.contentBg && !/rgb\(255, 255, 255\)/.test(darkColors.rulePanel.contentBg), `dark rule panel content is white: ${darkColors.rulePanel.contentBg}`)
  soft(darkColors.rulePanel.titleColor === 'rgb(255, 255, 255)', `dark rule panel title is not white: ${darkColors.rulePanel.titleColor}`)
  soft(darkColors.rulePanel.mapVisible === false, 'canvas map remains visible while a floating panel is open')

  await closeFloatingPanels()
  await page.evaluate(() => {
    localStorage.setItem('iot_verify_theme', 'light')
    document.documentElement.dataset.theme = 'light'
    document.documentElement.classList.remove('dark')
  })
  await page.goto(appUrl, { waitUntil: 'networkidle' })
  await page.waitForSelector('[data-testid="board-root"]')
  await page.waitForFunction(() => document.querySelectorAll('.device-node').length >= 5, null, { timeout: 20000 })
  await page.locator('[aria-label="Switch language"]').first().click()
  await page.waitForFunction(() => localStorage.getItem('locale') === 'zh-CN', null, { timeout: 3000 })
  await page.screenshot({ path: path.join(outDir, 'board-zh-light.png'), fullPage: true })
  const zhControlText = await page.locator('[data-testid="control-center"]').innerText()
  soft(zhControlText.includes('控制中心'), 'Chinese locale did not render control center copy')
  await page.locator('[data-testid="open-rule-recommendations"]').click()
  await page.waitForSelector('[data-testid="rule-recommendation-panel"]', { timeout: 5000 })
  const zhRulePanelText = await page.locator('[data-testid="rule-recommendation-panel"]').innerText()
  soft(zhRulePanelText.includes('类别') && zhRulePanelText.includes('数量'), 'Chinese recommendation panel missing localized filter labels')
  soft(!/\bCategory\b|\bCount\b|\bRefresh\b/.test(zhRulePanelText), 'Chinese recommendation panel still contains English control labels')
  await page.screenshot({ path: path.join(outDir, 'rule-recommendations-zh-light.png'), fullPage: true })
  await closeIfVisible('[data-testid="rule-recommendation-panel"]', '[data-testid="close-rule-recommendations"]')

  await page.setViewportSize({ width: 390, height: 844 })
  await page.evaluate(() => {
    localStorage.setItem('iot_verify_theme', 'dark')
    document.documentElement.dataset.theme = 'dark'
    document.documentElement.classList.add('dark')
  })
  await page.goto(appUrl, { waitUntil: 'networkidle' })
  await page.waitForSelector('[data-testid="board-root"]')
  await page.waitForFunction(() => document.querySelectorAll('.device-node').length >= 5, null, { timeout: 20000 })
  await page.waitForFunction(() => {
    const control = document.querySelector('[data-testid="control-center"]')
    const inspector = document.querySelector('[data-testid="system-inspector"]')
    if (!control || !inspector) return false
    return control.getBoundingClientRect().width <= 88
      && inspector.getBoundingClientRect().width <= 88
  }, null, { timeout: 3000 }).catch(() => {})
  await page.screenshot({ path: path.join(outDir, 'board-mobile-dark.png'), fullPage: true })
  const mobile = await page.evaluate(() => {
    const rect = selector => {
      const el = document.querySelector(selector)
      if (!el) return null
      const r = el.getBoundingClientRect()
      return { x: r.x, y: r.y, width: r.width, height: r.height, right: r.right, bottom: r.bottom }
    }
    return {
      vp: { w: window.innerWidth, h: window.innerHeight },
      control: rect('[data-testid="control-center"]'),
      inspector: rect('[data-testid="system-inspector"]'),
      map: rect('[data-testid="canvas-map"]'),
      nodes: document.querySelectorAll('.device-node').length
    }
  })
  soft(mobile.control && mobile.control.width <= 88, `mobile control panel should start collapsed, got ${mobile.control?.width}`)
  soft(mobile.inspector && mobile.inspector.width <= 88, `mobile inspector panel should start collapsed, got ${mobile.inspector?.width}`)
  soft(!mobile.map || mobile.map.right <= mobile.vp.w + 1, 'mobile canvas map overflows right edge')
  soft(mobile.nodes >= 5, 'mobile did not render seeded nodes')

  await browser.close()
  return { failures, browserEvents, surfaceColorsLight, darkColors }
}

const seed = await seedScenario()
const ui = await runUiChecks(seed)
const summary = {
  user: seed.user,
  layoutPanels: seed.savedLayout.panels,
  savedSimulationTraceId: seed.savedSimulationTrace?.id ?? null,
  shortSimulationTraceId: seed.shortSimulationTrace?.id ?? null,
  longSimulationTraceId: seed.longSimulationTrace?.id ?? null,
  simulationSummaries: seed.simulationSummaries.length,
  surfaceColorsLight: ui.surfaceColorsLight,
  darkColors: ui.darkColors,
  browserEvents: ui.browserEvents,
  screenshots: fs.readdirSync(outDir).map(name => path.join(outDir, name)),
  failures: ui.failures
}
console.log(JSON.stringify(summary, null, 2))
if (ui.failures.length) process.exit(1)

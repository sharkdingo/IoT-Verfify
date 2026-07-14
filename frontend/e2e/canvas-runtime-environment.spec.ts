import { expect, type APIRequestContext, type Page, test } from '@playwright/test'

const apiBaseURL = process.env.E2E_API_BASE_URL || 'http://127.0.0.1:8080'

type AuthUser = {
  userId: number
  phone: string
  username: string
  token: string
}

const authHeaders = (auth: AuthUser) => ({
  Authorization: `Bearer ${auth.token}`
})

const unwrap = async <T>(response: Awaited<ReturnType<APIRequestContext['get']>>): Promise<T> => {
  expect(response.ok(), await response.text()).toBeTruthy()
  const body = await response.json()
  expect(body.code, JSON.stringify(body)).toBe(200)
  return body.data as T
}

const createAuthenticatedUser = async (request: APIRequestContext): Promise<AuthUser> => {
  const suffix = String(Date.now() % 100_000_000).padStart(8, '0')
  const phone = `137${suffix}`
  const password = 'Pass1234'
  const username = `canvas${Date.now().toString(36).slice(-9)}`

  const registerResponse = await request.post(`${apiBaseURL}/api/auth/register`, {
    data: { phone, username, password }
  })
  expect(registerResponse.ok(), await registerResponse.text()).toBeTruthy()

  const loginResponse = await request.post(`${apiBaseURL}/api/auth/login`, {
    data: { identifier: username, password }
  })
  return unwrap<AuthUser>(loginResponse)
}

const openWorkspace = async (page: Page, auth: AuthUser) => {
  await page.addInitScript(({ token, user }) => {
    window.localStorage.setItem('iot_verify_token', token)
    window.localStorage.setItem('iot_verify_user', JSON.stringify(user))
    window.localStorage.setItem('iot_verify_theme', 'light')
    window.localStorage.setItem('locale', 'en')
  }, {
    token: auth.token,
    user: {
      userId: auth.userId,
      phone: auth.phone,
      username: auth.username
    }
  })

  await page.goto('/#/board')
  await expect(page.getByTestId('board-root')).toBeVisible({ timeout: 30_000 })
}

test('canvas node focus keeps environment variables scenario-level', async ({ page, request }) => {
  const auth = await createAuthenticatedUser(request)

  const seedNode = {
    id: 'temp_sensor_1',
    templateName: 'Temperature Sensor',
    label: 'Temp Sensor',
    position: { x: 1100, y: 540 },
    state: 'Working',
    width: 220,
    height: 180
  }

  const saveResponse = await request.post(`${apiBaseURL}/api/board/batch`, {
    headers: authHeaders(auth),
    data: { nodes: [seedNode] }
  })
  expect(saveResponse.ok(), await saveResponse.text()).toBeTruthy()

  const environmentResponse = await request.post(`${apiBaseURL}/api/board/environment`, {
    headers: authHeaders(auth),
    data: [{ name: 'temperature', value: '31', trust: 'trusted', privacy: 'public' }]
  })
  expect(environmentResponse.ok(), await environmentResponse.text()).toBeTruthy()

  const layoutResponse = await request.post(`${apiBaseURL}/api/board/layout`, {
    headers: authHeaders(auth),
    data: {
      canvasPan: { x: 0, y: 0 },
      canvasZoom: 0.4,
      panels: {
        control: { collapsed: false, width: 320, activeSection: 'templates' },
        inspector: { collapsed: false, width: 320, activeSection: 'devices' }
      }
    }
  })
  expect(layoutResponse.ok(), await layoutResponse.text()).toBeTruthy()

  await openWorkspace(page, auth)

  const node = page.locator('[data-node-id="temp_sensor_1"]')
  await expect(node).toBeVisible({ timeout: 30_000 })
  await expect(node).toHaveClass(/device-node--compact/)
  await node.click({ button: 'right' })
  await expect(page.getByTestId('device-dialog')).toHaveCount(0)
  await expect(page.locator('.board-context-menu')).toHaveCount(0)

  const environmentPool = page.getByTestId('environment-pool')
  await expect(environmentPool).toBeVisible()
  await expect(environmentPool).toContainText('temperature')
  await page.getByTestId('toggle-environment-pool').click()
  await environmentPool.locator('article').filter({ hasText: 'temperature' }).getByRole('button').first().click()
  await expect(environmentPool).not.toContainText('a_temperature')
  await expect(page.getByTestId('environment-value-temperature')).toHaveValue('31')

  await node.click()
  await expect(node).toHaveClass(/device-node--expanded/)
  await expect(page.getByTestId('device-dialog')).toBeVisible()
  await expect(page.getByTestId('device-dialog')).toContainText('No state machine')
  await expect(page.getByTestId('device-dialog')).toContainText('Environment variable')
  await expect(page.getByTestId('device-dialog')).not.toContainText('Working, Off')
  await expect(page.getByTestId('device-instance-runtime')).toHaveCount(0)
  await expect(page.getByTestId('environment-value-temperature')).toHaveValue('31')
})

test('device info renders multi-mode API state tuples as readable mode changes', async ({ page, request }) => {
  const auth = await createAuthenticatedUser(request)

  const saveResponse = await request.post(`${apiBaseURL}/api/board/batch`, {
    headers: authHeaders(auth),
    data: { nodes: [{
      id: 'thermostat_tuple_api',
      templateName: 'Thermostat',
      label: 'Living Thermostat',
      position: { x: 960, y: 460 },
      state: 'auto;auto',
      width: 220,
      height: 180
    }] }
  })
  expect(saveResponse.ok(), await saveResponse.text()).toBeTruthy()

  await openWorkspace(page, auth)

  const node = page.locator('[data-node-id="thermostat_tuple_api"]')
  await expect(node).toBeVisible({ timeout: 30_000 })
  await node.click()

  const apiSection = page.getByTestId('device-dialog-apis')
  await expect(apiSection).toBeVisible()
  await expect(apiSection).toContainText('Any state')
  await expect(apiSection).toContainText('ThermostatFanMode: auto')
  await expect(apiSection).toContainText('ThermostatMode: cool')
  await expect(apiSection).not.toContainText('auto;')
  await expect(apiSection).not.toContainText(';cool')
})

test('environment pool keeps one shared value for multiple readers before simulation', async ({ page, request }) => {
  const auth = await createAuthenticatedUser(request)

  const saveResponse = await request.post(`${apiBaseURL}/api/board/batch`, {
    headers: authHeaders(auth),
    data: { nodes: [
      {
        id: 'temp_sensor_a',
        templateName: 'Temperature Sensor',
        label: 'Temp Sensor A',
        position: { x: 980, y: 300 },
        state: 'Working',
        width: 180,
        height: 150
      },
      {
        id: 'temp_sensor_b',
        templateName: 'Temperature Sensor',
        label: 'Temp Sensor B',
        position: { x: 1230, y: 300 },
        state: 'Working',
        width: 180,
        height: 150
      }
    ] }
  })
  expect(saveResponse.ok(), await saveResponse.text()).toBeTruthy()

  const environmentResponse = await request.post(`${apiBaseURL}/api/board/environment`, {
    headers: authHeaders(auth),
    data: [{ name: 'temperature', value: '28', trust: 'trusted', privacy: 'public' }]
  })
  expect(environmentResponse.ok(), await environmentResponse.text()).toBeTruthy()

  await openWorkspace(page, auth)

  const environmentPool = page.getByTestId('environment-pool')
  await expect(environmentPool).toBeVisible()
  await page.getByTestId('toggle-environment-pool').click()
  await environmentPool.locator('article').filter({ hasText: 'temperature' }).getByRole('button').first().click()
  await expect(environmentPool).not.toContainText('a_temperature')
  await expect(page.getByTestId('environment-value-temperature')).toHaveValue('28')
  await expect(environmentPool).not.toContainText('Conflicting values')

  await page.getByTestId('open-simulation-panel').click()
  await expect(page.getByTestId('simulation-panel')).toBeVisible()
  await page.getByTestId('run-simulation').click()
  await expect(page.getByTestId('simulation-timeline')).toBeVisible({ timeout: 60_000 })
})

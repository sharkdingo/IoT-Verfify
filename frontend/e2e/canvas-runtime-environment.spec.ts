import { type APIRequestContext, type Page } from '@playwright/test'
import {
  apiBaseURL,
  createAuthenticatedUser,
  expect,
  test,
  type AuthUser
} from './support/auth'

const authHeaders = (auth: AuthUser) => ({
  Authorization: `Bearer ${auth.token}`
})

const unwrap = async <T>(response: Awaited<ReturnType<APIRequestContext['get']>>): Promise<T> => {
  expect(response.ok(), await response.text()).toBeTruthy()
  const body = await response.json()
  expect(body.code, JSON.stringify(body)).toBe(200)
  return body.data as T
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

const addNodes = async (
  request: APIRequestContext,
  auth: AuthUser,
  devices: Record<string, unknown>[],
  environmentVariablePatches: Record<string, unknown>[] = []
) => unwrap(await request.post(`${apiBaseURL}/api/board/nodes`, {
  headers: authHeaders(auth),
  data: { devices, environmentVariablePatches }
}))

test('opening canvas node details preserves the viewport while inspector focus remains explicit', async ({ page, request }) => {
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
  const minimumNode = {
    id: 'minimum_sensor_1',
    templateName: 'Temperature Sensor',
    label: 'Minimum Sensor',
    position: { x: 760, y: 320 },
    state: 'Working',
    width: 80,
    height: 60
  }

  await addNodes(request, auth, [seedNode, minimumNode], [
    { name: 'temperature', value: '31', trust: 'trusted', privacy: 'public' }
  ])

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
  await expect(node.locator('.resize-handle')).toHaveCount(1)
  const zoomInput = page.getByTestId('canvas-map-zoom-input')
  await expect(zoomInput).toHaveValue('40')
  const initialCanvasTransform = await page.locator('.canvas-inner').evaluate(element =>
    getComputedStyle(element).transform
  )
  const minimumRenderedNode = page.locator('[data-node-id="minimum_sensor_1"]')
  await expect(minimumRenderedNode).toBeVisible()
  const lowZoomHitTarget = await minimumRenderedNode.evaluate(element => {
    const rect = element.getBoundingClientRect()
    const target = document.elementFromPoint(rect.left + rect.width / 2, rect.top + rect.height / 2)
    return {
      nodeId: target?.closest<HTMLElement>('[data-node-id]')?.dataset.nodeId || null,
      resizeHandleCount: element.querySelectorAll('.resize-handle').length
    }
  })
  expect(lowZoomHitTarget).toEqual({ nodeId: minimumNode.id, resizeHandleCount: 0 })

  await node.click({ button: 'right' })
  await expect(page.getByTestId('device-dialog')).toHaveCount(0)
  const contextMenu = page.locator('.board-context-menu')
  await expect(contextMenu).toBeVisible()
  await contextMenu.getByRole('menuitem', { name: 'View Details' }).click()
  await expect(page.locator('.board-context-menu')).toHaveCount(0)
  const contextDialog = page.getByTestId('device-dialog')
  await expect(contextDialog).toBeVisible()
  await expect(zoomInput).toHaveValue('40')
  await expect(node).toHaveClass(/device-node--compact/)
  await expect.poll(() => page.locator('.canvas-inner').evaluate(element =>
    getComputedStyle(element).transform
  )).toBe(initialCanvasTransform)
  await contextDialog.getByLabel('Close', { exact: true }).click()
  await expect(contextDialog).toHaveCount(0)

  const environmentPool = page.getByTestId('environment-pool')
  await expect(environmentPool).toBeVisible()
  await expect(environmentPool).toContainText('Temperature')
  await page.getByTestId('toggle-environment-pool').click()
  await environmentPool.locator('article').filter({ hasText: 'Temperature' }).getByRole('button').first().click()
  await expect(environmentPool).not.toContainText('a_temperature')
  await expect(page.getByTestId('environment-value-temperature')).toHaveValue('31')

  await node.click()
  await expect(page.getByTestId('device-dialog')).toBeVisible()
  await expect(zoomInput).toHaveValue('40')
  await expect(node).toHaveClass(/device-node--compact/)
  await expect.poll(() => page.locator('.canvas-inner').evaluate(element =>
    getComputedStyle(element).transform
  )).toBe(initialCanvasTransform)
  await expect(page.getByTestId('device-dialog')).toContainText('No state machine')
  await expect(page.getByTestId('device-dialog')).toContainText('Environment variable')
  await expect(page.getByTestId('device-dialog')).not.toContainText('Working, Off')
  await expect(page.getByTestId('device-instance-runtime')).toHaveCount(0)
  await expect(page.getByTestId('environment-value-temperature')).toHaveValue('31')
  await page.getByTestId('device-dialog').getByLabel('Close', { exact: true }).click()

  await expect.poll(async () => {
    const response = await request.get(`${apiBaseURL}/api/board/layout`, {
      headers: authHeaders(auth)
    })
    if (!response.ok()) return null
    const persistedLayout = await unwrap<{
      canvasPan: { x: number; y: number }
      canvasZoom: number
    }>(response)
    return {
      canvasZoom: persistedLayout.canvasZoom,
      canvasPan: persistedLayout.canvasPan
    }
  }).toEqual({ canvasZoom: 0.4, canvasPan: { x: 0, y: 0 } })

  const inspectorDevice = page.locator('[data-testid="system-inspector"] [data-device-id="temp_sensor_1"]')
  await inspectorDevice.getByRole('button', { name: 'Temp Sensor' }).click()
  await expect(zoomInput).toHaveValue('100')
  await expect(node).toHaveClass(/device-node--expanded/)
  await expect(node).toHaveClass(/node-focused/)
})

test('device info renders multi-mode API state tuples as readable mode changes', async ({ page, request }) => {
  const auth = await createAuthenticatedUser(request)

  await addNodes(request, auth, [{
      id: 'thermostat_tuple_api',
      templateName: 'Thermostat',
      label: 'Living Thermostat',
      position: { x: 960, y: 460 },
      state: 'auto;auto',
      width: 220,
      height: 180
    }])

  await openWorkspace(page, auth)

  const node = page.locator('[data-node-id="thermostat_tuple_api"]')
  await expect(node).toBeVisible({ timeout: 30_000 })
  await node.click()

  const apiSection = page.getByTestId('device-dialog-apis')
  await expect(apiSection).toBeVisible()
  await expect(apiSection).toContainText('Any state')
  await expect(apiSection).toContainText('Thermostat fan mode: Auto')
  await expect(apiSection).toContainText('Thermostat mode: Cool')
  await expect(apiSection).not.toContainText('auto;')
  await expect(apiSection).not.toContainText(';cool')
})

test('environment pool keeps one shared value for multiple readers before simulation', async ({ page, request }) => {
  const auth = await createAuthenticatedUser(request)

  await addNodes(request, auth, [
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
    ], [
      { name: 'temperature', value: '28', trust: 'trusted', privacy: 'public' }
    ])

  await openWorkspace(page, auth)

  const environmentPool = page.getByTestId('environment-pool')
  await expect(environmentPool).toBeVisible()
  await page.getByTestId('toggle-environment-pool').click()
  await environmentPool.locator('article').filter({ hasText: 'Temperature' }).getByRole('button').first().click()
  await expect(environmentPool).not.toContainText('a_temperature')
  await expect(page.getByTestId('environment-value-temperature')).toHaveValue('28')
  await expect(environmentPool).not.toContainText('Conflicting values')

  await page.getByTestId('open-simulation-panel').click()
  await expect(page.getByTestId('simulation-panel')).toBeVisible()
  await page.getByTestId('run-simulation').click()
  await expect(page.getByTestId('simulation-timeline')).toBeVisible({ timeout: 60_000 })
})

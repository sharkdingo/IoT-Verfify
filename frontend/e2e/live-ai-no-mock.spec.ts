import { randomUUID } from 'node:crypto'
import type { APIRequestContext } from '@playwright/test'
import {
  apiBaseURL,
  createAuthenticatedUser,
  expect,
  test
} from './support/auth'

const liveAiEnabled = process.env.RUN_LIVE_AI_E2E === '1'

const readBoardCollection = async (
  request: APIRequestContext,
  headers: Record<string, string>,
  path: 'nodes' | 'rules' | 'specs'
): Promise<unknown[]> => {
  const response = await request.get(`${apiBaseURL}/api/board/${path}`, { headers })
  expect(response.ok(), await response.text()).toBeTruthy()
  const body = await response.json()
  expect(body.code, JSON.stringify(body)).toBe(200)
  expect(Array.isArray(body.data), JSON.stringify(body)).toBeTruthy()
  return body.data
}

test.describe('live AI full-stack audit', () => {
  test.skip(!liveAiEnabled, 'Set RUN_LIVE_AI_E2E=1 to call the configured external model endpoint.')
  test.setTimeout(360_000)

  test('returns a validated scene recommendation and streams a tool-backed board answer', async ({ request }) => {
    const auth = await createAuthenticatedUser(request, { usernamePrefix: 'liveai' })
    const headers = { Authorization: `Bearer ${auth.token}` }

    const recommendationResponse = await request.post(
      `${apiBaseURL}/api/board/scenario/recommend?requestId=${randomUUID()}`,
      {
        headers,
        timeout: 240_000,
        data: {
          minDevices: 2,
          minRules: 1,
          minSpecs: 1,
          maxDevices: 3,
          maxRules: 2,
          maxSpecs: 2,
          language: 'en',
          userRequirement: 'Create a compact hallway safety scene with a motion sensor, a light, and one safety specification.'
        }
      }
    )
    expect(recommendationResponse.ok(), await recommendationResponse.text()).toBeTruthy()
    const recommendationBody = await recommendationResponse.json()
    expect(recommendationBody.code, JSON.stringify(recommendationBody)).toBe(200)
    expect(recommendationBody.data.scene).toMatchObject({
      schema: 'iot-verify.board-scene',
      version: 4
    })
    expect(Array.isArray(recommendationBody.data.scene.devices)).toBeTruthy()
    expect(Array.isArray(recommendationBody.data.scene.rules)).toBeTruthy()
    expect(Array.isArray(recommendationBody.data.scene.specs)).toBeTruthy()
    const sceneCounts = {
      devices: recommendationBody.data.scene.devices.length,
      rules: recommendationBody.data.scene.rules.length,
      specs: recommendationBody.data.scene.specs.length
    }
    expect(sceneCounts.devices + sceneCounts.rules + sceneCounts.specs).toBeGreaterThan(0)
    expect(recommendationBody.data.objectiveTargets).toEqual({
      minDevices: 2,
      minRules: 1,
      minSpecs: 1
    })
    expect(Array.isArray(recommendationBody.data.objectiveIssues)).toBeTruthy()
    const expectedObjectiveIssueCodes = [
      ...(sceneCounts.devices < 2
        ? [sceneCounts.devices === 0 ? 'NO_DEVICES' : 'INSUFFICIENT_DEVICES']
        : []),
      ...(sceneCounts.rules < 1 ? ['NO_AUTOMATION_RULES'] : []),
      ...(sceneCounts.specs < 1 ? ['NO_SPECIFICATIONS'] : [])
    ]
    expect(recommendationBody.data.objectiveStatus).toBe(
      expectedObjectiveIssueCodes.length === 0 ? 'COMPLETE' : 'PARTIAL'
    )
    expect(recommendationBody.data.objectiveIssues.map((issue: any) => issue.code)).toEqual(
      expectedObjectiveIssueCodes
    )
    expect(recommendationBody.data.rawCandidateCount).toBeGreaterThanOrEqual(
      recommendationBody.data.inspectedCount)

    const sessionResponse = await request.post(`${apiBaseURL}/api/chat/sessions`, {
      headers,
      data: null
    })
    expect(sessionResponse.ok(), await sessionResponse.text()).toBeTruthy()
    const sessionBody = await sessionResponse.json()
    const sessionId = sessionBody.data.id as string

    const turnId = randomUUID()
    const streamResponse = await request.post(`${apiBaseURL}/api/chat/completions`, {
      headers: {
        ...headers,
        Accept: 'text/event-stream',
        'Content-Type': 'application/json'
      },
      timeout: 240_000,
      data: {
        sessionId,
        turnId,
        content: 'Inspect my current board and report its device, rule, and specification counts. Do not change anything.'
      }
    })
    expect(streamResponse.ok(), await streamResponse.text()).toBeTruthy()
    expect(streamResponse.headers()['content-type']).toContain('text/event-stream')
    const streamText = await streamResponse.text()
    expect(streamText).toContain('CONTEXT_READY')
    expect(streamText).toContain('PLANNING')
    expect(streamText).toContain('TOOL_EXECUTION')
    expect(streamText).toContain('WRITING_RESPONSE')
    const streamFrames = streamText
      .split(/\r?\n/)
      .map(line => line.match(/^\s*data:\s*(.+)\s*$/)?.[1])
      .filter((data): data is string => Boolean(data))
      .map(data => JSON.parse(data))
    expect(streamFrames.some(frame =>
      frame.progress?.stage === 'PLANNING' &&
      Number.isSafeInteger(frame.progress?.round) &&
      frame.progress.round >= 1)).toBeTruthy()
    const boardResults = streamFrames.filter(frame =>
      frame.progress?.stage === 'TOOL_RESULT' &&
      frame.progress?.toolName === 'board_overview' &&
      frame.progress?.outcome === 'USABLE')
    expect(boardResults.length).toBeGreaterThanOrEqual(1)
    const terminalFrames = streamFrames.filter(frame => frame.terminal)
    expect(terminalFrames).toHaveLength(1)
    expect(terminalFrames[0].terminal).toEqual({
      turnId,
      executionStatus: 'COMPLETED'
    })
    expect(streamFrames.at(-1)).toEqual(terminalFrames[0])
    const assistantReply = streamFrames
      .map(frame => typeof frame.content === 'string' ? frame.content : '')
      .join('')
      .trim()
    expect(assistantReply).not.toBe('')

    const historyResponse = await request.get(
      `${apiBaseURL}/api/chat/sessions/${encodeURIComponent(sessionId)}/messages`,
      { headers }
    )
    expect(historyResponse.ok(), await historyResponse.text()).toBeTruthy()
    const historyBody = await historyResponse.json()
    expect(historyBody.code, JSON.stringify(historyBody)).toBe(200)
    expect(Array.isArray(historyBody.data?.messages), JSON.stringify(historyBody)).toBeTruthy()
    expect(historyBody.data.messages.some((message: any) =>
      message.role === 'user' && message.turnId === turnId)).toBeTruthy()
    const terminalHistory = historyBody.data.messages.find((message: any) =>
      message.role === 'assistant' && message.turnId === turnId)
    expect(terminalHistory).toMatchObject({ executionStatus: 'COMPLETED' })
    expect(String(terminalHistory.content || '').trim()).not.toBe('')
    expect(terminalHistory.executionTrace.some((progress: any) =>
      progress.stage === 'TOOL_RESULT' &&
      progress.toolName === 'board_overview' &&
      progress.outcome === 'USABLE')).toBeTruthy()

    expect(await readBoardCollection(request, headers, 'nodes')).toHaveLength(0)
    expect(await readBoardCollection(request, headers, 'rules')).toHaveLength(0)
    expect(await readBoardCollection(request, headers, 'specs')).toHaveLength(0)
  })
})

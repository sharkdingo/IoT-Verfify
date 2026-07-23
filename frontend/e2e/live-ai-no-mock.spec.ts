import { randomUUID } from 'node:crypto'
import {
  apiBaseURL,
  createAuthenticatedUser,
  expect,
  test
} from './support/auth'

const liveAiEnabled = process.env.RUN_LIVE_AI_E2E === '1'

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
    expect(['COMPLETE', 'PARTIAL']).toContain(recommendationBody.data.objectiveStatus)
    expect(Array.isArray(recommendationBody.data.objectiveIssues)).toBeTruthy()
    expect(recommendationBody.data.rawCandidateCount).toBeGreaterThanOrEqual(
      recommendationBody.data.inspectedCount)

    const sessionResponse = await request.post(`${apiBaseURL}/api/chat/sessions`, {
      headers,
      data: null
    })
    expect(sessionResponse.ok(), await sessionResponse.text()).toBeTruthy()
    const sessionBody = await sessionResponse.json()
    const sessionId = sessionBody.data.id as string

    const streamResponse = await request.post(`${apiBaseURL}/api/chat/completions`, {
      headers: {
        ...headers,
        Accept: 'text/event-stream',
        'Content-Type': 'application/json'
      },
      timeout: 240_000,
      data: {
        sessionId,
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
    expect(streamText).toContain('Devices')
    expect(streamText).toContain('Specifications')
    const streamFrames = streamText
      .split(/\r?\n/)
      .filter(line => line.startsWith('data:{'))
      .map(line => JSON.parse(line.slice('data:'.length)))
    expect(streamFrames.filter(frame =>
      frame.progress?.stage === 'PLANNING' && frame.progress?.round === 1)).toHaveLength(1)

    const historyResponse = await request.get(
      `${apiBaseURL}/api/chat/sessions/${encodeURIComponent(sessionId)}/messages`,
      { headers }
    )
    expect(historyResponse.ok(), await historyResponse.text()).toBeTruthy()
    const historyBody = await historyResponse.json()
    expect(historyBody.code, JSON.stringify(historyBody)).toBe(200)
    expect(Array.isArray(historyBody.data?.messages), JSON.stringify(historyBody)).toBeTruthy()
    expect(historyBody.data.messages.some((message: any) => message.role === 'user')).toBeTruthy()
    expect(historyBody.data.messages.some((message: any) =>
      message.role === 'assistant' && String(message.content || '').trim().length > 0)).toBeTruthy()
  })
})

import {
  apiBaseURL,
  createAuthenticatedUser,
  expect,
  test
} from './support/auth'

test('missing a required fix request id returns a structured client error', async ({ request }) => {
  const auth = await createAuthenticatedUser(request, { usernamePrefix: 'errorapi' })
  const response = await request.post(`${apiBaseURL}/api/verify/traces/1/fix`, {
    headers: { Authorization: `Bearer ${auth.token}` },
    data: { strategies: ['remove'] }
  })

  expect(response.status()).toBe(400)
  const body = await response.json()
  expect(body.code).toBe(400)
  expect(body.message).toContain('requestId')
})

test('logout and permanent account deletion reject unauthenticated requests', async ({ request }) => {
  const logoutResponse = await request.post(`${apiBaseURL}/api/auth/logout`)
  expect(logoutResponse.status()).toBe(401)
  expect((await logoutResponse.json()).code).toBe(401)

  const deleteResponse = await request.delete(`${apiBaseURL}/api/auth/account`, {
    data: { password: 'not-used', confirmation: 'not-used' }
  })
  expect(deleteResponse.status()).toBe(401)
  expect((await deleteResponse.json()).code).toBe(401)
})

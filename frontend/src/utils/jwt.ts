const decodeJwtPayload = (token: string): Record<string, unknown> | null => {
  const parts = token.split('.')
  if (parts.length !== 3) return null
  try {
    const base64 = parts[1].replace(/-/g, '+').replace(/_/g, '/')
    const padded = base64.padEnd(Math.ceil(base64.length / 4) * 4, '=')
    const payload = JSON.parse(atob(padded))
    return payload && typeof payload === 'object' ? payload : null
  } catch {
    return null
  }
}

/** Client-side UX precheck only; the backend remains the authentication authority. */
export const isLocallyUsableJwt = (token: string | null): token is string => {
  if (!token) return false
  const payload = decodeJwtPayload(token)
  const expiresAt = payload?.exp
  return typeof expiresAt === 'number' && Number.isFinite(expiresAt)
    && expiresAt * 1000 > Date.now()
}

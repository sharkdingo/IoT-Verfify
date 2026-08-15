import type { AxiosResponse } from 'axios'

/**
 * Save a blob response as a file, using the filename the server chose.
 *
 * One owner because the SMV-model endpoints already had two byte-identical copies of this
 * (`api/board.ts` and `api/simulation.ts`), and adding a third for the run-keyed download would have
 * made the divergence harder to see than the duplication. The `Content-Disposition` parsing in
 * particular is worth having in one place: the backend briefly emitted an RFC 2047 encoded-word in
 * the legacy `filename` parameter, and a parser that trusts it would save the encoded string as the
 * name.
 */
export const saveBlobResponseAsFile = (response: AxiosResponse<Blob>, fallbackFilename: string): void => {
  const filename = filenameFromContentDisposition(response.headers?.['content-disposition'])
    ?? fallbackFilename

  const url = URL.createObjectURL(new Blob([response.data], { type: 'text/plain;charset=utf-8' }))
  const linkElement = document.createElement('a')
  linkElement.href = url
  linkElement.download = filename
  document.body.appendChild(linkElement)
  linkElement.click()
  document.body.removeChild(linkElement)
  URL.revokeObjectURL(url)
}

/**
 * The filename from a `Content-Disposition` header, or null when it carries none usable.
 *
 * Prefers RFC 5987 `filename*` over the legacy `filename`, because only `filename*` states its
 * encoding — the legacy parameter is where a server may put an RFC 2047 encoded-word, which is not a
 * filename and must not become one.
 */
export const filenameFromContentDisposition = (header?: string): string | null => {
  if (!header) return null

  const extended = /filename\*\s*=\s*([^']*)'([^']*)'([^;\n]*)/i.exec(header)
  if (extended?.[3]) {
    try {
      return decodeURIComponent(extended[3].trim())
    } catch {
      // A malformed percent-escape is not a filename; fall through to the legacy parameter.
    }
  }

  const legacy = /filename\s*=\s*("([^"]*)"|[^;\n]*)/i.exec(header)
  const raw = (legacy?.[2] ?? legacy?.[1])?.trim()
  if (!raw) return null
  // An encoded-word is a transport artifact, not a name the user should see on disk.
  if (/^=\?.*\?=$/.test(raw)) return null
  return raw
}

import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * Choosing an import file must invalidate the preview before the file is read, not after.
 *
 * `setImportTextImmediately` closes the 300ms debounce window for a file selection, but it can only run
 * once `await file.text()` resolves — and reading a file is asynchronous. In that gap the preview, the
 * parsed counts and the create button all still describe the PREVIOUS content, and the button is still
 * enabled from it, so a click there imports the payload the user just replaced.
 *
 * Measured from the CI artifact for `board-full-flow.spec.ts` "imports devices from pasted JSON and
 * selected CSV with precise preview validation", which failed on two consecutive nightly runs: at failure
 * the textarea was rendering its own placeholder (so its text was empty) while the create button read
 * "Create 2 device(s)" and was enabled, and the board had gained `import_phone_1` and `import_alarm_1` —
 * the JSON payload imported a second time — with neither CSV device present. Both payloads contain two
 * devices, so neither `toBeEnabled()` nor the button label could distinguish them. It reproduces in CI,
 * where a slower filesystem widens the gap, and not locally.
 *
 * Source-text assertions rather than a mounted component: what matters is the ORDER of two statements
 * around an await, which a render cannot observe without stubbing `File.text` to control the timing — and
 * a stub is precisely the thing whose timing the bug depends on.
 *
 * Comments are stripped before anything is located. The handler's own comment quotes `await file.text()`
 * while explaining the race, which is earlier in the file than the statement being pinned — so a search
 * over the raw text reads the prose as the code and reports the fix missing when it is present.
 */
describe('device import file selection race', () => {
  const source = readFileSync(join(process.cwd(), 'src/components/ControlCenter.vue'), 'utf8')

  const handler = (() => {
    const at = source.indexOf('const handleDeviceImportFile')
    expect(at, 'the file handler should exist').toBeGreaterThan(-1)
    const end = source.indexOf('\n}', at)
    expect(end, 'the handler should be a block').toBeGreaterThan(at)
    return source
      .slice(at, end + 2)
      .replace(/\/\*[\s\S]*?\*\//g, '')
      .replace(/\/\/[^\n]*/g, '')
  })()

  it('clears the stale preview before the first await', () => {
    const clearAt = handler.indexOf("setImportTextImmediately('')")
    expect(clearAt, 'the handler must invalidate the previous preview').toBeGreaterThan(-1)

    const firstAwait = handler.indexOf('await ')
    expect(firstAwait, 'the handler should await the file read').toBeGreaterThan(-1)

    expect(clearAt).toBeLessThan(firstAwait)
  })

  it('still installs the file contents in one tick once read', () => {
    // The original fix must survive: the contents replace text and parsed view together, so the
    // debounce cannot leave the button describing content the user has already replaced.
    expect(handler, 'the file contents go in immediately, not through the debounce')
      .toMatch(/setImportTextImmediately\(await file\.text\(\)\)/)
  })
})

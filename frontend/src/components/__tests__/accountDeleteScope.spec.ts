import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * The deletion warning must name everything the cascade actually removes.
 *
 * `AuthServiceImpl.deleteUserOwnedData` deletes from 14 repositories. Verified against the database: an account
 * with rows in `device_templates` (45), `board_edit_journal` (2), `board_environment_variable`, `chat_session`,
 * `device_node` and `specification` had **zero** owned rows afterwards, with zero join-orphans in
 * `chat_message`, `ai_session_state`, `chat_session_pre_admission_stop` and `trace`.
 *
 * The dialog's inventory listed seven of those and omitted three: **counterexamples** (`trace`,
 * `simulation_trace`, `fuzz_finding`), the **Environment Pool** (`board_environment_variable`) and the **undo
 * history** (`board_edit_journal`). All three vision reviews of the dialog noticed counterexamples were missing.
 * For a verification tool they are the hardest-won artefact on the list, and a consent screen that under-states
 * what it destroys is not consent.
 *
 * This check exists because the drift is silent in both directions: adding a repository to the cascade breaks no
 * test, and neither does dropping an item from the copy.
 */

const i18n = () => readFileSync(join(__dirname, '../../assets/i18n.ts'), 'utf8')

const warningFor = (locale: 'en' | 'zh') => {
  const source = i18n()
  const matches = [...source.matchAll(/deleteAccountDataWarning:\s*'([^']+)'/g)].map(m => m[1])
  expect(matches.length, 'both locales should declare the warning').toBe(2)
  // The zh block is declared first in this file.
  return locale === 'zh' ? matches[0] : matches[1]
}

describe('account deletion scope', () => {
  it('names every category the cascade removes, in English', () => {
    const text = warningFor('en').toLowerCase()
    for (const category of [
      'device',            // device_node
      'environment pool',  // board_environment_variable
      'rule',              // rules
      'specification',     // specification
      'template',          // device_templates
      'edit history',      // board_edit_journal — before/after snapshots of board content
      'counterexample',    // trace / simulation_trace / fuzz_finding
      'ai conversation'    // chat_session / chat_message / ai_session_state
    ]) {
      expect(text, `the warning should name "${category}"`).toContain(category)
    }
  })

  it('names every category the cascade removes, in Chinese', () => {
    const text = warningFor('zh')
    for (const category of ['画布设备', '环境变量池', '规则', '规约', '模板', '编辑历史', '反例', 'AI 会话']) {
      expect(text, `警告文案应包含「${category}」`).toContain(category)
    }
  })

  it('says the loss cannot be recovered, not only that it is permanent', () => {
    expect(warningFor('en').toLowerCase()).toContain('cannot be recovered')
    expect(warningFor('zh')).toContain('无法恢复')
  })

  it('keeps the destructive control disarmed and looking disarmed', () => {
    const dialog = readFileSync(join(__dirname, '../AccountDeleteDialog.vue'), 'utf8')

    // Disabled until both the identifier and the password are supplied.
    expect(dialog).toContain(':disabled="!canConfirm"')

    // And visibly so. `opacity: 0.58` alone left the button saturated red with its glow intact, and all three
    // reviews read it as enabled while measurement showed `disabled: true` — the control was right and its
    // appearance was not, which on an irreversible action is the worse failure.
    const disabledRule = dialog.slice(dialog.indexOf('.account-delete-confirm:disabled'))
    expect(disabledRule.slice(0, disabledRule.indexOf('}'))).toContain('box-shadow: none')

    // Desaturated to a neutral, not tinted toward the danger hue and not faded. Both of the treatments this
    // replaced were measured illegible: `opacity: 0.58` over a saturated red still read as armed, and mixing
    // danger 34% into the white surface produced a pink wash under white ink.
    const sheet = readFileSync(join(__dirname, '../../styles/dialog.css'), 'utf8')
    const shared = sheet.slice(sheet.indexOf('.iot-dialog-btn--danger:disabled'))
    expect(shared.slice(0, shared.indexOf('}'))).toContain('var(--accent-fill-disabled)')
  })

  it('keeps the flow addressable, since it is the one irreversible action', () => {
    const dialog = readFileSync(join(__dirname, '../AccountDeleteDialog.vue'), 'utf8')
    const logout = readFileSync(join(__dirname, '../LogoutConfirmDialog.vue'), 'utf8')

    // None of these existed, so nothing outside the component could reach the flow: a browser check looking for
    // it found no route and reported the affordance missing.
    expect(logout).toContain('data-testid="open-account-delete"')
    for (const id of [
      'account-delete-dialog',
      'account-delete-confirmation',
      'account-delete-password',
      'account-delete-confirm',
      'account-delete-cancel'
    ]) {
      expect(dialog, `${id} should be addressable`).toContain(`data-testid="${id}"`)
    }
  })
})

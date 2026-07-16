# Contributing

Guidelines for working on IoT-Verify. The overriding rule for documentation: **code is
the source of truth, and docs must not drift from it.**

---

## Documentation discipline

Documentation lives under `docs/`, indexed by the Doc Map ([docs/README.md](docs/README.md)).
Before editing docs, read the Doc Map's **Ownership rules** — each fact has exactly one
home:

1. **Endpoints** — index only in [docs/api/rest-endpoints.md](docs/api/rest-endpoints.md)
   (method, path, controller, link; no field detail).
2. **Endpoint detail** — field-level DTO contracts in one domain doc
   (`docs/api/auth.md`, `board.md`, `verification.md`, `fuzzing.md`, `chat-sse.md`).
3. **Configuration** — env vars/defaults only in
   [docs/getting-started/configuration.md](docs/getting-started/configuration.md).
4. **Global API conventions** — `Result<T>`, auth, error codes only in
   [docs/api/overview.md](docs/api/overview.md); elsewhere a one-line pointer, never a
   restatement.
5. **Change history** — dated entries only in [CHANGELOG.md](CHANGELOG.md).

If the same fact appears in two docs, one is wrong by construction: delete the copy and
link to the owner.

### Doc-sync checklist (PR requirement)

A change that touches any of the following **must** update the owning doc in the same
PR:

| If your change touches… | Update… |
| :--- | :--- |
| A controller endpoint (add/remove/rename/re-path) | `docs/api/rest-endpoints.md` + the domain doc |
| A request/response DTO field | the owning `docs/api/*.md` |
| A config key or default (`application.yaml`) | `docs/getting-started/configuration.md` |
| The `Result<T>` envelope, auth, or error mapping | `docs/api/overview.md` |
| A spec template, CTL/LTL formula, or P1–P5 rule | `docs/architecture/spec-templates.md` |
| NuSMV generation / identifier handling | `docs/architecture/nusmv-model.md` |
| A fix strategy | `docs/architecture/auto-fix.md` |
| An AI tool (add/remove/rename) | `docs/api/ai-tools.md` |
| Any externally visible behavior change | `CHANGELOG.md` (`Unreleased`, dated entry) |

Include this line in the PR description and tick it:
`[ ] Docs updated for endpoints/config/DTOs/spec-templates/AI-tools, or N/A.`

### Recommended CI gates

- Keep the real-backend Playwright journey green. The full-stack smoke gate runs
  `frontend/e2e/fuzzing-flow.spec.ts` against MySQL, Redis, and NuSMV; run the complete
  `npm run test:e2e` suite locally for broader interaction and authority-model changes.
- Regenerate the endpoint index from controller annotations and fail if it differs from
  `docs/api/rest-endpoints.md` (see the "Regeneration" note in that file).
- Run a Markdown dead-link check across `docs/` and the root docs.

---

## Language policy

- **All documentation is written in English** — `README.md`, everything under `docs/`,
  `CHANGELOG.md`, and this file. This avoids the historical split (mixed Chinese/English
  docs).
- Binary/archive showcase assets under `docs/assets/` may keep their original titles
  and source language for provenance. Markdown documentation that describes or links to
  those assets remains English.
- Code identifiers, comments, and commit messages follow the existing conventions of
  the file/module you are editing.
- If a Chinese-language showcase README is ever needed (e.g. for competition display),
  add it as a separate `README.zh-CN.md`; do not switch the primary docs to Chinese.

---

## Change history (CHANGELOG)

Until a formal release/tagging process exists, record changes under `[Unreleased]` with
a dated (`YYYY-MM-DD`) sub-heading and the standard Keep a Changelog groups (`Added`,
`Changed`, `Fixed`, `Removed`). When the first tag is cut, move the relevant entries
under a version heading.

---

## Git & PR conventions

- Never commit unless explicitly asked; keep unrelated changes out of a commit.
- Flag any file that may contain secrets (`.env`, credentials) before committing.
- Keep PR titles concise; put detail (summary, testing, blocked items) in the body.

---

## Repository hygiene

- **Encoding and line endings** are governed by `.editorconfig` and `.gitattributes`,
  not by each developer's local editor or git config. Tracked text files must be
  UTF-8 without BOM and LF; images, fonts, archives, and office docs
  (`.pdf`/`.docx`) are `binary`. Do not hand-edit line endings, add BOMs, or add
  per-file `eol` overrides — extend the repo-wide policy instead.
- **Ignored vs tracked**: real env files (`.env`) and generated output (`node_modules/`,
  `target/`, `dist/`, `nusmv_*/` verification artifacts, `.codex-review/`,
  `.claude/settings.local.json`) are gitignored. Committed counterparts: `*.env.example`
  templates, `package-lock.json`, and shared editor config (`.vscode/extensions.json`).
  Never commit secrets; if a new secret-bearing file type appears, add it to
  `.gitignore` in the same change.
- **Binary assets** live under `docs/assets/` (e.g. proposal `.docx`/`.pdf`), classified
  `binary` in `.gitattributes` so they are neither diffed nor line-ending-normalized.
- **Spelling**: `cspell.json` at the repo root holds the project dictionary (NuSMV,
  CTLSPEC, Volcengine, camelCase field names, etc.) and ignores code spans, fenced code
  blocks, and Markdown link targets. Add genuinely new domain terms there rather than
  disabling the checker.

---

## Verification before submitting

- Backend: `cd backend && mvn clean install` (or at least compile + relevant tests).
- Frontend: `cd frontend && npm run build` (runs `vue-tsc` type-check) and
  `npm run test:unit` where applicable.
- If you cannot run a step (environment constraints), say so in the PR.

# CLAUDE.md — IoT-Verify (repo root)

Repo-wide working manual for Claude Code. This file holds **cross-cutting rules and a
map**; stack-specific detail lives in the nearest sub-directory file, which Claude
merges automatically:

- Backend work → also read [backend/CLAUDE.md](backend/CLAUDE.md)
- Frontend work → also read [frontend/CLAUDE.md](frontend/CLAUDE.md)
- Reference docs (authoritative) → [docs/README.md](docs/README.md) (the Doc Map)

Keep this file short and rule-focused. It is a constitution, not documentation — do not
paste reference material here that already lives in `docs/`.

## What this repo is

A formal-verification platform for smart-home IoT systems. Users build a device
topology on a visual canvas, define automation rules and safety specifications, and the
NuSMV model checker verifies them — with counterexample analysis and automatic fix
suggestions. Includes an AI assistant (any OpenAI-compatible LLM endpoint, SSE streaming).

## Monorepo map

```
backend/    Spring Boot API + NuSMV orchestration + AI tools   → backend/CLAUDE.md
frontend/   Vue 3 + TypeScript + Vite SPA                       → frontend/CLAUDE.md
docs/       Single source of truth for all reference docs       → docs/README.md
CHANGELOG.md      dated change log (Unreleased + dates)
CONTRIBUTING.md   contribution + doc-sync rules (authoritative)
```

## The prime rule: code is truth, docs stay in sync

**When code and docs disagree, code wins — and you fix the doc in the same change.**
This repo just finished eliminating code/doc drift; do not reintroduce it.

If a change touches any of the following, update the owning doc **in the same change**
(this is enforced in [CONTRIBUTING.md](CONTRIBUTING.md); documentation is never an
"afterwards" task):

| You changed… | Update… |
| :--- | :--- |
| A controller endpoint (add/remove/rename/re-path) | `docs/api/rest-endpoints.md` + the domain doc |
| A request/response DTO field | the owning `docs/api/*.md` |
| A config key or default (`application.yaml` / `.env`) | `docs/getting-started/configuration.md` |
| The `Result<T>` envelope, auth, or error mapping | `docs/api/overview.md` |
| A spec template, CTL/LTL formula, or P1–P5 rule | `docs/architecture/spec-templates.md` |
| NuSMV generation / identifier handling | `docs/architecture/nusmv-model.md` |
| A fix strategy | `docs/architecture/auto-fix.md` |
| An AI tool (add/remove/rename) | `docs/api/ai-tools.md` |
| Any externally visible behavior | `CHANGELOG.md` (`Unreleased`, dated entry) |

Documentation ownership (avoid duplication — one fact, one home): endpoints live only
in `rest-endpoints.md` (index) + one domain doc; config defaults live only in
`configuration.md`; the `Result<T>` envelope/auth/error codes live only in
`api/overview.md`. Elsewhere, link — do not restate. If you find the same fact in two
docs, one is wrong: delete the copy and link to the owner.

## Shared conventions

- **Language**: all documentation is written in **English** (README, `docs/`,
  CHANGELOG, CONTRIBUTING, both sub-CLAUDE.md). Code identifiers follow each file's
  existing style. Chat replies to the user may be in the user's language.
- **Encoding**: all tracked text files are **UTF-8 without BOM** and use LF line
  endings. Keep `.editorconfig` and `.gitattributes` aligned; when writing repo files
  from PowerShell, prefer PowerShell 7 (`pwsh`) and avoid Windows PowerShell 5.1
  `-Encoding utf8`, which can add a BOM.
- **Frontend↔backend contract**: field names are camelCase on both sides
  (e.g. `userId`, not `user_id`). All REST responses use the `Result<T>` envelope
  except SSE. Keep TypeScript types in `frontend/src/types/` aligned with the backend
  DTOs; document field changes in the owning `docs/api/*.md`.
- **Docs discipline**: no dead links, no stale "(planned)" markers for files that now
  exist, uniform "Verified against code on <date>" notes. Prefer relative Markdown
  links between docs.
- **Match surrounding style**: read neighboring code before writing; mirror its
  conventions, libraries, and comment density rather than introducing new ones.

## Verify before you finish

Run the relevant build/tests and report results honestly (if a step fails or is
skipped, say so):

```bash
# backend
cd backend && mvn compile        # or: mvn test
# frontend
cd frontend && npm run build     # runs vue-tsc type-check + build
```

Do not commit unless explicitly asked. Push feature work to a branch, never directly to
`main`. Flag any file that may contain secrets (`.env`, credentials) before committing.
Full git/PR conventions: [CONTRIBUTING.md](CONTRIBUTING.md).

## Safety / gotchas that bite across the stack

- **`ProductionSafetyCheck`** refuses to start the backend under a `prod`/`production`
  profile if `JWT_SECRET` / `DB_PASSWORD` / `OPENAI_API_KEY` hold unsafe defaults.
- **Redis is fail-open**: logout token-revocation degrades silently if Redis is down —
  never make request flow hard-depend on it.
- **NuSMV 2.6–2.7 only** (not nuXmv); the trace parser depends on its English output
  format.
- **`saveRules` is an incremental upsert**, not full-replace (unlike nodes/edges/specs)
  — send existing `id`s back; details in [docs/api/board.md](docs/api/board.md).

## Open decisions (do not resolve silently)

- **LICENSE**: no license file exists; the authorization stance is unconfirmed. Do not
  add a LICENSE or assert a license until the user decides.

Note: there is no separate `AGENTS.md`; the three CLAUDE.md files (this root file plus
`backend/CLAUDE.md` and `frontend/CLAUDE.md`) are the coding-AI-agent guidance.

# AGENTS.md — IoT-Verify (repo root)

Repo-wide working manual for Codex. This file holds **cross-cutting rules and a
map**; stack-specific detail lives in the `CLAUDE.md` files:

- Backend work → also read [backend/CLAUDE.md](backend/CLAUDE.md)
- Frontend work → also read [frontend/CLAUDE.md](frontend/CLAUDE.md)
- Reference docs (authoritative) → [docs/README.md](docs/README.md) (the Doc Map)

Keep this file short and rule-focused. It is a constitution, not documentation — do not
paste reference material here that already lives in `docs/`.

## What this repo is

A verification platform for smart-home IoT systems. Users build a device topology on a
visual canvas, define automation rules and safety specifications, run bounded candidate
counterexample exploration, and use NuSMV for formal conclusions — with formal
counterexample analysis and automatic fix suggestions. Includes an AI assistant (any
OpenAI-compatible LLM endpoint, SSE streaming).

## Monorepo map

```
backend/    Spring Boot API + fuzz/NuSMV orchestration + AI tools → backend/CLAUDE.md
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

## Product-first development stage

This project is still in active development. Do **not** preserve a flawed legacy design
only for compatibility with an old implementation. When documentation, interfaces,
business logic, frontend interaction, or modeling semantics do not match the user's
mental model, the project goals, or sound human-computer interaction principles, you may
boldly adjust code, docs, type definitions, tests, and examples. Keep every change
evidence-based, scoped, and verifiable. The primary goal is the user's need and mental
model.

There is no released compatibility contract yet. Unless the user explicitly requires a
migration path, do not add backward-compatibility readers, dual-write formats, rolling-
deployment bridges, deprecated aliases, or silent fallbacks for old development data.
Change all in-repo callers and tests together, version persisted formats when useful, and
reject obsolete or malformed state explicitly. Compatibility code must answer a current,
documented requirement rather than a hypothetical future one.

## No AI slop

AI assistance does not lower the engineering bar. In this repository, "AI slop" means
plausible-looking output that has not been understood, integrated, or verified and that
pushes hidden review, repair, security, or maintenance cost onto the next contributor.
Judge the work by its evidence and maintainability, not by whether a human or model typed it.

- Every changed line must trace to a real requirement, reproduced defect, or necessary
  contract. Delete speculative features, placeholder branches, dead compatibility layers,
  and abstractions that do not remove demonstrated complexity.
- Read the owning code and tests before editing. Reuse established domain boundaries and
  helpers; do not clone logic, invent parallel sources of truth, or hide uncertainty behind
  generic wrappers and broad fallbacks.
- Never turn an unknown or failed outcome into apparent success. Reject malformed boundary
  data, preserve typed error semantics, and make partial, stale, cancelled, or unverified
  states explicit to both callers and users.
- Tests must exercise observable behavior, failure paths, races, and boundary cases. Do not
  weaken assertions to make generated code pass, mirror the implementation without testing
  its contract, or replace a failing integration check with a mock-only claim.
- Comments explain non-obvious invariants and tradeoffs. Remove narration, prompt-like prose,
  copied summaries, and confident claims that the code or cited evidence does not support.
- Before handing off, review the complete diff as a maintainer: account for every dependency,
  public field, helper, catch block, and documentation claim; remove unnecessary volume; run
  the proportional checks; and report anything not verified.

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

Do not commit unless explicitly asked. Flag any file that may contain secrets (`.env`,
credentials) before committing.
Full git/PR conventions: [CONTRIBUTING.md](CONTRIBUTING.md).

## Safety / gotchas that bite across the stack

- **`ProductionSafetyCheck`** refuses to start the backend under a `prod`/`production`
  profile if `JWT_SECRET` / `DB_PASSWORD` / `IOT_VERIFY_OPENAI_API_KEY` hold unsafe defaults.
- **Redis is fail-open**: logout token-revocation degrades silently if Redis is down —
  never make request flow hard-depend on it.
- **NuSMV 2.6–2.7 only** (not nuXmv); the trace parser depends on its English output
  format.
- **Ordinary board mutations are targeted**: add/update/delete only the intended
  device/rule/spec and reconcile from the returned current snapshot. `/api/board/batch`
  is the explicit full-scene replacement command and requires user confirmation in the UI.
  Details in [docs/api/board.md](docs/api/board.md).

## Open decisions (do not resolve silently)

- **LICENSE**: no license file exists; the authorization stance is unconfirmed. Do not
  add a LICENSE or assert a license until the user decides.

Note: there are no `backend/AGENTS.md` or `frontend/AGENTS.md` files. This root
`AGENTS.md` mirrors the cross-cutting Codex rules; stack-specific coding-AI guidance
lives in `backend/CLAUDE.md` and `frontend/CLAUDE.md`.

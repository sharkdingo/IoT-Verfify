# IoT-Verify Documentation

Documentation hub for IoT-Verify, a formal-verification platform for smart-home IoT
systems. This page is the **Doc Map**: it tells you which document owns which topic,
whether that document exists yet, and — for documents not yet written — where the
source material currently lives.

> **Language policy**: all documentation is written in **English** — this resolved the
> earlier split (root README in Chinese, backend README in English, NuSMV doc in
> Chinese). Archived binary showcase assets under `docs/assets/` may retain their
> original titles/language for provenance; Markdown around them remains English. The
> policy is enforced in [CONTRIBUTING.md](../CONTRIBUTING.md).

> **Source of truth**: where documentation and code disagree, **code wins**. Each
> document names the code paths it is derived from so it can be re-verified.

---

## Doc Map

Legend — **Status**: ✅ ready (migrated, code-verified) · 🚧 planned (not yet written;
see Source) · ⚠️ pending (blocked on a decision).

### Root-level

| Document | Status | Owns | Source (if not ready) |
| :--- | :--- | :--- | :--- |
| [README.md](../README.md) | ✅ ready | Project pitch, feature highlights, 5-minute quick start, links into `docs/` | — |
| [CHANGELOG.md](../CHANGELOG.md) | ✅ ready | Change history (`Unreleased` + dated entries until a release process exists) | — |
| [CONTRIBUTING.md](../CONTRIBUTING.md) | ✅ ready | Branch/commit conventions, **doc-sync discipline**, language policy | — |
| `LICENSE` | ⚠️ pending | License text | **Blocked on decision**: no LICENSE file exists. The root README previously described the project as a Nanjing University Challenge Cup entry and `backend/README.md` said "MIT License"; the conflicting MIT claim has been removed pending a confirmed authorization stance. Add a LICENSE file only once that stance is decided. |

### Getting started

| Document | Status | Owns | Source (if not ready) |
| :--- | :--- | :--- | :--- |
| [docs/getting-started/installation.md](getting-started/installation.md) | ✅ ready | Full prerequisites & install (JDK/Node/MySQL/Redis/NuSMV) | — |
| [docs/getting-started/configuration.md](getting-started/configuration.md) | ✅ ready | **SSOT** for every environment variable and default value | — |
| [docs/getting-started/deployment.md](getting-started/deployment.md) | ✅ ready | Production packaging, Nginx, profiles, `ProductionSafetyCheck` | — |

### Architecture

| Document | Status | Owns | Source (if not ready) |
| :--- | :--- | :--- | :--- |
| [docs/architecture/overview.md](architecture/overview.md) | ✅ ready | System topology, front/back boundary, package layout | — |
| [docs/architecture/device-identity.md](architecture/device-identity.md) | ✅ ready | Canonical device identity, display-label boundaries, NuSMV `varName` normalization | — |
| [docs/architecture/data-authority-model.md](architecture/data-authority-model.md) | ✅ ready | Field-level data ownership for devices, environment pool, rules, specs, traces, tasks, and fix | — |
| [docs/architecture/verification-flow.md](architecture/verification-flow.md) | ✅ ready | SmvGenerator → NusmvExecutor → SmvTraceParser pipeline | — |
| [docs/architecture/fuzzing-flow.md](architecture/fuzzing-flow.md) | ✅ ready | HAFuzz-inspired bounded exploration role, pipeline, supported finite semantics, and proof boundary | — |
| [docs/architecture/nusmv-model.md](architecture/nusmv-model.md) | ✅ ready | SMV modeling logic, identifier sanitization, user-input → model mapping | — |
| [docs/architecture/spec-templates.md](architecture/spec-templates.md) | ✅ ready | 7 spec templates ↔ CTL/LTL, `templateId` mapping, P1–P5 | — |
| [docs/architecture/auto-fix.md](architecture/auto-fix.md) | ✅ ready | Fault localization + parameter/condition/permanent-removal strategies + forward verification | — |

### API

| Document | Status | Owns | Source (if not ready) |
| :--- | :--- | :--- | :--- |
| [docs/api/overview.md](api/overview.md) | ✅ ready | `Result<T>` envelope, auth convention, error codes | — |
| [docs/api/rest-endpoints.md](api/rest-endpoints.md) | ✅ ready | **Index only**: method, path, controller, one-line note, link to domain doc | — |
| [docs/api/auth.md](api/auth.md) | ✅ ready | Auth DTO-level contract | — |
| [docs/api/board.md](api/board.md) | ✅ ready | Board/rules/specs/templates/recommend contracts | — |
| [docs/api/verification.md](api/verification.md) | ✅ ready | Verify/simulate/task/trace/fix DTO-level contract | — |
| [docs/api/fuzzing.md](api/fuzzing.md) | ✅ ready | Counterexample-exploration task/run/finding DTO-level contract | — |
| [docs/api/chat-sse.md](api/chat-sse.md) | ✅ ready | SSE streaming protocol for chat | — |
| [docs/api/ai-tools.md](api/ai-tools.md) | ✅ ready | The 33 AI tools: names, categories, argument semantics | — |

### Guides

| Document | Status | Owns | Source (if not ready) |
| :--- | :--- | :--- | :--- |
| [docs/guides/frontend-integration.md](guides/frontend-integration.md) | ✅ ready | How the frontend calls the backend (axios/SSE, real `boardApi`/`authApi` shape, type locations) | — |
| [docs/guides/acceptance-demo.md](guides/acceptance-demo.md) | ✅ ready | End-to-end acceptance scene: three construction paths, simulation/verification animation, attack/privacy contrast, and verified repair | — |
| [docs/guides/default-template-scenarios.md](guides/default-template-scenarios.md) | ✅ ready | Three additional importable default-template scenes covering fire response, rule priority, RFID trust/privacy, attack contrast, and verified repair | — |
| [docs/guides/troubleshooting.md](guides/troubleshooting.md) | ✅ ready | FAQ (MySQL/Redis/CORS/NuSMV/timeout) | — |

### Module READMEs & Claude manuals

| Document | Status | Notes |
| :--- | :--- | :--- |
| [backend/README.md](../backend/README.md) | ✅ ready | Slimmed to local-run + package layout + links into `docs/` |
| [frontend/README.md](../frontend/README.md) | ✅ ready | Slimmed to local-run + source layout + links into `docs/` |
| [CLAUDE.md](../CLAUDE.md) (root), [backend/CLAUDE.md](../backend/CLAUDE.md), [frontend/CLAUDE.md](../frontend/CLAUDE.md), [AGENTS.md](../AGENTS.md) | ✅ ready | Claude/Codex working manuals. `CLAUDE.md` owns the stack-specific coding-AI guidance (cross-cutting rules at root, per-stack detail in each); root `AGENTS.md` mirrors the cross-cutting Codex rules and points to the CLAUDE stack manuals. There are no backend/frontend `AGENTS.md` files. |

Removed legacy docs (content fully migrated into the set above, so the files were
deleted rather than kept as stubs):

- `backend/NuSMV_Module_Documentation.md` → `docs/architecture/*`, `docs/api/verification.md`, `CHANGELOG.md`
- `frontend/API-DOCUMENTATION.md` → `docs/guides/frontend-integration.md`
- `frontend/FRONTEND_FIX_GUIDE.md` → all 12 items now resolved in code (F-11, the
  `http.ts` base URL, was the last — both axios and chat SSE now read
  `VITE_API_BASE_URL`).

## Assets

- `docs/assets/智链未来企划书.docx` — project proposal (binary; see `.gitattributes`).
- `docs/assets/智护安居.pdf` — project document (binary; see `.gitattributes`).

These are archived binary/showcase materials. They are tracked for project provenance,
not as primary Markdown documentation, so their original filenames and source language
are intentionally preserved.

---

## Ownership rules (how duplication is prevented)

1. **Endpoints**: `docs/api/rest-endpoints.md` is the only place that lists the full
   set of endpoints, and it carries **index data only** (method, path, controller,
   link). It does **not** contain DTO fields or request/response examples.
2. **Endpoint detail**: field-level DTO contracts, examples, validation and error
   semantics live in exactly one domain doc (`auth.md` / `board.md` /
   `verification.md` / `fuzzing.md` / `chat-sse.md`). A field has one home.
3. **Configuration**: `docs/getting-started/configuration.md` is the only place that
   lists environment variables and their default values. Every other document links
   to it instead of copying values.
4. **Global API conventions**: `docs/api/overview.md` is the only authoritative home
   for the `Result<T>` envelope, the auth convention (`Authorization: Bearer`), and
   error codes. Other API docs may include a **one-line pointer** ("responses use the
   `Result<T>` envelope — see overview.md") but must not restate the field-level
   definition.
5. **Change history**: `CHANGELOG.md` is the only place for dated change entries.
   Technical specs describe the *current* state, not the history.
6. **Audit/review notes**: do not add dated audit reports under `docs/architecture/`.
   Durable findings must be folded into the current owner document above; dated
   summaries belong in `CHANGELOG.md`.

If you find the same fact in two documents, one of them is wrong by construction —
delete the copy and link to the owner.

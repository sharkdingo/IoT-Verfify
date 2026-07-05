# IoT-Verify Documentation

Documentation hub for IoT-Verify, a formal-verification platform for smart-home IoT
systems. This page is the **Doc Map**: it tells you which document owns which topic,
whether that document exists yet, and — for documents not yet written — where the
source material currently lives.

> **Language policy**: all documentation is written in **English** — this resolved the
> earlier split (root README in Chinese, backend README in English, NuSMV doc in
> Chinese). The policy is enforced in [CONTRIBUTING.md](../CONTRIBUTING.md).

> **Source of truth**: where documentation and code disagree, **code wins**. Each
> document names the code paths it is derived from so it can be re-verified.

---

## Doc Map

Legend — **Status**: ✅ ready (migrated, code-verified) · 🚧 planned (not yet written;
see Source) · ⚠️ pending (blocked on a decision).

### Root-level

| Document | Status | Owns | Source (if not ready) |
| :--- | :--- | :--- | :--- |
| `README.md` | ✅ ready | Project pitch, feature highlights, 5-minute quick start, links into `docs/` | — |
| `CHANGELOG.md` | ✅ ready | Change history (`Unreleased` + dated entries until a release process exists) | — |
| `CONTRIBUTING.md` | ✅ ready | Branch/commit conventions, **doc-sync discipline**, language policy | — |
| `LICENSE` | ⚠️ pending | License text | **Blocked on decision**: no LICENSE file exists. The root README previously described the project as a Nanjing University Challenge Cup entry and `backend/README.md` said "MIT License"; the conflicting MIT claim has been removed pending a confirmed authorization stance. Add a LICENSE file only once that stance is decided. |

### Getting started

| Document | Status | Owns | Source (if not ready) |
| :--- | :--- | :--- | :--- |
| `docs/getting-started/installation.md` | ✅ ready | Full prerequisites & install (JDK/Node/MySQL/Redis/NuSMV) | — |
| `docs/getting-started/configuration.md` | ✅ ready | **SSOT** for every environment variable and default value | — |
| `docs/getting-started/deployment.md` | ✅ ready | Production packaging, Nginx, profiles, `ProductionSafetyCheck` | — |

### Architecture

| Document | Status | Owns | Source (if not ready) |
| :--- | :--- | :--- | :--- |
| `docs/architecture/overview.md` | ✅ ready | System topology, front/back boundary, package layout | — |
| `docs/architecture/verification-flow.md` | ✅ ready | SmvGenerator → NusmvExecutor → SmvTraceParser pipeline | — |
| `docs/architecture/nusmv-model.md` | ✅ ready | SMV modeling logic, identifier sanitization, user-input → model mapping | — |
| `docs/architecture/spec-templates.md` | ✅ ready | 7 spec templates ↔ CTL/LTL, `templateId` mapping, P1–P5 | — |
| `docs/architecture/auto-fix.md` | ✅ ready | Fault localization + parameter/condition/disable strategies + forward verification | — |

### API

| Document | Status | Owns | Source (if not ready) |
| :--- | :--- | :--- | :--- |
| `docs/api/overview.md` | ✅ ready | `Result<T>` envelope, auth convention, error codes | — |
| `docs/api/rest-endpoints.md` | ✅ ready | **Index only**: method, path, controller, one-line note, link to domain doc | — |
| `docs/api/auth.md` | ✅ ready | Auth DTO-level contract | — |
| `docs/api/board.md` | ✅ ready | Board/rules/specs/templates/recommend contracts | — |
| `docs/api/verification.md` | ✅ ready | Verify/simulate/task/trace/fix DTO-level contract | — |
| `docs/api/chat-sse.md` | ✅ ready | SSE streaming protocol for chat | — |
| `docs/api/ai-tools.md` | ✅ ready | The 30 AI tools: names, categories, argument semantics | — |

### Guides

| Document | Status | Owns | Source (if not ready) |
| :--- | :--- | :--- | :--- |
| `docs/guides/frontend-integration.md` | ✅ ready | How the frontend calls the backend (axios/SSE, real `boardApi`/`authApi` shape, type locations) | — |
| `docs/guides/troubleshooting.md` | ✅ ready | FAQ (MySQL/Redis/CORS/NuSMV/timeout) | — |

### Module READMEs & Claude manuals

| Document | Status | Notes |
| :--- | :--- | :--- |
| `backend/README.md` | ✅ ready | Slimmed to local-run + package layout + links into `docs/` |
| `frontend/README.md` | ✅ ready | Slimmed to local-run + source layout + links into `docs/` |
| `CLAUDE.md` (root), `backend/CLAUDE.md`, `frontend/CLAUDE.md` | ✅ ready | Claude Code working manuals — also serve as the coding-AI-agent guidance (cross-cutting rules at root, per-stack detail in each). A separate `AGENTS.md` is **not** used; the CLAUDE.md set fills that role. |

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

---

## Ownership rules (how duplication is prevented)

1. **Endpoints**: `docs/api/rest-endpoints.md` is the only place that lists the full
   set of endpoints, and it carries **index data only** (method, path, controller,
   link). It does **not** contain DTO fields or request/response examples.
2. **Endpoint detail**: field-level DTO contracts, examples, validation and error
   semantics live in exactly one domain doc (`auth.md` / `board.md` /
   `verification.md` / `chat-sse.md`). A field has one home.
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

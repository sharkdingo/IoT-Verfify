# IoT-Verify Documentation

Documentation hub for IoT-Verify, a formal-verification platform for smart-home IoT
systems. This page is the **Doc Map**: it tells you which document owns which topic, so a
fact has exactly one home and every other mention links to it.

Verified against the repository on 2026-08-12: every `docs/**/*.md` file appears in the map below
exactly once, and every entry points at a file that exists. Source: the repository layout and the
owning documents linked below. Each document carries its own "verified against code" date — this
line covers the map, not their contents.

> **Language policy**: all documentation is written in **English** — this resolved the
> earlier split (root README in Chinese, backend README in English, NuSMV doc in
> Chinese). Archived binary showcase assets under `docs/assets/` may retain their
> original titles/language for provenance; Markdown around them remains English. The
> policy is enforced in [CONTRIBUTING.md](../CONTRIBUTING.md).

> **Source of truth**: where documentation and code disagree, **code wins**. Each
> document names the code paths it is derived from, and carries a dated "verified against code" line
> so it can be re-verified. The two `development/` documents are the deliberate exception: they
> describe process and diagnosed incidents rather than current code state, so there is nothing for
> such a line to point at.

---

## Doc Map

Legend — **Status**: ✅ ready (code-verified) · ⚠️ pending (blocked on a decision). Every document
below is ✅ except the `LICENSE` row, which is blocked on an authorization decision.

### Root-level

| Document | Status | Owns |
| :--- | :--- | :--- |
| [README.md](../README.md) | ✅ ready | Project pitch, feature highlights, 5-minute quick start, links into `docs/` |
| [CHANGELOG.md](../CHANGELOG.md) | ✅ ready | Change history (`Unreleased` + dated entries until a release process exists) |
| [CONTRIBUTING.md](../CONTRIBUTING.md) | ✅ ready | Branch/commit conventions, **doc-sync discipline**, language policy |
| `LICENSE` | ⚠️ pending | License text. **Blocked on decision**: no LICENSE file exists. `backend/README.md` once claimed "MIT License" while the root README described a Nanjing University Challenge Cup entry; the conflicting MIT claim has been removed pending a confirmed authorization stance. Add a LICENSE only once that stance is decided. |

### Getting started

| Document | Status | Owns |
| :--- | :--- | :--- |
| [docs/getting-started/installation.md](getting-started/installation.md) | ✅ ready | Full prerequisites & install (JDK/Node/MySQL/Redis/NuSMV) |
| [docs/getting-started/configuration.md](getting-started/configuration.md) | ✅ ready | **SSOT** for every environment variable and default value |
| [docs/getting-started/deployment.md](getting-started/deployment.md) | ✅ ready | Production packaging, Nginx, profiles, `ProductionSafetyCheck` |

### Architecture

| Document | Status | Owns |
| :--- | :--- | :--- |
| [docs/architecture/overview.md](architecture/overview.md) | ✅ ready | System topology, front/back boundary, package layout |
| [docs/architecture/device-identity.md](architecture/device-identity.md) | ✅ ready | Canonical device identity, display-label boundaries, NuSMV `varName` normalization |
| [docs/architecture/data-authority-model.md](architecture/data-authority-model.md) | ✅ ready | Field-level data ownership for devices, environment pool, rules, specs, traces, tasks, and fix |
| [docs/architecture/verification-flow.md](architecture/verification-flow.md) | ✅ ready | SmvGenerator → NusmvExecutor → SmvTraceParser pipeline |
| [docs/architecture/fuzzing-flow.md](architecture/fuzzing-flow.md) | ✅ ready | HAFuzz-inspired bounded exploration role, pipeline, supported finite semantics, and proof boundary |
| [docs/architecture/nusmv-model.md](architecture/nusmv-model.md) | ✅ ready | SMV modeling logic, identifier sanitization, user-input → model mapping |
| [docs/architecture/spec-templates.md](architecture/spec-templates.md) | ✅ ready | 7 spec templates ↔ CTL/LTL, `templateId` mapping, P1–P5 |
| [docs/architecture/auto-fix.md](architecture/auto-fix.md) | ✅ ready | Fault localization + parameter/condition/permanent-removal strategies + forward verification |
| [docs/architecture/shared-value-semantics.md](architecture/shared-value-semantics.md) | ✅ ready | The single authoritative semantics for shared environment values: identity, domain, read/affect capability, natural evolution, device effects, composition, conflicts, which rules are exact versus deliberately abstract, and how a stored run stays explainable |
| [docs/architecture/theory-sources.md](architecture/theory-sources.md) | ✅ ready | Which published algorithm owns which modeling/fix/exploration behaviour, with section citations |

### Development

Working on the codebase rather than understanding it: how CI is structured, and the environment
failures that waste time when nobody has written them down.

| Document | Status | Owns |
| :--- | :--- | :--- |
| [docs/development/ci.md](development/ci.md) | ✅ ready | The two-tier CI design: what Fast CI and Full CI each cover, which changes count as high risk and why, caching keys, and the live-AI gate |
| [docs/development/known-traps.md](development/known-traps.md) | ✅ ready | Archive of diagnosed failures that mimic product or compile bugs, grouped by cause: test authoring (tests that cannot fail), build environment (Maven, `target/classes`, stale dev JVM), E2E environment (rate limits, ports, CORS, known-flaky specs), and blast-radius misjudgements |

### API

| Document | Status | Owns |
| :--- | :--- | :--- |
| [docs/api/overview.md](api/overview.md) | ✅ ready | `Result<T>` envelope, auth convention, error codes |
| [docs/api/rest-endpoints.md](api/rest-endpoints.md) | ✅ ready | **Index only**: method, path, controller, one-line note, link to domain doc |
| [docs/api/auth.md](api/auth.md) | ✅ ready | Auth DTO-level contract |
| [docs/api/board.md](api/board.md) | ✅ ready | Board/rules/specs/templates/recommend contracts |
| [docs/api/verification.md](api/verification.md) | ✅ ready | Verify/simulate/task/trace/fix DTO-level contract |
| [docs/api/fuzzing.md](api/fuzzing.md) | ✅ ready | Counterexample-exploration task/run/finding DTO-level contract |
| [docs/api/chat-sse.md](api/chat-sse.md) | ✅ ready | SSE streaming protocol for chat |
| [docs/api/ai-tools.md](api/ai-tools.md) | ✅ ready | The 53 AI tools: names, categories, argument semantics |

### Guides

Two kinds of document share this directory, and they answer different questions.

**Conventions and integration** — binding rules and how-it-works, read while writing code:

| Document | Status | Owns |
| :--- | :--- | :--- |
| [docs/guides/frontend-integration.md](guides/frontend-integration.md) | ✅ ready | How the frontend calls the backend (axios/SSE, real `boardApi`/`authApi` shape, type locations) |
| [docs/guides/frontend-ui-conventions.md](guides/frontend-ui-conventions.md) | ✅ ready | Decision records for the board UI: URL surface, feedback mechanisms, undo's boundaries, dialog sizes and tones, action emphasis, the ink/paper colour split, type scale, depth, CSS precedence and replay — each with the measurement that settled it |
| [docs/guides/troubleshooting.md](guides/troubleshooting.md) | ✅ ready | FAQ (MySQL/Redis/CORS/NuSMV/timeout) |

**Scenes and walkthroughs** — scripted runs of the product, for acceptance and demonstration:

| Document | Status | Owns |
| :--- | :--- | :--- |
| [docs/guides/acceptance-demo.md](guides/acceptance-demo.md) | ✅ ready | End-to-end acceptance scene: three construction paths, simulation/verification animation, attack/privacy contrast, and verified repair |
| [docs/guides/default-template-scenarios.md](guides/default-template-scenarios.md) | ✅ ready | **Scene semantics SSOT** for the additional importable default-template scenes (fire response, rule priority, RFID trust/privacy, away-mode unlock, attack contrast, verified repair), including each scene's expected verification counts |
| [docs/guides/away-mode-unlock-demo.md](guides/away-mode-unlock-demo.md) | ✅ ready | Presenter walkthrough for the away-mode unlock scene: composition defect, three-state counterexample, two strategies declining with stated reasons, verified removal, optional budget-one attack act, and on-stage failure modes |

### Module READMEs & Claude manuals

| Document | Status | Notes |
| :--- | :--- | :--- |
| [backend/README.md](../backend/README.md) | ✅ ready | Slimmed to local-run + package layout + links into `docs/` |
| [frontend/README.md](../frontend/README.md) | ✅ ready | Slimmed to local-run + source layout + links into `docs/` |
| [CLAUDE.md](../CLAUDE.md) (root), [backend/CLAUDE.md](../backend/CLAUDE.md), [frontend/CLAUDE.md](../frontend/CLAUDE.md), [AGENTS.md](../AGENTS.md) | ✅ ready | Claude/Codex working manuals. `CLAUDE.md` owns the stack-specific coding-AI guidance (cross-cutting rules at root, per-stack detail in each); root `AGENTS.md` mirrors the cross-cutting Codex rules and points to the CLAUDE stack manuals. There are no backend/frontend `AGENTS.md` files. |

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
5. **Shared environment values**: `docs/architecture/shared-value-semantics.md` is the
   only authoritative home for what a shared value *means* — identity, domain,
   read/affect capability, natural evolution, composition and conflicts.
   `nusmv-model.md` owns how that becomes SMV text; `data-authority-model.md` owns who
   may write each field. Neither restates the semantics.
6. **Published algorithms**: `docs/architecture/theory-sources.md` is the only place
   that maps a behaviour to the paper and section it came from. Domain docs state the
   behaviour and cite the source doc.
7. **AI tools**: `docs/api/ai-tools.md` is the only place that enumerates the tools and
   their argument semantics.
8. **Scene semantics**: for the additional default-template scenes,
   `docs/guides/default-template-scenarios.md` owns each scene's semantics and expected
   verification counts. A presenter walkthrough references those numbers; it does not
   redefine them.
9. **Change history**: `CHANGELOG.md` is the only place for dated change entries.
   Technical specs describe the *current* state, not the history.
10. **Audit/review notes**: do not add dated audit reports under `docs/architecture/`.
    Durable findings must be folded into the current owner document above; dated
    summaries belong in `CHANGELOG.md`.

If you find the same fact in two documents, one of them is wrong by construction —
delete the copy and link to the owner.

---

## Six of these documents are checked by the backend test suite

Editing them can turn `mvn test` red, which is the point: these are the claims the repo refuses to let
drift. Run the owning test after editing, not just the linter.

| Document | Test | What it enforces |
| :--- | :--- | :--- |
| [api/verification.md](api/verification.md) | `ModelSnapshotDocumentationTest` | Every field of the run-snapshot and provenance DTOs appears in the field tables — a new DTO field fails until documented |
| [api/ai-tools.md](api/ai-tools.md), [architecture/overview.md](architecture/overview.md) | `AiToolCatalogDocumentationTest` | The stated tool count matches the concrete `*Tool` classes (also checked in the root and module READMEs and `backend/CLAUDE.md`) |
| [architecture/theory-sources.md](architecture/theory-sources.md) | `TheorySourceConformanceTest` | The documented paper-derived semantics match what the code implements |
| [architecture/shared-value-semantics.md](architecture/shared-value-semantics.md) | `EnvironmentProvenanceCollectorTest` | Provenance behaviour matches the documented semantics |
| [guides/away-mode-unlock-demo.md](guides/away-mode-unlock-demo.md) | `AwayModeUnlockSceneNusmvTest` | The walkthrough's counterexample claims hold under a real NuSMV run |
| [api/auth.md](api/auth.md) | `AccountDeletionCoverageTest` | The documented account-deletion coverage matches the code |

`backend/CLAUDE.md` is pinned the same way by `SchemaDocumentationTruthTest` (table count, table
names, composite keys). A doc test should pin *facts*, never phrasing — if one blocks a legitimate
rewrite, loosen the test rather than contorting the prose, and verify by mutation that it still
catches the defect it exists for.

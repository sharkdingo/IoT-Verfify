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
.claude/    Hooks that enforce rules mechanically rather than by instruction
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
| Any modeling/fix/exploration semantics from a paper | `docs/architecture/theory-sources.md` (cite the section) |
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

AI assistance does not lower the engineering bar. "AI slop" means plausible-looking output that
has not been understood, integrated, or verified, and that pushes hidden review, repair, security,
or maintenance cost onto the next contributor. Judge work by its evidence, not by who typed it.

**The traceability check:** every modified line must map back to something that was asked for — a
requirement, a reproduced defect, or a necessary contract. If it does not, delete it.

- **Read before writing.** Find the owning code, its tests, and the existing helper or domain
  boundary that already covers this. Reuse it rather than cloning logic or inventing a second
  source of truth.
- **Nothing speculative.** No unrequested features, no abstraction for single-use code, no
  configurability nobody asked for, no handling for impossible cases. A new abstraction must
  remove demonstrated duplication or enforce a named invariant — pass-through layers and one-call
  wrappers need a stated reason.
- **Surgical scope.** No drive-by edits to nearby code, comments, or formatting. Delete only the
  orphans your own change created; mention pre-existing dead code instead of removing it unasked.
  Match the surrounding style even where you would write it differently.
- **Root causes, not symptoms.** Never suppress an error, bypass a validation, or add a
  special-case branch to make a check pass. Never loosen a lint or type config to go green.
- **Never turn an unknown or failed outcome into apparent success.** Reject malformed boundary
  data, preserve typed error semantics, and make partial, stale, cancelled, or unverified states
  explicit to callers and users.
- **Comments carry the "why".** Non-obvious invariants and tradeoffs, not narration, prompt-like
  prose, or claims the code does not support.
- **Before handing off**, read the complete diff as the maintainer who inherits it: account for
  every dependency, public field, helper, and catch block; remove volume; report what you did not
  verify. New production dependencies need explicit justification.

## Autonomy: act, confirm, or refuse

Match caution to reversibility instead of asking about everything or nothing.

**Act without asking** — typo and comment fixes, adding types with no logic change,
behavior-preserving refactors, tests for under-covered code, docs that follow a change you made,
and any decision where the alternatives are equivalent (naming, formatting, default values).

**Confirm first** — changing business logic or a persisted format, adding a production dependency,
altering an API contract or DB schema, removing a feature or a user-visible behavior, and any
scope change beyond what was asked.

**Do not do without an explicit request** — commit or push, push to `main`, touch env vars or
production config, run production migrations, or delete files wholesale (prefer narrowing the
change and saying what you left).

When genuinely blocked, state the assumption you are proceeding under rather than stopping; when
proceeding either way would be unsafe or wasted, ask one specific question.

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

## Review the source first, then verify

**A green suite is evidence, not a conclusion.** Tests only check what someone thought to check, so
reading the code you changed is the primary review and the suite is the backstop. Before handing
off, read your own complete diff and ask of each change: what breaks if this is wrong, which caller
depends on it, and which state does it now own?

Three failure modes that a passing suite hides, all of which have actually happened here:

- **Correct by accident.** The state was right only because some unrelated refresh happened to
  repair it. Fix: trace the mechanism, do not accept the outcome.
- **A test that cannot fail.** Before trusting a new test, break the code it covers and confirm it
  goes red. A test that passes with the fix reverted proves nothing — and has twice revealed that
  the "bug" being fixed did not exist. One session shipped **five** of these at once, in four
  recurring shapes worth recognising by sight:
  - **The empty scan.** A loop over a selector, directory, or field list that matches nothing. Zero
    iterations assert nothing and report success. Fix: assert the scan found something *before*
    looping (`expect(rules.length).toBeGreaterThan(0)`).
  - **The wrong slice.** A source-text assertion whose window excludes the place the defect lives —
    slicing `<div` up to a `data-testid` examines only whitespace, so a `v-show` after the testid is
    invisible. Fix: print the slice once and read it.
  - **The unfalsifiable claim.** Asserting something the framework can never produce
    (`doesNotContain("isSourceModelComplete")` — Jackson never emits a getter name as a key), or the
    absence of a symbol that no longer exists anywhere. Prefer a positive assertion about the value
    you want.
  - **The unreached path.** A fixture that never enters the branch the test names — a single rule
    cannot produce a rule *conflict*, so the helper under test is never called. Fix: check the
    mutation reddens *this* test, not merely some test.
  A guard scoped to a subset also lies: one written to catch locale-dependent case folds scanned six
  hand-picked packages and missed the highest-stakes fold in the product, in the boot-time check that
  refuses to start with default secrets.
- **Verifying stale artifacts.** A rebuilt backend, a cached bundle, or a reused dev server can make
  the run describe code you are not editing.

When a check fails, find the root cause. "Flaky" is a conclusion that needs evidence — a different
test failing each run points at the environment, the same assertion failing points at the code.

### Scale the check to the change — do not re-run everything per edit

Verification is staged. Running the full suite (or worse, E2E) after every small edit burns minutes
and tokens for information the narrow check already gave you, and it trains you to skim results
instead of reading them.

| Stage | When | What to run |
| :--- | :--- | :--- |
| 1. Narrow | After each edit | The owning spec file(s) plus the mutation check on the behaviour you changed |
| 2. Type | Once per coherent slice of work | `vue-tsc --noEmit` (frontend) / `mvn compile` (backend) |
| 3. Suite | Once a slice is complete, before reporting it done | `npm run test:unit` / `mvn test` — delegate |
| 4. E2E | Once per session-level milestone, or when touching routing, auth, deep links, cross-tab sync, or a real backend contract | `npm run test:e2e` — delegate, never inline |

Rules that follow from this:

- **Stage 1 is where the signal is.** A focused spec run is seconds; use it freely. The mutation
  check (break it, see red, restore) belongs here too — it is per-behaviour, not per-suite.
- **Never run stage 3 or 4 to "see if anything broke" after an isolated edit.** Reason about the
  blast radius instead: if the edit cannot reach a surface, its tests cannot tell you anything new.
- **Batch stages 3 and 4.** Several fixes in one area share one suite run. Finish the area first.
- **E2E is the most expensive check in the repo (minutes, needs MySQL + backend).** It earns its
  cost on integration contracts, not on component-local logic a unit test already pins.
- **Changing a REST request or response shape *is* the E2E trigger, however green the other stages
  are.** Narrowing the verify/simulate contract to run parameters passed 2148 backend and 1040
  frontend tests plus a live-backend probe, and still broke three E2E specs — they audited scene
  semantics by reading the request body, which is a contract only a browser-driven run observes.
  Reasoning about blast radius works for logic; it does not substitute for E2E on a wire format.
- Re-running a suite that just passed, with nothing changed in between, is never verification.

### Delegate long runs to background subagents

Full test suites, E2E, and live-AI runs take minutes and must not occupy the main thread. Launch
them as background subagents with a read-only, single-purpose brief ("run X, report failures with
root cause, modify nothing"), keep reviewing source in the foreground, and relay results when they
land. Never predict or assume a pending agent's outcome.

The commands themselves live with the stack that owns them — [backend/CLAUDE.md](backend/CLAUDE.md) and
[frontend/CLAUDE.md](frontend/CLAUDE.md) — where their prerequisites and traps are documented alongside
them. Restating them here created a second place to keep in sync for no benefit.

Report results honestly: if a step failed, say so with the output; if you skipped one, say that.

**Two E2E environment facts, both learned from real false results:**

- **A reused server tests stale code and reports green.** E2E deliberately refuses to adopt an existing
  server, and a `PreToolUse` hook (`.claude/hooks/guard-e2e-port.sh`) enforces that rather than trusting
  anyone to remember it. The port, the proxy and the escape hatch are frontend mechanics:
  [frontend/CLAUDE.md](frontend/CLAUDE.md).
- **A stale JVM is the backend's version of that stale dev server, and nothing guards it.** A
  `spring-boot:run` process started before your last edit serves the old classes, so a fix looks
  ineffective and an already-fixed defect looks live. This cost five wrong hypotheses in one session.
  Start the dev backend with its output redirected (`> backend/run.log 2>&1`, already gitignored) so
  the next unexplained failure begins with a stack trace.
  **A `mvn clean` while that JVM is alive makes it worse than stale.** The dev JVM keeps loading classes
  lazily from `target/classes`, so wiping and rebuilding underneath it leaves it serving a mix of two
  builds. After any `mvn clean` in a checkout with a live `spring-boot:run`, restart that backend before
  believing anything it says; a live probe against it is otherwise measuring neither tree. It can also hold a
  lock that fails the `clean` outright (`Failed to delete …/target`, zero tests run, succeeds on a single
  retry) — intermittently, so one clean run does not disprove it. Do not confuse that with the *other*
  contender for `target/classes`, the VS Code `redhat.java` language server, whose symptoms are mass
  `NoClassDefFoundError` rather than a failed delete: [backend/CLAUDE.md](backend/CLAUDE.md).
  **Compare the process start time against the modified `.java` sources, not against
  `target/classes`.** A full `mvn compile` rewrites *every* class file, so class timestamps are all
  identical and always newer than the JVM — comparing against them reports a stale JVM whenever
  anything was compiled, which is a false alarm every time. It produced one here: the classes read
  28 minutes newer than the process, while the only source edited after startup was a set of
  `static final` constants whose values matched the literals they replaced, and a live probe
  confirmed current behaviour. `git status` names the changed sources; their mtimes are the ones that
  matter.

**`git checkout -- <file>` and `git restore <file>` are destructive here.** They discard every uncommitted
change in that file, and in a working session that is all of it. This is not theoretical: undoing a
two-character test mutation that way erased a raw-hue migration, a scroll-region migration, a type-floor pass
and a session of colour-role work from one component, and `git fsck` could not help because nothing had been
staged. To undo a temporary edit, copy the file first and restore from the copy. The danger is that this
command reads as "revert my last thing" while meaning "revert everything since the last commit".

Do not commit or push unless explicitly asked. Direct pushes to `main` are allowed when the user
explicitly requests them, but only after reviewing the complete change set, running the
proportional gates, and checking for secret-bearing files. After the push, follow the CI runs to
completion and address failures before handing off.
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

## Maintaining these files

This rule set is a living document, not an append-only log. It only works while it keeps changing
behavior, so treat it like code:

- **A rule earns its place by changing a decision.** Prefer a concrete failure mode with its cause
  ("X was silently reused, so the suite went green against stale code") over an adjective ("be
  careful with servers").
- **Prefer enforcement over instruction.** If a rule is mechanically checkable, make it a test, a
  type, or a hook in `.claude/` and keep only a one-line pointer here. If the agent already does
  something correctly without being told, delete the instruction — every unread line makes the
  rules that matter harder to find.
- **Prune when you add.** Merge overlapping rules, delete guidance the code now enforces, and delete
  anything describing structure that no longer exists. A rule nobody reads protects nothing.
- **Detail lives in `docs/`, not here.** These files are an index of cross-cutting constraints; link
  rather than restate.
- **Stale is worse than missing.** When code and this file disagree, code wins — fix the file in the
  same change.

Layout: this root file plus `backend/CLAUDE.md` and `frontend/CLAUDE.md` hold stack-specific
guidance. The root `AGENTS.md` is a Codex mirror of *this* file — keep its body identical, differing
only in the header/footer, and do not add backend/frontend AGENTS files.

Each rule above carries its own rationale inline, which is where the "why" belongs — a separate change log
of this file duplicated those reasons and `git log -p CLAUDE.md` already holds the history. Product and
behaviour changes go in [CHANGELOG.md](CHANGELOG.md); that is its job, not this file's.

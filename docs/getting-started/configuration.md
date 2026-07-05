# Configuration Reference

**Single source of truth** for every runtime configuration option. Any other document
that needs to mention a config key or default value must link here rather than copy
the value.

Backend options are read from `backend/src/main/resources/application.yaml` using the
`${ENV_VAR:default}` pattern, so every value can be overridden by an environment
variable without editing the file. Frontend options are Vite build-time variables (see
the [Frontend](#frontend-vite) section at the end).

Verified against code on 2026-07-05. Source:
`backend/src/main/resources/application.yaml`, `configure/ProductionSafetyCheck`,
`frontend/src/api/`, `frontend/.env.example`.

---

## Database (MySQL)

| Env var | Default | Notes |
| :--- | :--- | :--- |
| `DB_URL` | `jdbc:mysql://localhost:3306/iot_verify?useSSL=false&serverTimezone=Asia/Shanghai&characterEncoding=utf-8&allowPublicKeyRetrieval=true` | JDBC connection string |
| `DB_USERNAME` | `root` | Database user |
| `DB_PASSWORD` | `sharkdingo123` | Database password. **Unsafe default — must be overridden in production** (enforced by `ProductionSafetyCheck`). |
| `JPA_SHOW_SQL` | `false` | Log SQL statements |

`spring.jpa.hibernate.ddl-auto` is fixed to `update` (tables auto-created on first
start); dialect is `MySQL8Dialect`.

## Server

| Env var | Default | Notes |
| :--- | :--- | :--- |
| `SERVER_PORT` | `8080` | Backend HTTP port |

`server.error.include-message` and `include-binding-errors` are fixed to `never` to
prevent the Spring `/error` endpoint from leaking internal exception detail.

## Authentication (JWT)

| Env var | Default | Notes |
| :--- | :--- | :--- |
| `JWT_SECRET` | `iot-verify-secret-key-must-be-at-least-256-bits-long-for-hs256` | HS256 signing key (≥256 bits). **Unsafe default — must be overridden in production.** |
| `JWT_EXPIRATION` | `86400000` | Token lifetime in ms (24h) |

## Redis

Redis backs the JWT-token blacklist (logout revocation) and runs in **fail-open** mode:
if Redis is unavailable the app still starts, but logout revocation degrades.

| Env var | Default | Notes |
| :--- | :--- | :--- |
| `REDIS_HOST` | `localhost` | |
| `REDIS_PORT` | `6379` | |
| `REDIS_PASSWORD` | *(empty)* | |
| `REDIS_DATABASE` | `0` | Database index |

Fixed pool settings: `timeout 3000ms`, `max-active 16`, `max-idle 8`, `min-idle 2`,
`max-wait 2000ms`.

## CORS

| Env var | Default | Notes |
| :--- | :--- | :--- |
| `CORS_ORIGINS` | `http://localhost:3000,http://127.0.0.1:3000,http://localhost:3001,http://127.0.0.1:3001,http://localhost:5173,http://127.0.0.1:5173,http://localhost:5174,http://127.0.0.1:5174,http://localhost:5175,http://127.0.0.1:5175,http://localhost:5176,http://127.0.0.1:5176` | Comma-separated allowed origins. The defaults cover the primary Vite dev port and common fallback ports for local development; set a tighter value in deployed environments. |

## LLM (AI)

Any OpenAI-compatible endpoint — the official OpenAI API, a self-hosted gateway, or a
relay. Point `OPENAI_BASE_URL` at the endpoint and supply the matching key.

| Env var | Default | Notes |
| :--- | :--- | :--- |
| `OPENAI_API_KEY` | `your_api_key_here` | API key for the endpoint. **Placeholder default — must be overridden in production.** |
| `OPENAI_MODEL` | `gpt-4o` | Model id / deployment name sent to the endpoint |
| `OPENAI_BASE_URL` | `https://api.openai.com/v1` | OpenAI-compatible base URL (official API or relay) |
| `LLM_PROVIDER` | `openai` | Provider implementation selector (currently only `openai`) |
| `LLM_TIMEOUT_MINUTES` | `5` | AI request timeout (minutes) |

## Chat Streaming

| Env var | Default | Notes |
| :--- | :--- | :--- |
| `CHAT_SSE_TIMEOUT_MS` | `600000` | SSE emitter timeout for `/api/chat/completions`; keep it higher than `LLM_TIMEOUT_MINUTES` so provider errors can be sent as SSE frames. |

## NuSMV

| Env var | Default | Notes |
| :--- | :--- | :--- |
| `NUSMV_PATH` | `D:/NuSMV/NuSMV-2.7.1-win64/NuSMV-2.7.1-win64/bin/NuSMV.exe` | Path to the NuSMV executable. Requires NuSMV 2.6–2.7 (**not** nuXmv). |
| `NUSMV_PREFIX` | *(empty)* | Command prefix, e.g. `wine` when running a Windows NuSMV build on Linux |
| `NUSMV_TIMEOUT_MS` | `120000` | Per-verification timeout (ms) |
| `NUSMV_MAX_CONCURRENT` | `6` | Max concurrent NuSMV processes (semaphore) |
| `NUSMV_ACQUIRE_PERMIT_TIMEOUT_MS` | `10000` | Timeout to acquire a concurrency permit (ms) |

## Auto-fix

| Env var | Default | Notes |
| :--- | :--- | :--- |
| `FIX_MAX_ATTEMPTS` | `20` | Max NuSMV calls per fix strategy |
| `FIX_MAX_CANDIDATES_PER_RULE` | `5` | Max candidate fixes per rule |
| `FIX_MAX_REFINE_ATTEMPTS` | `10` | Max refinement-loop iterations |
| `FIX_TIMEOUT_MS` | `300000` | Overall fix timeout / soft deadline (ms) |

## Device Templates

| Env var | Default | Notes |
| :--- | :--- | :--- |
| `DEVICE_TEMPLATE_SCHEMA_PATH` | `device-template-schema.json` | Optional filesystem override for the canonical device-template manifest schema. The repository source of truth is `backend/device-template-schema.json`; the Maven build also packages that file onto the backend classpath. Leave this unset unless a deployment intentionally supplies the same schema from a mounted path. |

## Thread pools

Five pools, each with the same four parameters. Env-var pattern:
`THREAD_POOL_{NAME}_{PARAM}` where `PARAM` ∈ `CORE`, `MAX`, `QUEUE`, `AWAIT`.

Concrete env vars are: `THREAD_POOL_CHAT_CORE`, `THREAD_POOL_CHAT_MAX`,
`THREAD_POOL_CHAT_QUEUE`, `THREAD_POOL_CHAT_AWAIT`, `THREAD_POOL_VERIFICATION_TASK_CORE`,
`THREAD_POOL_VERIFICATION_TASK_MAX`, `THREAD_POOL_VERIFICATION_TASK_QUEUE`,
`THREAD_POOL_VERIFICATION_TASK_AWAIT`, `THREAD_POOL_SYNC_VERIFICATION_CORE`,
`THREAD_POOL_SYNC_VERIFICATION_MAX`, `THREAD_POOL_SYNC_VERIFICATION_QUEUE`,
`THREAD_POOL_SYNC_VERIFICATION_AWAIT`, `THREAD_POOL_SYNC_SIMULATION_CORE`,
`THREAD_POOL_SYNC_SIMULATION_MAX`, `THREAD_POOL_SYNC_SIMULATION_QUEUE`,
`THREAD_POOL_SYNC_SIMULATION_AWAIT`, `THREAD_POOL_SIMULATION_TASK_CORE`,
`THREAD_POOL_SIMULATION_TASK_MAX`, `THREAD_POOL_SIMULATION_TASK_QUEUE`,
`THREAD_POOL_SIMULATION_TASK_AWAIT`.

| Pool (`NAME`) | CORE | MAX | QUEUE | AWAIT (s) |
| :--- | :--- | :--- | :--- | :--- |
| `CHAT` | 10 | 50 | 200 | 30 |
| `VERIFICATION_TASK` | 4 | 8 | 40 | 60 |
| `SYNC_VERIFICATION` | 4 | 4 | 16 | 30 |
| `SYNC_SIMULATION` | 4 | 4 | 16 | 30 |
| `SIMULATION_TASK` | 4 | 8 | 40 | 60 |

Example override: `THREAD_POOL_CHAT_CORE=20`.

---

## Production safety

When `spring.profiles.active` contains `prod` or `production` (case-insensitive),
`ProductionSafetyCheck` (`@PostConstruct`) refuses to start if any of these still hold
their unsafe default: `JWT_SECRET`, `DB_PASSWORD`, `OPENAI_API_KEY`. Override all
three before deploying.

---

## Frontend (Vite)

Build-time variables read via `import.meta.env`. Copy `frontend/.env.example` to
`frontend/.env` to override; `.env` is gitignored, `.env.example` is committed.

| Variable | Default | Notes |
| :--- | :--- | :--- |
| `VITE_API_BASE_URL` | *(empty)* | Backend origin, read by both the axios client (`src/api/http.ts`, which appends `/api`) and the chat SSE call (`src/api/chat.ts`). **Leave empty** for same-origin setups: requests use a relative `/api` proxied by the Vite dev server (`vite.config.ts`) or a production reverse proxy (Nginx). Set an absolute URL (e.g. `https://api.example.com`) only for cross-origin deployments. |

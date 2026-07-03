# Installation

> Verified against code on 2026-07-03. Source: root `README.md`, `backend/README.md` (§3 Prerequisites & Installation), `backend/pom.xml`, `frontend/package.json`, `frontend/vite.config.ts`.

This guide covers a local development setup of the IoT-Verify platform (Vue 3 frontend + Spring Boot backend + NuSMV model checker). For the complete list of environment variables and their defaults, see [configuration.md](./configuration.md) — it is the single source of truth. This page only names the variables you must set.

## Prerequisites

| Dependency | Version | Notes |
| ---------- | ------- | ----- |
| JDK        | 17+     | Backend runtime (Spring Boot 3.5.7 targets Java 17) |
| Node.js    | 18+     | Frontend runtime |
| Maven      | 3.6+    | Backend build |
| MySQL      | 8.0+    | Primary datastore |
| Redis      | 6.0+    | Optional. JWT logout blacklist; runs fail-open (the app continues to start if Redis is unavailable) |
| NuSMV      | 2.6-2.7 | Formal verification engine. **NOT nuXmv — nuXmv is incompatible.** |

### NuSMV

Download NuSMV from the [NuSMV official site](http://nusmv.fbk.eu/). You need a 2.6 or 2.7 release; nuXmv will not work.

Typical install paths (used to set `NUSMV_PATH`):

- Windows: `D:/NuSMV/NuSMV-2.7.1-win64/NuSMV-2.7.1-win64/bin/NuSMV.exe`
- Linux: `/usr/local/bin/NuSMV`
- macOS: `/usr/local/bin/NuSMV`

Verify the install resolves:

```bash
NuSMV -version   # should report 2.6+ (not nuXmv)
```

### AI features

AI-powered assistance (chat, rule/spec/device recommendations) requires a Volcengine Ark API key. Set it via `VOLCENGINE_API_KEY` (see [configuration.md](./configuration.md)).

## Steps

### 1. Create the MySQL database

Create a database named `iot_verify` with the `utf8mb4` character set:

```bash
mysql -u root -p -e "CREATE DATABASE iot_verify CHARACTER SET utf8mb4 COLLATE utf8mb4_unicode_ci;"
```

The backend auto-creates all tables on first startup, so no schema import is needed.

### 2. Set required environment variables

All backend settings can be overridden by environment variables. At minimum you must set the following (full list and defaults in [configuration.md](./configuration.md)):

- `DB_PASSWORD` — your MySQL password
- `JWT_SECRET` — signing key for JWT auth (min 256 bits)
- `VOLCENGINE_API_KEY` — required for AI features
- `NUSMV_PATH` — absolute path to the NuSMV executable (required for verification)

```bash
export DB_PASSWORD="your_mysql_password"
export JWT_SECRET="your-secret-key-here-min-256-bits"
export VOLCENGINE_API_KEY="your-api-key"
export NUSMV_PATH="/path/to/NuSMV"
```

### 3. Build and run the backend

```bash
cd backend
mvn clean install -DskipTests
mvn spring-boot:run
```

The backend listens on `http://localhost:8080` and creates its tables automatically on first run.

### 4. Install and run the frontend

```bash
cd frontend
npm install
npm run dev
```

The dev server listens on `http://localhost:3000` and proxies `/api` to `http://localhost:8080` (configured in `frontend/vite.config.ts`). npm scripts: `dev` (Vite dev server), `build` (`vue-tsc` type-check + production build), `preview` (serve the build), `test:unit` (Vitest).

For the frontend source layout see [../architecture/overview.md](../architecture/overview.md#frontend-layout); for how the frontend calls the backend see [../guides/frontend-integration.md](../guides/frontend-integration.md).

## Verify the install

Register a user, then log in. Both endpoints are documented in [auth.md](../api/auth.md).

```bash
# Register
curl -X POST http://localhost:8080/api/auth/register \
  -H "Content-Type: application/json" \
  -d '{"phone":"13800138000","password":"password123","username":"testuser"}'

# Login
curl -X POST http://localhost:8080/api/auth/login \
  -H "Content-Type: application/json" \
  -d '{"phone":"13800138000","password":"password123"}'
```

A successful call returns the standard envelope `{"code": 200, "message": "success", "data": {...}}`. If either call fails, see [../guides/troubleshooting.md](../guides/troubleshooting.md).

## Next steps

- Production setup: [deployment.md](./deployment.md)
- Configuration reference: [configuration.md](./configuration.md)
- API overview: [../api/overview.md](../api/overview.md)
- Documentation map: [../README.md](../README.md)

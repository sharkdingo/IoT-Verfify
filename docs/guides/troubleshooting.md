# Troubleshooting

> Verified against code on 2026-07-03. Source: root `README.md` (FAQ), `backend/README.md` (§10 Troubleshooting).

Common issues and fixes. For every configuration key mentioned here, see [../getting-started/configuration.md](../getting-started/configuration.md) for the variable, its default, and how it is resolved — this page does not repeat defaults.

## MySQL connection failure

The backend cannot reach the database on startup.

- Confirm MySQL is running: `mysql -u root -p -e "SHOW DATABASES;"`
- Confirm the `iot_verify` database exists (see [../getting-started/installation.md](../getting-started/installation.md)).
- Check the connection settings (`DB_URL`, `DB_USERNAME`, `DB_PASSWORD`) in [../getting-started/configuration.md](../getting-started/configuration.md).

## Redis connection failure

```
Unable to connect to Redis at localhost:6379
```

Redis is optional and runs in fail-open mode: a failed connection does not stop the backend from starting. The only degraded behavior is the JWT logout blacklist — token revocation on logout stops working, so previously issued tokens remain valid until they expire.

- To restore full behavior, start Redis (`redis-server`, or `docker run -d -p 6379:6379 redis:alpine`).
- Otherwise it is safe to continue without Redis.

See `REDIS_HOST` / `REDIS_PORT` / `REDIS_PASSWORD` in [../getting-started/configuration.md](../getting-started/configuration.md).

## CORS errors

The browser blocks requests from the frontend origin.

- Confirm `CORS_ORIGINS` includes the exact origin (scheme, host, and port) the frontend runs on. See [../getting-started/configuration.md](../getting-started/configuration.md).

## NuSMV execution failure

**Synchronous verification** returns HTTP 200 with `safe: false` and details in `checkLogs`:

```json
{
  "code": 200,
  "data": {
    "safe": false,
    "traces": [],
    "specResults": [],
    "checkLogs": ["NuSMV execution failed: <error details>"]
  }
}
```

**Asynchronous verification** task status shows `FAILED`:

```json
{
  "status": "FAILED",
  "errorMessage": "NuSMV execution failed: NuSMV exited with code 1: <output details>"
}
```

Checklist:

- Confirm `nusmv.path` (`NUSMV_PATH`) points to the correct NuSMV executable.
- Confirm the version is NuSMV 2.6+ and **not nuXmv** (incompatible): `NuSMV -version`.
- On Linux running a Windows NuSMV build, set `nusmv.command-prefix` (`NUSMV_PREFIX=wine`) so the executable is launched through Wine.
- Review the specific error in `checkLogs` (sync) or `errorMessage` (async).

See NuSMV keys in [../getting-started/configuration.md](../getting-started/configuration.md) and the model details in [../architecture/nusmv-model.md](../architecture/nusmv-model.md).

## Verification timeout

**Synchronous verification** returns HTTP 200 with `safe: false` and a timeout note in `checkLogs`:

```json
{
  "code": 200,
  "data": {
    "safe": false,
    "traces": [],
    "specResults": [],
    "checkLogs": ["Verification timed out"]
  }
}
```

**Asynchronous verification** task status shows `FAILED`:

```json
{
  "status": "FAILED",
  "errorMessage": "NuSMV execution failed: NuSMV execution timed out after ..."
}
```

This means the model is too complex or the timeout is too short. Try:

- Raise the per-verification timeout via `NUSMV_TIMEOUT_MS`.
- Reduce the state space: fewer devices and/or rules.
- Lower `NUSMV_MAX_CONCURRENT` to balance concurrency against system resources.
- Prefer async verification (`POST /api/verify/async`) for large models so the request does not block.

See the NuSMV timeout/concurrency keys in [../getting-started/configuration.md](../getting-started/configuration.md).

## JWT token expired

```json
{"code": 401, "message": "Token expired"}
```

The access token has passed its expiration window. Log in again to obtain a new token. See [../api/auth.md](../api/auth.md); token lifetime is controlled by `JWT_EXPIRATION` in [../getting-started/configuration.md](../getting-started/configuration.md).

## Related

- Installation: [../getting-started/installation.md](../getting-started/installation.md)
- Deployment: [../getting-started/deployment.md](../getting-started/deployment.md)
- Configuration reference: [../getting-started/configuration.md](../getting-started/configuration.md)
- Documentation map: [../README.md](../README.md)

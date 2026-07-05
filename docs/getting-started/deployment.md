# Production Deployment

> Verified against code on 2026-07-05. Source: `backend/pom.xml`,
> `backend/src/main/java/cn/edu/nju/Iot_Verify/configure/ProductionSafetyCheck.java`,
> `frontend/package.json`, `frontend/src/api/`, `frontend/vite.config.ts`.

This guide covers packaging and deploying IoT-Verify for production. For the full list of environment variables and their defaults, see [configuration.md](./configuration.md) — it is the single source of truth. This page only names the variables that matter for a production rollout.

## Backend

Package the backend into a runnable jar and start it under the production profile:

```bash
cd backend
mvn clean package -DskipTests
java -jar target/Iot-Verify-0.0.1-SNAPSHOT.jar --spring.profiles.active=prod
```

### Production safety check

When the backend starts under the `prod` or `production` profile, `ProductionSafetyCheck` refuses to start unless the following values are overridden from their unsafe defaults:

- `JWT_SECRET`
- `DB_PASSWORD`
- `OPENAI_API_KEY`

If any of these still hold their default value, startup aborts with an error. Set real values before deploying — see [configuration.md](./configuration.md) for how each variable is resolved.

### CORS

`CORS_ORIGINS` must include the origin from which the deployed frontend is served (scheme, host, and port). Requests from an origin not in this list are rejected by the browser. See [configuration.md](./configuration.md).

## Frontend

Build the static bundle:

```bash
cd frontend
npm run build
```

This produces a `dist/` directory. Deploy `dist/` behind a web server (for example
Nginx). In the default same-origin build, frontend requests go to relative `/api`, so
the web server should proxy `/api` to the backend.

That same-origin proxy is the default and recommended production shape: leave
`VITE_API_BASE_URL` empty when building the frontend and proxy `/api` from the SPA host
to the backend. For a cross-origin deployment, build the frontend with an absolute
`VITE_API_BASE_URL` such as `https://api.example.com`; `src/api/http.ts` and
`src/api/chat.ts` append `/api` themselves. In that cross-origin shape, configure
`CORS_ORIGINS` on the backend to include the frontend origin, and the SPA host does not
need an `/api` reverse proxy.

## Nginx reference configuration

The web server serves the SPA bundle with a `try_files` fallback to `index.html` (so client-side routes resolve) and proxies `/api` to the backend on `localhost:8080`:

```nginx
server {
    listen 80;
    server_name your-domain.com;

    location / {
        root /var/www/iot-verify/dist;
        try_files $uri $uri/ /index.html;
    }

    location /api {
        proxy_pass http://localhost:8080;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
    }
}
```

Make sure the deployed frontend origin (for example `http://your-domain.com`) is present in `CORS_ORIGINS` on the backend.

## Related

- Local setup: [installation.md](./installation.md)
- Configuration reference: [configuration.md](./configuration.md)
- Troubleshooting: [../guides/troubleshooting.md](../guides/troubleshooting.md)
- Documentation map: [../README.md](../README.md)

# IoT-Verify Frontend

Vue 3 + TypeScript + Vite single-page app for the IoT-Verify platform. This file covers
running the frontend locally and its source layout. For everything else, see the project
**[Documentation Hub](../docs/README.md)**.

## Run locally

Prerequisites: Node.js 18+. The backend should be running on `http://localhost:8080`
(see [../backend/README.md](../backend/README.md)).

```bash
npm install
npm run dev        # http://localhost:3000, proxies /api → http://localhost:8080
```

Other scripts: `npm run build` (type-check via `vue-tsc` + production build),
`npm run preview`, `npm run test:unit` (Vitest), `npm run test:e2e` (Playwright).
The e2e suite starts the Vite frontend automatically when `E2E_BASE_URL` is unset,
but it exercises real auth/board APIs, so keep the backend running at
`E2E_API_BASE_URL` (default `http://127.0.0.1:8080`).

## Source layout

```
src/
  api/       http.ts (axios) + auth / board / chat / rules / simulation modules
  types/     TypeScript contracts (auth, device, node, edge, rule, spec, verify, fix, …)
  stores/    reactive state (auth, chat)
  router/    routes + auth guard
  views/     Landing / Login / Register / Board / TemplateCreate / NotFound
  components/ CanvasBoard, ChatView, ControlCenter, SystemInspector,
              TraceVisualization, SimulationTimeline, FixResultDialog,
              RuleBuilderDialog, DeviceDialog, …
  assets/    static assets + i18n (zh-CN / en)
```

## How the frontend talks to the backend

See [docs/guides/frontend-integration.md](../docs/guides/frontend-integration.md) for
the axios client, the real `boardApi` / `authApi` shapes, the two response-unwrapping
conventions, and the SSE chat streaming. Backend API contracts:
[docs/api/](../docs/api/rest-endpoints.md).

> Base URL: both `src/api/http.ts` (axios) and `src/api/chat.ts` (SSE) read
> `VITE_API_BASE_URL`. Leave it empty (default) for same-origin setups — requests use a
> relative `/api` proxied by Vite in dev and by your reverse proxy in prod. Set an
> absolute URL only for cross-origin deployments. See the frontend integration guide.

## License

See the LICENSE note in the project [README](../README.md#license).

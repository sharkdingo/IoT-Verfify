# IoT-Verify Frontend API Documentation

## Overview

This document describes the frontend API layer, including HTTP client configuration, API service functions, and type definitions.

---

## API Directory Structure

```
frontend/src/
├── api/
│   ├── http.ts          # Axios instance with interceptors
│   ├── auth.ts          # Authentication API
│   ├── board.ts         # Board storage API (nodes, edges, specs, rules, etc.)
│   └── chat.ts          # Chat API (SSE streaming)
├── types/
│   ├── auth.ts          # Auth-related types
│   ├── chat.ts          # Chat types
│   ├── device.ts        # Device template types
│   ├── edge.ts          # Edge types
│   ├── node.ts          # Node types
│   ├── panel.ts         # Panel/layout types
│   ├── rule.ts          # Rule types
│   └── spec.ts          # Specification types
└── stores/
    └── auth.ts          # Auth state management (Vue reactive)
```

---

## HTTP Client Configuration

### File: `src/api/http.ts`

The Axios instance is configured with:
- **Base URL**: `http://localhost:8080/api`
- **Request Interceptor**: Automatically adds `Authorization: Bearer <token>` header
- **Response Interceptor**: Handles 401 errors (clears auth state, redirects to login)

```typescript
import axios from 'axios';
import { useAuth } from '../stores/auth';
import { router } from '../router';

const api = axios.create({
  baseURL: 'http://localhost:8080/api',
  timeout: 10000,
  headers: {
    'Content-Type': 'application/json'
  }
});

// Request interceptor
api.interceptors.request.use((config) => {
  const { getToken } = useAuth();
  const token = getToken();
  if (token) {
    config.headers.Authorization = `Bearer ${token}`;
  }
  return config;
});

// Response interceptor
api.interceptors.response.use(
  (response) => response,
  (error) => {
    if (error.response?.status === 401) {
      const { logout } = useAuth();
      logout();
      const currentPath = router.currentRoute.value.path;
      if (!['/login', '/register'].includes(currentPath)) {
        router.push({ path: '/login', query: { redirect: currentPath } });
      }
    }
    return Promise.reject(error);
  }
);

export default api;
```

---

## Result Unpacking

### File: `src/api/board.ts`

All REST APIs return data wrapped in `Result<T>` format:
```json
{
  "code": 200,
  "message": "success",
  "data": <T>
}
```

The `unpack` function extracts the `data` field:

```typescript
const unpack = <T>(response: any): T => {
  return response.data.data;
};
```

**Note:** After unpacking, the return value is the raw data (not wrapped).

---

## Authentication API

### File: `src/api/auth.ts`

| Function | Method | Endpoint | Description |
|----------|--------|----------|-------------|
| `login(data)` | POST | `/auth/login` | User login |
| `register(data)` | POST | `/auth/register` | User registration |
| `logout()` | POST | `/auth/logout` | User logout (blacklists token) |
| `getUserInfo()` | GET | `/auth/me` | Get current user info |

### Usage Example
```typescript
import { login, logout } from '@/api/auth';

const handleLogin = async () => {
  const response = await login({ phone: '13800138000', password: '123456' });
  // Response is already unpacked
  console.log(response.userId, response.token);
};
```

---

## Board Storage API

### File: `src/api/board.ts`

#### Nodes (Devices)

| Function | Method | Endpoint | Description |
|----------|--------|----------|-------------|
| `getNodes()` | GET | `/board/nodes` | Get all device nodes |
| `saveNodes(nodes)` | POST | `/board/nodes` | Save nodes (full replace) |

#### Edges

| Function | Method | Endpoint | Description |
|----------|--------|----------|-------------|
| `getEdges()` | GET | `/board/edges` | Get all edges |
| `saveEdges(edges)` | POST | `/board/edges` | Save edges (full replace) |

#### Specifications

| Function | Method | Endpoint | Description |
|----------|--------|----------|-------------|
| `getSpecs()` | GET | `/board/specs` | Get all specifications |
| `saveSpecs(specs)` | POST | `/board/specs` | Save specifications |

#### Rules

| Function | Method | Endpoint | Description |
|----------|--------|----------|-------------|
| `getRules()` | GET | `/board/rules` | Get all rules |
| `saveRules(rules)` | POST | `/board/rules` | Save rules (incremental update) |

#### Layout

| Function | Method | Endpoint | Description |
|----------|--------|----------|-------------|
| `getLayout()` | GET | `/board/layout` | Get panel layout |
| `saveLayout(layout)` | POST | `/board/layout` | Save layout |

#### Active Tabs

| Function | Method | Endpoint | Description |
|----------|--------|----------|-------------|
| `getActive()` | GET | `/board/active` | Get active tabs |
| `saveActive(active)` | POST | `/board/active` | Save active tabs |

#### Device Templates

| Function | Method | Endpoint | Description |
|----------|--------|----------|-------------|
| `getTemplates()` | GET | `/board/templates` | Get all templates |
| `addTemplate(template)` | POST | `/board/templates` | Add new template |

### Usage Example
```typescript
import boardApi from '@/api/board';

// Get all nodes
const nodes = await boardApi.getNodes();
console.log(nodes);

// Save a new node
await boardApi.saveNodes([{
  id: 'node-1',
  templateName: 'AirConditioner',
  label: 'AC-1',
  position: { x: 100, y: 200 },
  width: 150,
  height: 100
}]);
```

---

## Chat API (SSE Streaming)

### File: `src/api/chat.ts`

The chat API uses native `fetch` for Server-Sent Events (SSE) streaming, as SSE is not well-supported by Axios.

#### Functions

| Function | Method | Endpoint | Description |
|----------|--------|----------|-------------|
| `getSessionList()` | GET | `/chat/sessions` | Get user's chat sessions |
| `createSession()` | POST | `/chat/sessions` | Create new session |
| `getSessionHistory(id)` | GET | `/chat/sessions/{id}/messages` | Get message history |
| `deleteSession(id)` | DELETE | `/chat/sessions/{id}` | Delete a session |
| `sendStreamChat(sessionId, content, callbacks, controller)` | POST | `/chat/completions` | Send message (SSE) |

#### sendStreamChat Signature

```typescript
export const sendStreamChat = async (
    sessionId: string,
    content: string,
    callbacks: {
        onMessage: (text: string) => void           // Called for each content chunk
        onCommand?: (cmd: StreamCommand) => void;   // Called when command received
        onError?: (err: any) => void                 // Called on error
        onFinish?: () => void                        // Called when stream ends
    },
    controller?: AbortController
) => {
  // ...
}
```

#### Usage Example

```typescript
import { sendStreamChat } from '@/api/chat';

const handleSendMessage = async () => {
  const abortController = new AbortController();
  
  await sendStreamChat(
    sessionId,
    content,
    {
      onMessage: (chunk) => {
        // Append AI response chunk to message
        messageContent += chunk;
      },
      onCommand: (cmd) => {
        console.log('Command received:', cmd);
        // Handle commands like REFRESH_DATA
        if (cmd.type === 'REFRESH_DATA') {
          refreshDeviceList();
        }
      },
      onError: (err) => {
        console.error('Stream error:', err);
        messageContent += '\n[发送失败]';
      },
      onFinish: () => {
        isLoading.value = false;
        abortController.abort();
      }
    },
    abortController
  );
};
```

#### Stream Command Type

```typescript
interface StreamCommand {
  type: string;              // e.g., "REFRESH_DATA"
  payload?: Record<string, any>;  // Command parameters
}
```

---

## Frontend Type Definitions

### Type Mappings (Frontend ↔ Backend DTO)

| Frontend Type | Backend DTO | File |
|---------------|-------------|------|
| `DeviceNode` | `DeviceNodeDto` | `types/node.ts` |
| `DeviceEdge` | `DeviceEdgeDto` | `types/edge.ts` |
| `Specification` | `SpecificationDto` | `types/spec.ts` |
| `RuleForm` | `RuleDto` | `types/rule.ts` |
| `DeviceTemplate` | `DeviceTemplateDto` | `types/device.ts` |
| `ChatSession` | `ChatSessionPo` | `types/chat.ts` |
| `ChatMessage` | `ChatMessagePo` | `types/chat.ts` |

### Example: DeviceNode Type

```typescript
// frontend/src/types/node.ts
export interface DeviceNode {
  id: string;
  templateName: string;
  label: string;
  position: { x: number; y: number };
  state: string;
  width: number;
  height: number;
}
```

### Example: ChatSession Type

```typescript
// frontend/src/types/chat.ts
export interface ChatSession {
  id: string;        // UUID
  userId: string;    // User ID (from JWT)
  title: string;
  updatedAt: string; // ISO datetime string
}

export interface ChatMessage {
  id?: number;
  role: 'user' | 'assistant' | 'tool';
  content: string;
}
```

---

## Authentication State Management

### File: `src/stores/auth.ts`

Uses Vue 3 `reactive()` for state management:

```typescript
interface AuthState {
  token: string | null;
  user: UserInfo | null;
  isLoggedIn: boolean;
}

interface UserInfo {
  userId: number;
  phone: string;
  username: string;
}

// Usage
const { getToken, getUser, isAuthenticated, logout } = useAuth();

const token = getToken();  // Returns JWT token string
const user = getUser();    // Returns UserInfo object
const loggedIn = isAuthenticated();
```

---

## Environment Variables

### File: `frontend/.env`

```bash
# API 基础地址（后端服务地址）
VITE_API_BASE_URL=http://localhost:8080
```

---

## Error Handling

### Frontend Error Handling Strategy

1. **HTTP Errors (4xx, 5xx)**
   - Axios response interceptor handles 401 (redirects to login)
   - Other errors are thrown and caught by components

2. **SSE Stream Errors**
   - Handled in `sendStreamChat` callbacks
   - `onError`: Called on stream error
   - `onFinish`: Called when stream ends (even after error)
   - Only show error if no content was received

### Common Error Messages

| Scenario | Frontend Display |
|----------|-----------------|
| Network error | "发送消息失败: network error" |
| 401 Unauthorized | Redirected to /login |
| Validation error | Displayed from backend message |

---

## Quick Start for Frontend Developers

### 1. Make an API Call
```typescript
import boardApi from '@/api/board';

// GET request
const nodes = await boardApi.getNodes();

// POST request
await boardApi.saveNodes(nodes);
```

### 2. Handle SSE Stream
```typescript
import { sendStreamChat } from '@/api/chat';

await sendStreamChat(sessionId, message, {
  onMessage: (chunk) => {
    // Update UI with response chunk
    response.value += chunk;
  },
  onCommand: (cmd) => {
    // Handle commands
    if (cmd.type === 'REFRESH_DATA') {
      refreshData();
    }
  },
  onError: (err) => {
    console.error('Error:', err);
  },
  onFinish: () => {
    isLoading.value = false;
  }
});
```

### 3. Access Auth State
```typescript
import { useAuth } from '@/stores/auth';

const { getToken, getUser, logout } = useAuth();
const token = getToken();  // Use in custom fetch calls
```

---

## Related Documentation

- **Backend API**: [backend/API-DOCUMENTATION.md](../backend/API-DOCUMENTATION.md)
- **Project README**: [README.md](../README.md)

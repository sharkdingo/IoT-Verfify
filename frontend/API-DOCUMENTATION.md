# IoT-Verify Frontend API Documentation

## Overview

This document describes the frontend API layer, including HTTP client configuration, API service functions, and type definitions.

### What's New

- **Asynchronous Verification**: Long-running verifications now support async mode with progress tracking
- **Task Management**: New APIs for task status, progress polling, and cancellation
- **Enhanced Trace Parser**: Backend now supports MEDIC-test output format

### Documentation Sections

1. [API Directory Structure](#api-directory-structure)
2. [HTTP Client Configuration](#http-client-configuration)
3. [Result Unpacking](#result-unpacking)
4. [Authentication API](#authentication-api)
5. [Board Storage API](#board-storage-api)
6. [Chat API (SSE Streaming)](#chat-api-sse-streaming)
7. [Verification API](#verification-api) ⭐ **Updated with async support**
8. [Frontend Type Definitions](#frontend-type-definitions)
9. [Authentication State Management](#authentication-state-management)
10. [Environment Variables](#environment-variables)
11. [Error Handling](#error-handling)
12. [Quick Start for Frontend Developers](#quick-start-for-frontend-developers)

---

## API Directory Structure

```
frontend/src/
├── api/
│   ├── http.ts          # Axios instance with interceptors
│   ├── auth.ts          # Authentication API
│   ├── board.ts         # Board storage API (nodes, edges, specs, rules, etc.)
│   ├── chat.ts          # Chat API (SSE streaming)
│   └── verify.ts        # Verification API (sync/async verification, traces)
├── types/
│   ├── auth.ts          # Auth-related types
│   ├── chat.ts          # Chat types
│   ├── device.ts        # Device template types
│   ├── edge.ts          # Edge types
│   ├── node.ts          # Node types
│   ├── panel.ts         # Panel/layout types
│   ├── rule.ts          # Rule types
│   ├── spec.ts          # Specification types
│   ├── trace.ts         # Trace types (counterexample traces)
│   └── verify.ts        # Verification types (tasks, results)
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

---

## Verification API

### File: `src/api/verify.ts`

The verification API handles IoT system verification using NuSMV model checking.

**Note:** The API now supports both synchronous and asynchronous verification modes.

#### Functions

| Function | Method | Endpoint | Description |
|----------|--------|----------|-------------|
| `verify(request)` | POST | `/verify` | Execute verification (synchronous) |
| `verifyAsync(request, taskId)` | POST | `/verify/async?taskId={taskId}` | Execute verification (asynchronous) |
| `getTask(taskId)` | GET | `/verify/tasks/{taskId}` | Get task status and result |
| `getTaskProgress(taskId)` | GET | `/verify/tasks/{taskId}/progress` | Get task progress (0-100) |
| `cancelTask(taskId)` | POST | `/verify/tasks/{taskId}/cancel` | Cancel a running task |
| `getTraces()` | GET | `/verify/traces` | Get all user traces |
| `getTrace(id)` | GET | `/verify/traces/{id}` | Get single trace |
| `deleteTrace(id)` | DELETE | `/verify/traces/{id}` | Delete trace |

#### When to Use Async Verification

- **Synchronous** (`verify`): Use for quick verifications (< 10 seconds). Blocks UI until complete.
- **Asynchronous** (`verifyAsync`): Use for long-running verifications. Returns immediately, poll for progress.

#### Data Type Definitions

```typescript
// Backend RuleDto (used by /verify and /board/rules)
interface RuleDto {
  id?: string;
  userId?: number;
  conditions: RuleConditionDto[];
  command: RuleCommandDto;
  ruleString?: string;
}

interface RuleConditionDto {
  deviceName: string;   // Source device name or ID
  attribute: string;    // State/variable/API name
  relation?: string;    // "=", ">", "<", etc. If null => API signal
  value?: string;       // Condition value
}

interface RuleCommandDto {
  deviceName: string;   // Target device name or ID
  action: string;       // API/action name
  contentDevice?: string;
  content?: string;
}

// Specification with seven types
interface SpecificationDto {
  id: string;
  templateId: string;        // "1"-"7" for spec types
  templateLabel: string;
  aConditions: SpecConditionDto[];    // For always/eventually/never
  ifConditions: SpecConditionDto[];     // For B-type specs (IF)
  thenConditions: SpecConditionDto[];   // For B-type specs (THEN)
}

// Specification condition
interface SpecConditionDto {
  id: string;
  side: 'a' | 'if' | 'then';
  deviceId: string;
  deviceLabel: string;
  targetType: 'state' | 'variable' | 'api';
  key: string;               // State/variable/API name
  relation: string;
  value: string;
}

// Seven Specification Types Mapping
type SpecTemplateType = 
  | 'always'      // templateId: "1" - AG(A) - A holds forever
  | 'eventually'  // templateId: "2" - AF(A) - A will happen later
  | 'never'       // templateId: "3" - AG !(A) - A never happens
  | 'immediate'   // templateId: "4" - AG(A -> AX(B)) - A→B at same time
  | 'response'    // templateId: "5" - AG(A -> AF(B)) - A→◇B eventually
  | 'persistence' // templateId: "6" - LTL G(A -> F G(B)) - A→□B forever
  | 'safety'      // templateId: "7" - AG(untrusted -> !A) - untrusted constraint
```

#### verify Function

```typescript
interface VerificationRequest {
  devices: DeviceNodeDto[];
  rules: RuleDto[];
  specs: SpecificationDto[];
  isAttack: boolean;
  intensity: number; // 0-50
}

interface VerificationResult {
  safe: boolean;
  traces: TraceDto[];
  specResults: boolean[];
  checkLogs: string[];
  nusmvOutput: string;
}

// Task status for async verification
type TaskStatus = 'PENDING' | 'RUNNING' | 'COMPLETED' | 'FAILED' | 'CANCELLED';

interface VerificationTask {
  id: number;
  userId: number;
  status: TaskStatus;
  createdAt: string;      // ISO datetime
  startedAt?: string;     // ISO datetime
  completedAt?: string;   // ISO datetime
  processingTimeMs?: number;
  isSafe?: boolean;
  violatedSpecCount?: number;
  checkLogs: string[];
  nusmvOutput?: string;
  errorMessage?: string;
}

export const verify = async (request: VerificationRequest): Promise<VerificationResult> => {
  // POST /api/verify
  // Returns: Result<VerificationResult>
};

export const verifyAsync = async (
  request: VerificationRequest, 
  taskId: number
): Promise<number> => {
  // POST /api/verify/async?taskId={taskId}
  // Returns: Result<number> (taskId)
};

export const getTask = async (taskId: number): Promise<VerificationTask> => {
  // GET /api/verify/tasks/{taskId}
  // Returns: Result<VerificationTask>
};

export const getTaskProgress = async (taskId: number): Promise<number> => {
  // GET /api/verify/tasks/{taskId}/progress
  // Returns: Result<number> (0-100)
};

export const cancelTask = async (taskId: number): Promise<boolean> => {
  // POST /api/verify/tasks/{taskId}/cancel
  // Returns: Result<boolean>
};
```

#### getTraces Function

```typescript
export const getTraces = async (): Promise<TraceDto[]> => {
  // GET /api/verify/traces
  // Returns: Result<TraceDto[]>
};
```

#### getTrace Function

```typescript
export const getTrace = async (id: number): Promise<TraceDto | null> => {
  // GET /api/verify/traces/{id}
  // Returns: Result<TraceDto | null>
};
```

#### deleteTrace Function

```typescript
export const deleteTrace = async (id: number): Promise<void> => {
  // DELETE /api/verify/traces/{id}
  // Returns: Result<void>
};
```

#### Trace Type Definitions

```typescript
// frontend/src/types/trace.ts (new file)

export interface TraceDto {
  id: number;
  userId: number;
  violatedSpecId: string;
  violatedSpecJson: string;
  states: TraceStateDto[];
  createdAt: string;  // ISO datetime
}

export interface TraceStateDto {
  stateIndex: number;
  devices: TraceDeviceDto[];
}

export interface TraceDeviceDto {
  deviceId: string;
  deviceLabel: string;
  templateName: string;
  newState: string;
  variables: TraceVariableDto[];
  trustPrivacy: TraceTrustPrivacyDto[];
  privacies: TraceTrustPrivacyDto[];
}

export interface TraceVariableDto {
  name: string;
  value: string;
  trust: string;  // "trusted" or "untrusted"
}

export interface TraceTrustPrivacyDto {
  name: string;
  trust: boolean;   // true = trusted, false = untrusted
  privacy: string;  // "private" or "public"
}
```

#### Usage Example - Synchronous Verification

```typescript
import verificationApi from '@/api/verify';

// Execute verification (blocks until complete)
const result = await verificationApi.verify({
  devices: [
    {
      id: 'device-001',
      templateName: 'AirConditioner',
      label: 'AC Cooler',
      position: { x: 100, y: 200 },
      state: 'Off',
      variables: [{ name: 'temperature', value: '24', trust: 'trusted' }],
      privacies: [{ name: 'temperature', privacy: 'private' }]
    }
  ],
  rules: [
    {
      id: 'rule-001',
      conditions: [
        { deviceName: 'AC Cooler', attribute: 'temperature', relation: '>', value: '28' }
      ],
      command: { deviceName: 'device-001', action: 'turnOn' }
    }
  ],
  specs: [
    {
      id: 'spec-001',
      aConditions: [
        { deviceId: 'device-001', targetType: 'state', key: 'state', relation: '=', value: 'Cooling' }
      ]
    }
  ],
  isAttack: false,
  intensity: 3
});

if (!result.safe) {
  // Display violation traces
  result.traces.forEach(trace => {
    console.log(`Violation: ${trace.violatedSpecId}`);
    trace.states.forEach((state, index) => {
      console.log(`State ${index}:`, state.devices);
    });
  });
}
```

#### Usage Example - Asynchronous Verification

```typescript
import verificationApi from '@/api/verify';

// Start async verification
const taskId = 123; // Generate or get from backend
await verificationApi.verifyAsync(verificationRequest, taskId);

// Poll progress every 2 seconds
const pollProgress = async () => {
  const progress = await verificationApi.getTaskProgress(taskId);
  console.log(`Progress: ${progress}%`);
  
  if (progress < 100) {
    setTimeout(pollProgress, 2000);
  } else {
    // Get final result
    const task = await verificationApi.getTask(taskId);
    console.log('Task completed:', task.status);
    
    if (task.status === 'COMPLETED') {
      console.log('Safe:', task.isSafe);
      console.log('Logs:', task.checkLogs);
    }
  }
};

pollProgress();

// Cancel if needed (e.g., user clicks cancel button)
const handleCancel = async () => {
  const cancelled = await verificationApi.cancelTask(taskId);
  if (cancelled) {
    console.log('Task cancelled successfully');
  }
};
```

#### Async Verification with Progress UI

```typescript
import { ref, onUnmounted } from 'vue';
import verificationApi from '@/api/verify';

const useAsyncVerification = () => {
  const isVerifying = ref(false);
  const progress = ref(0);
  const taskStatus = ref<TaskStatus>('PENDING');
  const result = ref<VerificationTask | null>(null);
  let pollInterval: number | null = null;

  const startVerification = async (request: VerificationRequest, taskId: number) => {
    isVerifying.value = true;
    progress.value = 0;
    taskStatus.value = 'PENDING';
    result.value = null;

    try {
      // Start async verification
      await verificationApi.verifyAsync(request, taskId);
      taskStatus.value = 'RUNNING';

      // Poll progress
      pollInterval = window.setInterval(async () => {
        try {
          progress.value = await verificationApi.getTaskProgress(taskId);
          
          if (progress.value >= 100) {
            // Get final result
            const task = await verificationApi.getTask(taskId);
            result.value = task;
            taskStatus.value = task.status;
            
            // Stop polling
            if (pollInterval) {
              clearInterval(pollInterval);
              pollInterval = null;
            }
            isVerifying.value = false;
          }
        } catch (error) {
          console.error('Poll error:', error);
          stopPolling();
        }
      }, 2000);
    } catch (error) {
      console.error('Start verification error:', error);
      isVerifying.value = false;
    }
  };

  const cancelVerification = async (taskId: number) => {
    try {
      const cancelled = await verificationApi.cancelTask(taskId);
      if (cancelled) {
        taskStatus.value = 'CANCELLED';
        stopPolling();
      }
      return cancelled;
    } catch (error) {
      console.error('Cancel error:', error);
      return false;
    }
  };

  const stopPolling = () => {
    if (pollInterval) {
      clearInterval(pollInterval);
      pollInterval = null;
    }
    isVerifying.value = false;
  };

  // Cleanup on component unmount
  onUnmounted(() => {
    stopPolling();
  });

  return {
    isVerifying,
    progress,
    taskStatus,
    result,
    startVerification,
    cancelVerification
  };
};

// Usage in component
const { isVerifying, progress, taskStatus, result, startVerification, cancelVerification } = useAsyncVerification();

// Template
// <div v-if="isVerifying">
//   <progress :value="progress" max="100">{{ progress }}%</progress>
//   <button @click="cancelVerification(taskId)">Cancel</button>
// </div>
```

#### Test Scenarios

**Safe Configuration (No Violation):**
```typescript
// Spec: state != Cooling, temp=24, trigger when temp > 28
// Expected: safe: true, traces: []
```

**Unsafe Configuration (Violation Detected):**
```typescript
// Spec: state == Cooling, temp can rise, trigger when temp > 28
// Expected: safe: false, traces contains counterexample
```

**Async Verification Flow:**
```typescript
// 1. Start async verification
const taskId = 123;
await verifyAsync(request, taskId);

// 2. Poll progress (0% -> 20% -> 50% -> 80% -> 100%)
// Expected progress stages:
// 0%   - Task started
// 20%  - Generating SMV model
// 50%  - Executing NuSMV
// 80%  - Parsing results
// 100% - Verification completed

// 3. Get final result
const task = await getTask(taskId);
// Expected: status = 'COMPLETED', isSafe = true/false
```

**Task Cancellation:**
```typescript
// 1. Start async verification
const taskId = 456;
await verifyAsync(request, taskId);

// 2. Cancel after 3 seconds
setTimeout(async () => {
  const cancelled = await cancelTask(taskId);
  // Expected: cancelled = true, task status = 'CANCELLED'
}, 3000);
```
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
| `VerificationTask` | `VerificationTaskPo` | `types/verify.ts` |
| `TraceDto` | `TraceDto` | `types/trace.ts` |

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

### Example: VerificationTask Type

```typescript
// frontend/src/types/verify.ts

export type TaskStatus = 'PENDING' | 'RUNNING' | 'COMPLETED' | 'FAILED' | 'CANCELLED';

export interface VerificationTask {
  id: number;
  status: TaskStatus;
  createdAt: string;      // ISO datetime
  startedAt?: string;     // ISO datetime
  completedAt?: string;   // ISO datetime
  processingTimeMs?: number;
  isSafe?: boolean;
  violatedSpecCount?: number;
  checkLogs: string[];
  errorMessage?: string;
}

export interface TraceDto {
  id: number;
  userId: number;
  violatedSpecId: string;
  violatedSpecJson: string;
  states: TraceStateDto[];
  createdAt: string;
}

export interface TraceStateDto {
  stateIndex: number;
  devices: TraceDeviceDto[];
}

export interface TraceDeviceDto {
  deviceId: string;
  deviceLabel: string;
  templateName: string;
  newState: string;
  variables: TraceVariableDto[];
  trustPrivacy: TraceTrustPrivacyDto[];
  privacies: TraceTrustPrivacyDto[];
}

export interface TraceVariableDto {
  name: string;
  value: string;
  trust: string;  // "trusted" or "untrusted"
}

export interface TraceTrustPrivacyDto {
  name: string;
  trust: boolean;
  privacy: string;  // "private" or "public"
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

### 4. Execute Async Verification
```typescript
import verificationApi from '@/api/verify';

// For long-running verifications, use async mode
const taskId = 123; // Generate unique task ID

// Start async verification
await verificationApi.verifyAsync(verificationRequest, taskId);

// Poll progress
const checkProgress = async () => {
  const progress = await verificationApi.getTaskProgress(taskId);
  updateProgressBar(progress);
  
  if (progress < 100) {
    setTimeout(checkProgress, 2000);
  } else {
    // Get result
    const result = await verificationApi.getTask(taskId);
    displayResult(result);
  }
};

checkProgress();

// Allow user to cancel
const handleCancel = async () => {
  await verificationApi.cancelTask(taskId);
};
```

---

## Related Documentation

- **Backend API**: [backend/API-DOCUMENTATION.md](../backend/API-DOCUMENTATION.md)
- **Project README**: [README.md](../README.md)

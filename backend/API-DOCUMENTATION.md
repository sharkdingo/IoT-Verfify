# IoT-Verify Backend API Documentation

## Base URL
```
http://localhost:8080
```

## Authentication

All API endpoints (except `/api/auth/**`) require JWT authentication.

### Headers
```
Authorization: Bearer <token>
```

---

## Response Format

All responses follow the unified `Result<T>` format:

```json
{
  "code": 200,
  "message": "success",
  "data": <T>
}
```

### Status Codes

| Code | Meaning | Description |
|------|---------|-------------|
| 200 | Success | Request completed successfully |
| 400 | Bad Request | Invalid request data or parameters |
| 401 | Unauthorized | Missing or invalid authentication token |
| 403 | Forbidden | Authenticated but lacks permission |
| 404 | Not Found | Resource does not exist |
| 409 | Conflict | Resource already exists or state conflict |
| 422 | Validation Error | Request data failed validation |
| 500 | Internal Server Error | Unexpected server error |
| 503 | Service Unavailable | External service temporarily unavailable |

---

## 1. Authentication API

### 1.1 Register

**Endpoint:** `POST /api/auth/register`

> **Note:** Registration does not return a token. Please login after successful registration.

**Request Body:**
```json
{
  "phone": "13800138000",
  "username": "testuser",
  "password": "123456"
}
```

| Field | Type | Required | Validation |
|-------|------|----------|------------|
| phone | string | Yes | Format: 1[3-9]xxxxxxxxx |
| username | string | Yes | 3-20 characters |
| password | string | Yes | 6-20 characters |

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": {
    "userId": 1,
    "phone": "13800138000",
    "username": "testuser"
  }
}
```

**Error Responses:**

| Code | Message | Cause |
|------|---------|-------|
| 409 | Phone number already registered: 13800138000 | Phone exists |
| 409 | Username already exists: testuser | Username exists |
| 422 | phone: Phone number format is invalid | Invalid phone format |
| 422 | username: Username must be 3-20 characters | Invalid username |
| 422 | password: Password must be 6-20 characters | Invalid password |

---

### 1.2 Login

**Endpoint:** `POST /api/auth/login`

**Request Body:**
```json
{
  "phone": "13800138000",
  "password": "123456"
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| phone | string | Yes | Registered phone number |
| password | string | Yes | User password |

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": {
    "userId": 1,
    "phone": "13800138000",
    "username": "testuser",
    "token": "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9..."
  }
}
```

**Error Responses:**

| Code | Message | Cause |
|------|---------|-------|
| 401 | Phone number or password is incorrect | Invalid credentials |
| 422 | phone: Phone number is required | Missing phone |
| 422 | password: Password is required | Missing password |

---

### 1.3 Logout

**Endpoint:** `POST /api/auth/logout`

> **Note:** Requires authentication. The token will be added to a blacklist and can no longer be used for subsequent requests.

**Headers:**
```
Authorization: Bearer <token>
```

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": null
}
```

**Error Responses:**

| Code | Message | Cause |
|------|---------|-------|
| 401 | Missing Authorization header | No token provided |
| 401 | Invalid or expired token | Token is invalid or expired |

---

## 2. Board Storage API

> All endpoints require authentication.

### 2.1 Device Nodes

#### Get Nodes
**Endpoint:** `GET /api/board/nodes`

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": [
    {
      "id": "node-1",
      "templateName": "AirConditioner",
      "label": "AC-Living-Room",
      "position": {
        "x": 100.0,
        "y": 200.0
      },
      "state": "idle",
      "width": 150,
      "height": 100
    }
  ]
}
```

#### Save Nodes
**Endpoint:** `POST /api/board/nodes`

**Request Body:**
```json
[
  {
    "id": "node-1",
    "templateName": "AirConditioner",
    "label": "AC-Living-Room",
    "position": {
      "x": 100.0,
      "y": 200.0
    },
    "state": "idle",
    "width": 150,
    "height": 100
  }
]
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| id | string | Yes | Unique node identifier |
| templateName | string | Yes | Device template name |
| label | string | No | Display label |
| position | object | Yes | Node position (x, y) |
| state | string | No | Current state |
| width | integer | No | Node width in pixels |
| height | integer | No | Node height in pixels |

**Success Response:** Returns saved nodes array.

---

### 2.2 Device Edges

#### Get Edges
**Endpoint:** `GET /api/board/edges`

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": [
    {
      "id": "edge-1",
      "from": "node-1",
      "to": "node-2",
      "fromLabel": "AC-Living-Room",
      "toLabel": "Thermostat",
      "fromApi": "setTemperature",
      "toApi": "onTemperatureChange",
      "fromPos": { "x": 100.0, "y": 200.0 },
      "toPos": { "x": 300.0, "y": 200.0 }
    }
  ]
}
```

#### Save Edges
**Endpoint:** `POST /api/board/edges`

**Request Body:** Array of edge objects.

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| id | string | Yes | Unique edge identifier |
| from | string | Yes | Source node ID |
| to | string | Yes | Target node ID |
| fromLabel | string | No | Source node label |
| toLabel | string | No | Target node label |
| fromApi | string | No | Source API name |
| toApi | string | No | Target API name |
| fromPos | object | No | Source position (edge endpoint coordinates) |
| toPos | object | No | Target position (edge endpoint coordinates) |

**Success Response:** Returns saved edges array.

---

### 2.3 Specifications

#### Get Specifications
**Endpoint:** `GET /api/board/specs`

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": [
    {
      "id": "spec-1",
      "templateId": "template-1",
      "templateLabel": "AirConditioner",
      "aConditions": [
        {
          "id": "cond-1",
          "side": "a",
          "deviceId": "node-1",
          "deviceLabel": "AC-Living-Room",
          "targetType": "state",
          "key": "power",
          "relation": "==",
          "value": "on"
        }
      ],
      "ifConditions": [],
      "thenConditions": []
    }
  ]
}
```

#### Save Specifications
**Endpoint:** `POST /api/board/specs`

**Request Body:** Array of specification objects.

**SpecConditionDto Structure:**

| Field | Type | Description |
|-------|------|-------------|
| id | string | Condition ID |
| side | string | "a" \| "if" \| "then" |
| deviceId | string | Device node ID |
| deviceLabel | string | Device label |
| targetType | string | "state" \| "variable" \| "api" |
| key | string | Property key |
| relation | string | Comparison operator |
| value | string | Expected value |

**Success Response:** Returns saved specifications array.

---

### 2.4 Rules

#### Get Rules
**Endpoint:** `GET /api/board/rules`

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": [
    {
      "id": "rule-1",
      "sources": [
        {
          "fromId": "node-1",
          "fromApi": "getTemperature",
          "fromLabel": "AC-Living-Room"
        }
      ],
      "toId": "node-2",
      "toApi": "setTemperature",
      "templateLabel": "Thermostat"
    }
  ]
}
```

#### Save Rules
**Endpoint:** `POST /api/board/rules`

**Request Body:** Array of rule objects.

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| id | string | No | Rule ID (auto-generated if not provided) |
| sources | array | Yes | Source entries (fromId, fromApi) |
| toId | string | Yes | Target node ID |
| toApi | string | Yes | Target API name |
| templateLabel | string | No | Target template label |

**Success Response:** Returns saved rules array.

---

### 2.5 Layout

#### Get Layout
**Endpoint:** `GET /api/board/layout`

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": {
    "input": { "x": 24.0, "y": 24.0 },
    "status": { "x": 1040.0, "y": 80.0 },
    "canvasPan": { "x": 0.0, "y": 0.0 },
    "canvasZoom": 1.0,
    "dockState": {
      "input": {
        "isDocked": false,
        "side": null,
        "lastPos": { "x": 24.0, "y": 24.0 }
      },
      "status": {
        "isDocked": false,
        "side": null,
        "lastPos": { "x": 1040.0, "y": 80.0 }
      }
    }
  }
}
```

#### Save Layout
**Endpoint:** `POST /api/board/layout`

**Request Body:** Layout object (same structure as response data).

**Success Response:** Returns saved layout.

---

### 2.6 Active Tabs

#### Get Active Tabs
**Endpoint:** `GET /api/board/active`

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": {
    "input": ["devices", "rules", "specs"],
    "status": ["devices", "edges", "specs"]
  }
}
```

#### Save Active Tabs
**Endpoint:** `POST /api/board/active`

**Request Body:**
```json
{
  "input": ["devices", "rules", "specs"],
  "status": ["devices", "edges", "specs"]
}
```

**Success Response:** Returns saved active tabs.

---

### 2.7 Device Templates

#### Get Templates
**Endpoint:** `GET /api/board/templates`

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": [
    {
      "id": "1",
      "name": "AirConditioner",
      "manifest": {
        "Name": "AirConditioner",
        "Description": "Smart air conditioner device",
        "Modes": ["cooling", "heating", "auto"],
        "InternalVariables": [
          {
            "Name": "temperature",
            "Description": "Current temperature",
            "IsInside": true,
            "PublicVisible": true,
            "Trust": "high",
            "Privacy": "low",
            "LowerBound": 16.0,
            "UpperBound": 30.0
          }
        ],
        "ImpactedVariables": ["roomTemperature"],
        "InitState": "idle",
        "WorkingStates": [
          {
            "Name": "idle",
            "Description": "Device is idle",
            "Trust": "high",
            "Privacy": "low",
            "Invariant": "power == off",
            "Dynamics": []
          }
        ],
        "Transitions": [],
        "APIs": [
          {
            "Name": "turnOn",
            "Description": "Turn on the device",
            "Signal": true,
            "StartState": "idle",
            "EndState": "running",
            "Trigger": "user",
            "Assignments": []
          }
        ]
      }
    }
  ]
}
```

#### Add Template
**Endpoint:** `POST /api/board/templates`

**Request Body:**
```json
{
  "name": "NewDevice",
  "manifest": {
    "Name": "NewDevice",
    "Description": "New device template",
    "Modes": [],
    "InternalVariables": [],
    "ImpactedVariables": [],
    "InitState": "idle",
    "WorkingStates": [],
    "Transitions": [],
    "APIs": []
  }
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| name | string | Yes | Template name (must be unique) |
| manifest | object | No | Device manifest definition |

**Success Response (200):** Returns the created template with generated ID.

**Error Responses:**

| Code | Message | Cause |
|------|---------|-------|
| 409 | Device template already exists: NewDevice | Duplicate name |

---

## 3. Chat API

> All endpoints require authentication.

### 3.1 Get Sessions
**Endpoint:** `GET /api/chat/sessions`

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": [
    {
      "id": "550e8400-e29b-41d4-a716-446655440000",
      "userId": 1,
      "title": "Chat Session 1",
      "createdAt": "2024-01-01T10:00:00",
      "updatedAt": "2024-01-01T10:30:00"
    }
  ]
}
```

| Field | Type | Description |
|-------|------|-------------|
| id | string | Session UUID |
| userId | Long | Owner user ID |
| title | string | Session title (auto-generated from first message) |
| createdAt | DateTime | Creation timestamp |
| updatedAt | DateTime | Last update timestamp |

### 3.2 Create Session
**Endpoint:** `POST /api/chat/sessions`

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": {
    "id": "550e8400-e29b-41d4-a716-446655440000",
    "userId": 1,
    "title": "New Chat",
    "createdAt": "2024-01-01T10:00:00",
    "updatedAt": "2024-01-01T10:00:00"
  }
}
```

### 3.3 Get Messages
**Endpoint:** `GET /api/chat/sessions/{sessionId}/messages`

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": [
    {
      "id": 1,
      "sessionId": "550e8400-e29b-41d4-a716-446655440000",
      "role": "user",
      "content": "Hello",
      "createdAt": "2024-01-01T10:00:00"
    },
    {
      "id": 2,
      "sessionId": "550e8400-e29b-41d4-a716-446655440000",
      "role": "assistant",
      "content": "Hi there! How can I assist you?",
      "createdAt": "2024-01-01T10:00:01"
    }
  ]
}
```

| Field | Type | Description |
|-------|------|-------------|
| id | Long | Message ID (auto-increment) |
| sessionId | string | Parent session UUID |
| role | string | "user" \| "assistant" \| "tool" |
| content | string | Message content |
| createdAt | DateTime | Creation timestamp |

### 3.4 Send Message (SSE Stream)
**Endpoint:** `POST /api/chat/completions`

**Request Body:**
```json
{
  "sessionId": "550e8400-e29b-41d4-a716-446655440000",
  "content": "Your message here"
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| sessionId | string | Yes | Chat session ID |
| content | string | Yes | Message content |

**Response:** Server-Sent Events (SSE) stream.

**SSE Event Format:**

```
data: {"content":"AI response chunk 1"}

data: {"content":"AI response chunk 2"}

data: {"command":{"type":"REFRESH_DATA","payload":{"target":"device_list"}}}

data: [DONE]
```

**StreamResponseDto Structure:**

| Field | Type | Description |
|-------|------|-------------|
| content | string | AI response text chunk (may be empty when command is present) |
| command | CommandDto | Optional command for frontend actions |

**CommandDto Structure:**

| Field | Type | Description |
|-------|------|-------------|
| type | string | Command type (e.g., "REFRESH_DATA") |
| payload | Map | Command parameters |

### 3.5 Delete Session
**Endpoint:** `DELETE /api/chat/sessions/{sessionId}`

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": null
}
```

---

## 4. Error Handling

### Error Response Format
```json
{
  "code": 400,
  "message": "Descriptive error message"
}
```

### Exception Types

| Exception | Code | Usage |
|-----------|------|-------|
| BadRequestException | 400 | Invalid request data |
| UnauthorizedException | 401 | Authentication failure |
| ForbiddenException | 403 | Insufficient permissions |
| ResourceNotFoundException | 404 | Resource not found |
| ConflictException | 409 | Resource conflict |
| ValidationException | 422 | Validation failure |
| InternalServerException | 500 | Server error |
| ServiceUnavailableException | 503 | External service down |

### Common Error Messages

| Scenario | Code | Message |
|----------|------|---------|
| Missing token | 401 | Missing Authorization header |
| Invalid token | 401 | Invalid or expired token |
| Expired token | 401 | Token has expired |
| Token blacklisted | 401 | Invalid or expired token |
| Invalid credentials | 401 | Phone number or password is incorrect |
| Duplicate phone | 409 | Phone number already registered: {phone} |
| Duplicate username | 409 | Username already exists: {username} |
| Duplicate template | 409 | Device template already exists: {name} |
| Session not found | 404 | Chat session not found: {id} |
| User not found | 404 | User not found with id: {id} |
| Validation failed | 422 | {field}: {message} |

---

## 5. Configuration

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| DB_URL | Database connection URL | jdbc:mysql://localhost:3306/iot_verify... |
| DB_USERNAME | Database username | root |
| DB_PASSWORD | Database password | your_password_here |
| SERVER_PORT | Server port | 8080 |
| JWT_SECRET | JWT signing secret (min 256 bits) | iot-verify-secret-key... |
| JWT_EXPIRATION | Token expiration in ms | 86400000 (24 hours) |
| VOLCENGINE_API_KEY | Volcengine AI API key | your_api_key_here |
| VOLCENGINE_MODEL_ID | AI model endpoint ID | ep-20251125202752-bhwbw |
| VOLCENGINE_BASE_URL | Volcengine API base URL | https://ark.cn-beijing.volces.com/api/v3 |
| REDIS_HOST | Redis server host | localhost |
| REDIS_PORT | Redis server port | 6379 |
| REDIS_PASSWORD | Redis password | (empty) |
| REDIS_DATABASE | Redis database number | 0 |

---

## 6. Quick Start Example

### Step 1: Register
```bash
curl -X POST http://localhost:8080/api/auth/register \
  -H "Content-Type: application/json" \
  -d '{"phone":"13800138000","username":"testuser","password":"123456"}'
```

### Step 2: Login
```bash
curl -X POST http://localhost:8080/api/auth/login \
  -H "Content-Type: application/json" \
  -d '{"phone":"13800138000","password":"123456"}'
```

### Step 3: Use Token for Protected APIs
```bash
# Save token from login response
TOKEN="eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9..."

# Get nodes
curl -X GET http://localhost:8080/api/board/nodes \
  -H "Authorization: Bearer $TOKEN"

# Save nodes
curl -X POST http://localhost:8080/api/board/nodes \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '[{"id":"node-1","templateName":"AC","label":"AC1","position":{"x":100,"y":100},"state":"idle","width":150,"height":100}]'
```

### Step 4: Chat with AI (SSE Stream)
```bash
# First create a session
SESSION=$(curl -X POST http://localhost:8080/api/chat/sessions \
  -H "Authorization: Bearer $TOKEN" \
  -s | jq -r '.data.id')

# Send message and receive SSE stream
curl -X POST http://localhost:8080/api/chat/completions \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -H "Accept: text/event-stream" \
  -d "{\"sessionId\":\"$SESSION\",\"content\":\"Hello\"}" \
  --stream
```

### Step 5: Logout
```bash
# Logout to invalidate the token
curl -X POST http://localhost:8080/api/auth/logout \
  -H "Authorization: Bearer $TOKEN"

# Subsequent requests with this token will be rejected
```

---

## 7. Data Models Reference

### DeviceNodeDto
```typescript
interface DeviceNodeDto {
  id: string;           // Required
  templateName: string; // Required
  label: string;
  position: {           // Required
    x: number;          // Required
    y: number;          // Required
  };
  state: string;
  width: number;
  height: number;
  // 运行时状态（验证时使用）
  currentStateTrust?: string;           // "trusted" | "untrusted"
  variables?: VariableStateDto[];       // 变量状态列表
  privacies?: PrivacyStateDto[];        // 隐私状态列表
}

interface VariableStateDto {
  name: string;
  value: string;
  trust: string;         // "trusted" | "untrusted"
}

interface PrivacyStateDto {
  name: string;
  privacy: string;       // "private" | "public"
}
```

### DeviceEdgeDto
```typescript
interface DeviceEdgeDto {
  id: string;       // Required
  from: string;     // Required
  to: string;       // Required
  fromLabel: string;
  toLabel: string;
  fromApi: string;
  toApi: string;
  fromPos: { x: number; y: number };
  toPos: { x: number; y: number };
}
```

### SpecificationDto
```typescript
interface SpecificationDto {
  id: string;
  templateId: string;
  templateLabel: string;
  aConditions: SpecConditionDto[];
  ifConditions: SpecConditionDto[];
  thenConditions: SpecConditionDto[];
}

interface SpecConditionDto {
  id: string;
  side: 'a' | 'if' | 'then';
  deviceId: string;
  deviceLabel: string;
  targetType: 'state' | 'variable' | 'api';
  key: string;
  relation: string;
  value: string;
}
```

### RuleDto
```typescript
interface RuleDto {
  id?: string;              // Optional, auto-generated
  sources: SourceEntryDto[]; // IF conditions (triggers)
  toId: string;             // Required, target device ID
  toApi: string;            // Required, target API name
  templateLabel?: string;   // Target device template label
  privacyDeviceId?: string; // Privacy operation: target device ID
  privacyContent?: string;  // Privacy operation: content
}

interface SourceEntryDto {
  fromId: string;           // Source device ID
  fromLabel?: string;       // Source device label (for display)
  targetType: 'api' | 'variable';  // Trigger type
  fromApi?: string;         // API name (when targetType='api')
  property?: string;        // Variable name (when targetType='variable')
  relation?: string;        // Comparison: "=", ">", "<", etc.
  value?: string;           // Comparison value
}
```

### DeviceTemplateDto
```typescript
interface DeviceTemplateDto {
  id: string;
  name: string;       // Required
  manifest: DeviceManifest;
}

interface DeviceManifest {
  Name: string;
  Description: string;
  Modes: string[];
  InternalVariables: InternalVariable[];
  ImpactedVariables: string[];
  InitState: string;
  WorkingStates: WorkingState[];
  Transitions: any[];
  APIs: API[];
}
```

### AuthResponseDto
```typescript
interface AuthResponseDto {
  userId: number;
  phone: string;
  username: string;
  token: string;      // Only returned on login
}
```

### RegisterResponseDto
```typescript
interface RegisterResponseDto {
  userId: number;
  phone: string;
  username: string;
}
```

### ChatRequestDto
```typescript
interface ChatRequestDto {
  sessionId: string;  // Required
  content: string;    // Required
}
```

### ChatSessionPo (Database Entity)
```typescript
interface ChatSessionPo {
  id: string;              // UUID
  userId: Long;            // Required
  title: string;
  createdAt: DateTime;
  updatedAt: DateTime;
}
```

### ChatMessagePo (Database Entity)
```typescript
interface ChatMessagePo {
  id: Long;                // Auto-increment
  sessionId: string;       // Required, FK to ChatSessionPo
  role: string;            // "user" | "assistant" | "tool"
  content: string;
  createdAt: DateTime;
}
```

### StreamResponseDto (SSE Response)
```typescript
interface StreamResponseDto {
  content: string;         // AI response text chunk
  command?: CommandDto;    // Optional command for frontend
}

interface CommandDto {
  type: string;            // e.g., "REFRESH_DATA"
  payload: Record<string, any>;  // Command parameters
}
```

---

## 8. Verification API

> All endpoints require authentication.

### 8.1 Execute Verification

**Endpoint:** `POST /api/verify`

Execute IoT system verification using NuSMV model checking.

**Request Body:**
```json
{
  "devices": [
    {
      "id": "device-001",
      "templateName": "AirConditioner",
      "label": "AC Cooler",
      "position": { "x": 100.0, "y": 200.0 },
      "state": "Off",
      "currentStateTrust": "trusted",
      "variables": [
        { "name": "temperature", "value": "24", "trust": "trusted" }
      ],
      "privacies": [
        { "name": "temperature", "privacy": "private" }
      ]
    }
  ],
  "rules": [
    {
      "id": "rule-001",
      "sources": [
        {
          "fromId": "AC Cooler",
          "fromLabel": "AC Cooler",
          "targetType": "variable",
          "property": "temperature",
          "relation": ">",
          "value": "28"
        }
      ],
      "toId": "device-001",
      "toApi": "turnOn",
      "templateLabel": "AirConditioner",
      "privacyDeviceId": null,
      "privacyContent": null
    }
  ],
  "specs": [
    {
      "id": "spec-001",
      "templateId": "1",
      "templateLabel": "always",
      "aConditions": [
        {
          "id": "cond-001",
          "side": "a",
          "deviceId": "device-001",
          "deviceLabel": "AC Cooler",
          "targetType": "state",
          "key": "state",
          "relation": "=",
          "value": "Cooling"
        }
      ],
      "ifConditions": [],
      "thenConditions": []
    }
  ],
  "saveTrace": true
}
```

#### Device Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | Unique device identifier |
| `templateName` | string | Yes | Device template name (e.g., "AirConditioner") |
| `label` | string | No | Display label |
| `position` | object | Yes | Device position `{x, y}` |
| `state` | string | No | Current state |
| `currentStateTrust` | string | No | "trusted" or "untrusted" |
| `variables` | array | No | List of variable states |
| `privacies` | array | No | List of privacy states |

#### VariableStateDto
```json
{ "name": "temperature", "value": "24", "trust": "trusted" }
```

#### PrivacyStateDto
```json
{ "name": "temperature", "privacy": "private" }
```

#### Rule Fields

| Field | Type | Description |
|-------|------|-------------|
| `sources` | array | IF conditions (triggers) |
| `sources[].fromId` | string | Source device ID |
| `sources[].targetType` | string | "api" or "variable" |
| `sources[].property` | string | API name or variable name |
| `sources[].relation` | string | "=", ">", "<", etc. |
| `sources[].value` | string | Condition value |
| `toId` | string | Target device ID |
| `toApi` | string | API to call on target |

#### Specification Fields

| Field | Type | Description |
|-------|------|-------------|
| `templateId` | string | "1"-"7" for spec types |
| `aConditions` | array | A-type spec conditions (always/eventually/never) |
| `ifConditions` | array | IF conditions (for B-type specs) |
| `thenConditions` | array | THEN conditions (for B-type specs) |
| `targetType` | string | "state", "variable", or "api" |
| `relation` | string | "=", "!=", ">", "<", etc. |

#### Seven Specification Types

| templateId | Type | NuSMV Syntax | Required Sides |
|------------|------|--------------|----------------|
| "1" | always | CTLSPEC AG(A) | aConditions only |
| "2" | eventually | CTLSPEC AF(A) | aConditions only |
| "3" | never | CTLSPEC AG !(A) | aConditions only |
| "4" | immediate | CTLSPEC AG(A → AX(B)) | ifConditions + thenConditions |
| "5" | response | CTLSPEC AG(A → AF(B)) | ifConditions + thenConditions |
| "6" | persistence | LTLSPEC G(A → F G(B)) | ifConditions + thenConditions |
| "7" | safety | CTLSPEC AG(untrusted → !(A)) | ifConditions + thenConditions |

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": {
    "safe": false,
    "traces": [
      {
        "id": 1,
        "userId": 1,
        "violatedSpecId": "spec-001",
        "violatedSpecJson": "{\"id\":\"spec-001\",...}",
        "states": [
          {
            "stateIndex": 0,
            "devices": [
              {
                "deviceId": "device-001",
                "deviceLabel": "AC Cooler",
                "templateName": "AirConditioner",
                "newState": "Off",
                "variables": [...],
                "trustPrivacy": [...],
                "privacies": [...]
              }
            ]
          }
        ],
        "createdAt": "2026-02-02T10:30:00"
      }
    ],
    "specResults": [false],
    "checkLogs": [
      "Generating NuSMV model...",
      "Model generated: /tmp/nusmv_xxx/model.smv",
      "Executing NuSMV verification...",
      "NuSMV execution completed successfully.",
      "Specification violation detected!",
      "Generated 1 violation trace(s)."
    ],
    "nusmvOutput": "..."
  }
}
```

#### VerificationResultDto

| Field | Type | Description |
|-------|------|-------------|
| `safe` | boolean | true if all specs satisfied |
| `traces` | array | List of TraceDto (violation traces) |
| `specResults` | array | Boolean result for each spec |
| `checkLogs` | array | Execution logs |
| `nusmvOutput` | string | Raw NuSMV output (truncated if >10000 chars) |

---

### 8.2 Get All Traces

**Endpoint:** `GET /api/verify/traces`

Get all traces for the current user.

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": [
    {
      "id": 1,
      "userId": 1,
      "violatedSpecId": "spec-001",
      "violatedSpecJson": "{\"id\":\"spec-001\",...}",
      "states": [...],
      "createdAt": "2026-02-02T10:30:00"
    }
  ]
}
```

---

### 8.3 Get Single Trace

**Endpoint:** `GET /api/verify/traces/{id}`

Get a specific trace by ID.

**Success Response (200):** Same format as above, returns single trace object.

**Error Responses:**

| Code | Message | Cause |
|------|---------|-------|
| 404 | Trace not found with id: {id} | Trace doesn't exist |

---

### 8.4 Delete Trace

**Endpoint:** `DELETE /api/verify/traces/{id}`

Delete a specific trace.

**Success Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": null
}
```

---

### 8.5 Trace DTO Structure

```typescript
interface TraceDto {
  id: Long;              // Database ID
  userId: Long;          // Owner user ID
  violatedSpecId: string;    // Violated spec ID
  violatedSpecJson: string;  // Full spec as JSON
  states: TraceStateDto[];   // State sequence
  createdAt: DateTime;   // Creation timestamp
}

interface TraceStateDto {
  stateIndex: number;    // 0, 1, 2, ...
  devices: TraceDeviceDto[];
}

interface TraceDeviceDto {
  deviceId: string;           // Device ID
  deviceLabel: string;        // Device display label
  templateName: string;       // Device template name
  newState: string;           // Current state (renamed from state)
  variables: TraceVariableDto[];
  trustPrivacy: TraceTrustPrivacyDto[];  // State trust/privacy (renamed from stateTrusts)
  privacies: TraceTrustPrivacyDto[];
}

interface TraceVariableDto {
  name: string;
  value: string;
  trust: string;         // "trusted" or "untrusted"
}

interface TraceTrustPrivacyDto {
  name: string;
  trust: boolean;        // true=trusted, false=untrusted
  privacy: string;       // "private" or "public"
}
```

---

### 8.6 Test Cases

#### Test Case 1: Safe Configuration (No Violation)

**Scenario**: AC is in Off state, temperature is 24, rule triggers when temperature > 28, spec checks that state != Cooling.

**Expected Result**: `safe: true`, `traces: []`

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [{"id":"device-001","templateName":"AirConditioner","label":"AC Cooler","position":{"x":100,"y":200},"state":"Off","variables":[{"name":"temperature","value":"24","trust":"trusted"}],"privacies":[{"name":"temperature","privacy":"private"}]}],
    "rules": [{"id":"rule-001","sources":[{"fromId":"AC Cooler","targetType":"variable","property":"temperature","relation":">","value":"28"}],"toId":"device-001","toApi":"turnOn"}],
    "specs": [{"id":"spec-001","aConditions":[{"deviceId":"device-001","targetType":"state","key":"state","relation":"!=","value":"Cooling"}]}],
    "saveTrace": false
  }'
```

---

#### Test Case 2: Unsafe Configuration (Violation Detected)

**Scenario**: Temperature can rise to 30, rule triggers when temperature > 28, spec requires state == Cooling.

**Expected Result**: `safe: false`, `traces` contains counterexample

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [{"id":"device-001","templateName":"AirConditioner","label":"AC Cooler","position":{"x":100,"y":200},"state":"Off","variables":[{"name":"temperature","value":"24","trust":"trusted"}],"privacies":[{"name":"temperature","privacy":"private"}]}],
    "rules": [{"id":"rule-001","sources":[{"fromId":"AC Cooler","targetType":"variable","property":"temperature","relation":">","value":"28"}],"toId":"device-001","toApi":"turnOn"}],
    "specs": [{"id":"spec-001","aConditions":[{"deviceId":"device-001","targetType":"state","key":"state","relation":"=","value":"Cooling"}]}],
    "saveTrace": true
  }'
```

**Expected Trace Flow**:
1. State: Off, Temperature: 24
2. State: Off, Temperature: 30 (temperature rises)
3. Rule triggers: temperature > 28
4. State: Cooling (API called)
5. Violation: state = Cooling (spec requires != Cooling)

---

#### Test Case 3: Multiple Devices

**Scenario**: Two AC units, one triggers the other.

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [
      {"id":"device-001","templateName":"AirConditioner","label":"AC Living Room","position":{"x":100,"y":200},"state":"Off","variables":[{"name":"temperature","value":"24","trust":"trusted"}],"privacies":[]},
      {"id":"device-002","templateName":"AirConditioner","label":"AC Bedroom","position":{"x":300,"y":200},"state":"Off","variables":[{"name":"temperature","value":"22","trust":"trusted"}],"privacies":[]}
    ],
    "rules": [{"id":"rule-001","sources":[{"fromId":"AC Living Room","targetType":"api","property":"turnOn"}],"toId":"device-002","toApi":"turnOn"}],
    "specs": [{"id":"spec-001","aConditions":[{"deviceId":"device-002","targetType":"state","key":"state","relation":"!=","value":"Heating"}]}],
    "saveTrace": true
  }'
```

---

### 8.7 Error Responses

| Code | Message | Cause |
|------|---------|-------|
| 400 | Validation failed | Invalid request data |
| 500 | Verification failed: {error} | NuSMV execution error |

---

## 9. NuSMV Configuration

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| NUSMV_PATH | NuSMV executable path | D:/NuSMV/NuSMV-2.7.1-win64/NuSMV-2.7.1-win64/bin/NuSMV.exe |
| NUSMV_PREFIX | Command prefix (e.g., "wsl" for Windows Subsystem Linux) | (empty) |

### Configuration in application.yaml

```yaml
nusmv:
  path: ${NUSMV_PATH:D:/NuSMV/NuSMV-2.7.1-win64/NuSMV-2.7.1-win64/bin/NuSMV.exe}
  command-prefix: ${NUSMV_PREFIX:}
```

### Supported Spec Types

| Type | Constraint | NuSMV Syntax |
|------|------------|--------------|
| A | holds forever | CTLSPEC AG(condition) |
| A | will happen later | CTLSPEC AF(condition) |
| A | never happens | CTLSPEC AG !(condition) |
| B | should happen at same time | CTLSPEC AG((A) -> AX(B)) |
| B | should happen later | CTLSPEC AG((A) -> AF(B)) |
| B | should happen forever | LTLSPEC G((A) -> F G(B))

# IoT-Verify Backend API Documentation

## Table of Contents

1. [Overview](#1-overview)
2. [Base URL & Authentication](#2-base-url--authentication)
3. [Response Format](#3-response-format)
4. [Data Models](#4-data-models)
5. [API Endpoints](#5-api-endpoints)
6. [Complete Workflow Examples](#6-complete-workflow-examples)
7. [Test Cases](#7-test-cases)
8. [Configuration](#8-configuration)
9. [Troubleshooting](#9-troubleshooting)
10. [Quick Reference](#10-quick-reference)

---

## 1. Overview

IoT-Verify is a smart home simulation and formal verification platform based on NuSMV model checking. This document provides comprehensive API documentation for the backend service.

### Core Features

| Feature | Description |
|---------|-------------|
| **Device Management** | Create, edit, and manage IoT device nodes and connections |
| **Rule Engine** | IFTTT-style rules for device interactions |
| **Specification Verification** | Formal verification using NuSMV |
| **Trace Analysis** | Counterexample visualization and analysis |
| **AI Assistant** | Natural language interface for device management |

### Tech Stack

- **Framework**: Spring Boot 3.x
- **Database**: MySQL + Redis
- **Authentication**: JWT
- **AI**: Volcengine Ark
- **Verification**: NuSMV

---

## 2. Base URL & Authentication

### Base URL

```
http://localhost:8080/api
```

### Authentication

All endpoints (except `/api/auth/**`) require JWT authentication.

#### Request Header

```
Authorization: Bearer <token>
```

#### Example

```bash
curl -X GET http://localhost:8080/api/board/nodes \
  -H "Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9..."
```

### Authentication Flow

1. **Register** → `POST /api/auth/register`
2. **Login** → `POST /api/auth/login` (get token)
3. **Use Token** for protected APIs
4. **Logout** → `POST /api/auth/logout` (blacklist token)

---

## 3. Response Format

### Success Response

All successful responses follow the unified `Result<T>` format:

```json
{
  "code": 200,
  "message": "success",
  "data": <T>
}
```

### Error Response

```json
{
  "code": <status-code>,
  "message": "Error message",
  "data": null
}
```

### HTTP Status Codes

| Code | Meaning | Description |
|------|---------|-------------|
| 200 | Success | Request completed successfully |
| 400 | Bad Request | Invalid request data or parameters |
| 401 | Unauthorized | Missing or invalid authentication token |
| 403 | Forbidden | Authenticated but lacks permission |
| 404 | Not Found | Resource does not exist |
| 409 | Conflict | Resource already exists or state conflict |
| 500 | Internal Server Error | Unexpected server error |
| 503 | Service Unavailable | External service temporarily unavailable |

### Exception Types

| Exception | Code | Usage |
|-----------|------|-------|
| `BadRequestException` | 400 | Invalid request data |
| `UnauthorizedException` | 401 | Authentication failure |
| `ForbiddenException` | 403 | Insufficient permissions |
| `ResourceNotFoundException` | 404 | Resource not found |
| `ConflictException` | 409 | Resource conflict |
| `InternalServerException` | 500 | Server error |
| `ServiceUnavailableException` | 503 | External service down |

---

## 4. Data Models

### 4.1 Device Models

#### DeviceNodeDto

```typescript
interface DeviceNodeDto {
  id: string;                    // Required, unique node ID
  templateName: string;          // Required, device template name
  label: string;                 // Display label
  position: {                    // Required
    x: number;                   // X coordinate
    y: number;                   // Y coordinate
  };
  state: string;                 // Current state
  width: number;                 // Node width in pixels
  height: number;                // Node height in pixels
  currentStateTrust?: string;    // "trusted" | "untrusted" (for verification)
  variables?: VariableStateDto[]; // Variable states (for verification)
  privacies?: PrivacyStateDto[];  // Privacy states (for verification)
}

interface VariableStateDto {
  name: string;      // Variable name (e.g., "temperature")
  value: string;     // Current value
  trust: string;     // "trusted" | "untrusted"
}

interface PrivacyStateDto {
  name: string;      // Privacy item name
  privacy: string;   // "private" | "public"
}
```

#### DeviceEdgeDto

```typescript
interface DeviceEdgeDto {
  id: string;        // Required, unique edge ID
  from: string;      // Required, source node ID
  to: string;        // Required, target node ID
  fromLabel: string; // Source node label
  toLabel: string;   // Target node label
  fromApi: string;   // Source API name
  toApi: string;     // Target API name
  fromPos: { x: number; y: number }; // Source position
  toPos: { x: number; y: number };   // Target position
}
```

#### DeviceTemplateDto

```typescript
interface DeviceTemplateDto {
  id: string;        // Template ID
  name: string;      // Required, template name
  manifest: DeviceManifest;
}

interface DeviceManifest {
  Name: string;                    // Template name
  Description: string;              // Template description
  Modes?: string[];                 // Device modes
  InternalVariables: InternalVariable[];
  ImpactedVariables: string[];      // Variables affected by state changes
  InitState: string;                // Initial state
  WorkingStates: WorkingState[];    // Available states
  Transitions?: any[];              // State transitions
  APIs: API[];                      // Available APIs
}

interface InternalVariable {
  Name: string;
  Description?: string;
  IsInside?: boolean;
  PublicVisible?: boolean;
  Trust?: string;       // "trusted" | "untrusted"
  Privacy?: string;     // "private" | "public"
  LowerBound?: number;
  UpperBound?: number;
  InitialValue?: string;
  NaturalChangeRate?: string;
  Values?: string[];    // For enum variables
}

interface WorkingState {
  Name: string;
  Description?: string;
  Dynamics?: Dynamic[];
  Invariant?: string;
  Trust: string;        // "trusted" | "untrusted"
  Privacy?: string;     // "private" | "public"
}

interface Dynamic {
  VariableName: string;
  ChangeRate: string;   // e.g., "[-1, 1]" for random change
}

interface API {
  Name: string;
  Description?: string;
  Signal?: boolean;     // Whether this is a signal API
  StartState: string;   // State before API call
  EndState: string;     // State after API call
  Trigger?: string;
  Assignments?: any[];
}
```

### 4.2 Rule Models

#### RuleDto

```typescript
interface RuleDto {
  id?: string;                   // Optional, auto-generated
  sources: SourceEntryDto[];     // Required, IF conditions (triggers)
  toId: string;                  // Required, target device ID
  toApi: string;                 // Required, target API name
  templateLabel?: string;        // Target device template label
  privacyDeviceId?: string;      // Privacy operation: target device ID
  privacyContent?: string;       // Privacy operation: content
}

interface SourceEntryDto {
  fromId: string;           // Source device ID
  fromLabel?: string;       // Source device label (for display)
  targetType: 'api' | 'variable';  // Trigger type
  fromApi?: string;         // API name (when targetType='api')
  property?: string;        // Variable name (when targetType='variable')
  relation?: string;        // Comparison: "=", ">", "<", ">=", "<=", "!="
  value?: string;           // Comparison value
}
```

### 4.3 Specification Models

#### SpecificationDto

```typescript
interface SpecificationDto {
  id: string;                    // Specification ID
  templateId: string;            // Required, "1"-"7" (see below)
  templateLabel?: string;        // Template label
  aConditions: SpecConditionDto[];   // A-type conditions
  ifConditions: SpecConditionDto[];  // IF conditions (for B-type)
  thenConditions: SpecConditionDto[]; // THEN conditions (for B-type)
}

interface SpecConditionDto {
  id: string;
  side: 'a' | 'if' | 'then';    // Condition side
  deviceId: string;              // Device node ID
  deviceLabel?: string;          // Device label
  targetType: 'state' | 'variable' | 'api'; // What to check
  key: string;                   // Property key (state/variable/API name)
  relation: string;              // Comparison operator
  value: string;                 // Expected value
}
```

#### Seven Specification Types

| templateId | Type | NuSMV Syntax | Required Sides | Description |
|------------|------|--------------|----------------|-------------|
| "1" | always | `CTLSPEC AG(A)` | aConditions | A holds forever |
| "2" | eventually | `CTLSPEC AF(A)` | aConditions | A will happen later |
| "3" | never | `CTLSPEC AG !(A)` | aConditions | A never happens |
| "4" | immediate | `CTLSPEC AG(A → AX(B))` | ifConditions + thenConditions | A → B (at same time) |
| "5" | response | `CTLSPEC AG(A → AF(B))` | ifConditions + thenConditions | A → ◇B (eventually) |
| "6" | persistence | `LTLSPEC G(A → F G(B))` | ifConditions + thenConditions | A → □B (forever after) |
| "7" | safety | `CTLSPEC AG(untrusted → !(A))` | ifConditions + thenConditions | untrusted → ¬A |

### 4.4 Trace Models

#### TraceDto

```typescript
interface TraceDto {
  id: Long;                   // Database ID
  userId: Long;               // Owner user ID
  violatedSpecId: string;     // Violated specification ID
  violatedSpecJson: string;   // Full specification as JSON
  states: TraceStateDto[];    // State sequence (counterexample)
  createdAt: DateTime;        // Creation timestamp
}

interface TraceStateDto {
  stateIndex: number;         // 0, 1, 2, ...
  devices: TraceDeviceDto[];
}

interface TraceDeviceDto {
  deviceId: string;           // Device ID
  deviceLabel: string;        // Device display label
  templateName: string;       // Device template name
  newState: string;           // Current state
  variables: TraceVariableDto[];
  trustPrivacy: TraceTrustPrivacyDto[];  // State trust/privacy info
  privacies: TraceTrustPrivacyDto[];
}

interface TraceVariableDto {
  name: string;
  value: string;
  trust: string;         // "trusted" | "untrusted"
}

interface TraceTrustPrivacyDto {
  name: string;
  trust: boolean;        // true=trusted, false=untrusted
  privacy: string;       // "private" | "public"
}
```

### 4.5 Verification Models

#### VerificationRequestDto

```typescript
interface VerificationRequestDto {
  devices: DeviceNodeDto[];      // Device nodes with runtime state
  rules: RuleDto[];              // IFTTT rules
  specs: SpecificationDto[];     // Specifications to verify
  isAttack: boolean;             // Enable attack mode
  intensity: number;             // Attack intensity (0-50)
}
```

#### VerificationResultDto

```typescript
interface VerificationResultDto {
  safe: boolean;                 // true if all specs satisfied
  traces: TraceDto[];            // Violation traces (if any)
  specResults: boolean[];        // Result for each spec
  checkLogs: string[];           // Execution logs
  nusmvOutput: string;           // Raw NuSMV output (truncated)
}
```

### Database Migration Note

If your database already has the `verification_task` table, add the column below:

```
ALTER TABLE verification_task ADD COLUMN nusmv_output TEXT;
```

### 4.6 Authentication Models

```typescript
interface RegisterRequestDto {
  phone: string;     // Format: 1[3-9]xxxxxxxxx
  username: string;  // 3-20 characters
  password: string;  // 6-20 characters
}

interface LoginRequestDto {
  phone: string;
  password: string;
}

interface AuthResponseDto {
  userId: Long;
  phone: string;
  username: string;
  token: string;     // Only on login
}

interface RegisterResponseDto {
  userId: Long;
  phone: string;
  username: string;
}
```

### 4.7 Chat Models

```typescript
interface ChatRequestDto {
  sessionId: string;  // Required
  content: string;    // Required
}

interface StreamResponseDto {
  content: string;         // AI response chunk
  command?: CommandDto;    // Optional command for frontend
}

interface CommandDto {
  type: string;                    // e.g., "REFRESH_DATA"
  payload: Record<string, any>;    // Command parameters
}

interface ChatSessionPo {
  id: string;              // UUID
  userId: Long;
  title: string;
  createdAt: DateTime;
  updatedAt: DateTime;
}

interface ChatMessagePo {
  id: Long;                // Auto-increment
  sessionId: string;       // FK to ChatSessionPo
  role: string;            // "user" | "assistant" | "tool"
  content: string;
  createdAt: DateTime;
}
```

---

## 5. API Endpoints

### 5.1 Authentication API

| Method | Endpoint | Description |
|--------|----------|-------------|
| POST | `/api/auth/register` | Register new user |
| POST | `/api/auth/login` | Login, get token |
| POST | `/api/auth/logout` | Logout, blacklist token |

#### Register

```bash
curl -X POST http://localhost:8080/api/auth/register \
  -H "Content-Type: application/json" \
  -d '{"phone":"13800138000","username":"testuser","password":"123456"}'
```

**Response (200):**
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

**Errors:**
| Code | Message | Cause |
|------|---------|-------|
| 409 | Phone number already registered: {phone} | Phone exists |
| 409 | Username already exists: {username} | Username exists |

#### Login

```bash
curl -X POST http://localhost:8080/api/auth/login \
  -H "Content-Type: application/json" \
  -d '{"phone":"13800138000","password":"123456"}'
```

**Response (200):**
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

**Errors:**
| Code | Message | Cause |
|------|---------|-------|
| 401 | Phone number or password is incorrect | Invalid credentials |

#### Logout

```bash
curl -X POST http://localhost:8080/api/auth/logout \
  -H "Authorization: Bearer <token>"
```

**Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": null
}
```

---

### 5.2 Board Storage API

All endpoints require authentication.

#### Device Nodes

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | `/api/board/nodes` | Get all nodes |
| POST | `/api/board/nodes` | Save nodes (replace all) |

**Get Nodes:**
```bash
curl -X GET http://localhost:8080/api/board/nodes \
  -H "Authorization: Bearer <token>"
```

**Save Nodes:**
```bash
curl -X POST http://localhost:8080/api/board/nodes \
  -H "Authorization: Bearer <token>" \
  -H "Content-Type: application/json" \
  -d '[{"id":"node-1","templateName":"AC Cooler","label":"AC-Living-Room","position":{"x":100,"y":200},"state":"Off","width":150,"height":100}]'
```

#### Device Edges

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | `/api/board/edges` | Get all edges |
| POST | `/api/board/edges` | Save edges (replace all) |

#### Rules

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | `/api/board/rules` | Get all rules |
| POST | `/api/board/rules` | Save rules (incremental update) |

**Rule Request Body:**
```json
[
  {
    "id": "rule-001",
    "sources": [
      {
        "fromId": "AC Living Room",
        "fromLabel": "AC Living Room",
        "targetType": "variable",
        "property": "temperature",
        "relation": ">",
        "value": "28"
      }
    ],
    "toId": "device-001",
    "toApi": "turnOn",
    "templateLabel": "AC Cooler"
  }
]
```

#### Specifications

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | `/api/board/specs` | Get all specifications |
| POST | `/api/board/specs` | Save specifications |

**Spec Request Body:**
```json
[
  {
    "id": "spec-001",
    "templateId": "1",
    "aConditions": [
      {
        "id": "cond-001",
        "side": "a",
        "deviceId": "device-001",
        "deviceLabel": "AC Living Room",
        "targetType": "state",
        "key": "state",
        "relation": "=",
        "value": "Cooling"
      }
    ]
  }
]
```

#### Device Templates

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | `/api/board/templates` | Get all templates |
| POST | `/api/board/templates` | Create template |
| DELETE | `/api/board/templates/{id}` | Delete template |

#### Layout & UI State

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | `/api/board/layout` | Get layout |
| POST | `/api/board/layout` | Save layout |
| GET | `/api/board/active` | Get active tabs |
| POST | `/api/board/active` | Save active tabs |

---

### 5.3 Chat API

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | `/api/chat/sessions` | Get all sessions |
| POST | `/api/chat/sessions` | Create session |
| GET | `/api/chat/sessions/{id}/messages` | Get messages |
| POST | `/api/chat/completions` | Send message (SSE) |
| DELETE | `/api/chat/sessions/{id}` | Delete session |

#### SSE Stream Example

```bash
curl -X POST http://localhost:8080/api/chat/completions \
  -H "Authorization: Bearer <token>" \
  -H "Content-Type: application/json" \
  -H "Accept: text/event-stream" \
  -d '{"sessionId":"550e8400-e29b-41d4-a716-446655440000","content":"Add a new AC device"}' \
  --stream
```

**SSE Format:**
```
data: {"content":"AI response chunk 1"}
data: {"content":"AI response chunk 2"}
data: {"command":{"type":"REFRESH_DATA","payload":{"target":"device_list"}}}
data: [DONE]
```

---

### 5.4 Verification API

| Method | Endpoint | Description |
|--------|----------|-------------|
| POST | `/api/verify` | Execute verification |
| GET | `/api/verify/traces` | Get all traces |
| GET | `/api/verify/traces/{id}` | Get single trace |
| DELETE | `/api/verify/traces/{id}` | Delete trace |

#### Execute Verification

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer <token>" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [
      {
        "id": "device-001",
        "templateName": "AC Cooler",
        "label": "AC Living Room",
        "position": {"x": 100, "y": 200},
        "state": "Off",
        "currentStateTrust": "trusted",
        "variables": [{"name": "temperature", "value": "24", "trust": "untrusted"}],
        "privacies": [{"name": "temperature", "privacy": "private"}]
      }
    ],
    "rules": [
      {
        "id": "rule-001",
        "sources": [
          {"fromId": "AC Living Room", "targetType": "variable", "property": "temperature", "relation": ">", "value": "28"}
        ],
        "toId": "device-001",
        "toApi": "turnOn"
      }
    ],
    "specs": [
      {
        "id": "spec-001",
        "templateId": "1",
        "aConditions": [
          {"deviceId": "device-001", "targetType": "state", "key": "state", "relation": "!=", "value": "Cooling"}
        ]
      }
    ],
    "isAttack": false,
    "intensity": 3
  }'
```

**Response (200):**
```json
{
  "code": 200,
  "message": "success",
  "data": {
    "safe": false,
    "traces": [
      {
        "id": 1,
        "violatedSpecId": "spec-001",
        "states": [...]
      }
    ],
    "specResults": [false],
    "checkLogs": [
      "Generating NuSMV model...",
      "Executing NuSMV verification...",
      "Specification violation detected!"
    ],
    "nusmvOutput": "..."
  }
}
```

---

## 6. Complete Workflow Examples

### Workflow: Register → Create Template → Create Device → Verify

#### Step 1: Register

```bash
curl -X POST http://localhost:8080/api/auth/register \
  -H "Content-Type: application/json" \
  -d '{"phone":"13800138001","username":"testuser1","password":"123456"}'
```

#### Step 2: Login

```bash
curl -X POST http://localhost:8080/api/auth/login \
  -H "Content-Type: application/json" \
  -d '{"phone":"13800138001","password":"123456"}'

# Save token
TOKEN="eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9..."
```

#### Step 3: Create Device Template

```bash
curl -X POST http://localhost:8080/api/board/templates \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "name": "AC Cooler",
    "manifest": {
      "Name": "AC Cooler",
      "Description": "Air conditioner for cooling",
      "Modes": ["Cooling", "Off"],
      "InternalVariables": [
        {
          "Name": "temperature",
          "Description": "Current temperature",
          "IsInside": false,
          "PublicVisible": true,
          "Trust": "untrusted",
          "Privacy": "private",
          "LowerBound": 16,
          "UpperBound": 30,
          "InitialValue": 24
        }
      ],
      "ImpactedVariables": ["temperature"],
      "InitState": "Off",
      "WorkingStates": [
        {
          "Name": "Off",
          "Description": "Device is off",
          "Trust": "trusted",
          "Privacy": "public",
          "Dynamics": [{"VariableName": "temperature", "ChangeRate": "0"}]
        },
        {
          "Name": "Cooling",
          "Description": "Device is cooling",
          "Trust": "trusted",
          "Privacy": "public",
          "Dynamics": [{"VariableName": "temperature", "ChangeRate": "-1"}]
        }
      ],
      "APIs": [
        {"Name": "turnOn", "StartState": "Off", "EndState": "Cooling"},
        {"Name": "turnOff", "StartState": "Cooling", "EndState": "Off"}
      ]
    }
  }'
```

#### Step 4: Create Device Instance

```bash
curl -X POST http://localhost:8080/api/board/nodes \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '[
    {
      "id": "device-001",
      "templateName": "AC Cooler",
      "label": "AC Living Room",
      "position": {"x": 100, "y": 200},
      "state": "Off",
      "width": 150,
      "height": 100
    }
  ]'
```

#### Step 5: Create Rule

```bash
curl -X POST http://localhost:8080/api/board/rules \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '[
    {
      "id": "rule-001",
      "sources": [
        {"fromId": "AC Living Room", "targetType": "variable", "property": "temperature", "relation": ">", "value": "28"}
      ],
      "toId": "device-001",
      "toApi": "turnOn"
    }
  ]'
```

#### Step 6: Create Specification

```bash
curl -X POST http://localhost:8080/api/board/specs \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '[
    {
      "id": "spec-001",
      "templateId": "1",
      "aConditions": [
        {"deviceId": "device-001", "targetType": "state", "key": "state", "relation": "!=", "value": "Cooling"}
      ]
    }
  ]'
```

#### Step 7: Execute Verification

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [
      {"id": "device-001", "templateName": "AC Cooler", "label": "AC Living Room", "position": {"x": 100, "y": 200}, "state": "Off", "variables": [{"name": "temperature", "value": "24", "trust": "untrusted"}], "privacies": []}
    ],
    "rules": [
      {"id": "rule-001", "sources": [{"fromId": "AC Living Room", "targetType": "variable", "property": "temperature", "relation": ">", "value": "28"}], "toId": "device-001", "toApi": "turnOn"}
    ],
    "specs": [
      {"id": "spec-001", "aConditions": [{"deviceId": "device-001", "targetType": "state", "key": "state", "relation": "!=", "value": "Cooling"}]}
    ],
    "isAttack": false,
    "intensity": 3
  }'
```

---

## 7. Test Cases

### Test Case 1: Safe Configuration (No Violation)

**Scenario:** AC is in Off state, temperature is 24, rule triggers when temperature > 28, spec checks that state != Cooling.

**Expected Result:** `safe: true`, `traces: []`

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [{"id":"device-001","templateName":"AC Cooler","label":"AC Cooler","position":{"x":100,"y":200},"state":"Off","variables":[{"name":"temperature","value":"24","trust":"trusted"}],"privacies":[{"name":"temperature","privacy":"private"}]}],
    "rules": [{"id":"rule-001","sources":[{"fromId":"AC Cooler","targetType":"variable","property":"temperature","relation":">","value":"28"}],"toId":"device-001","toApi":"turnOn"}],
    "specs": [{"id":"spec-001","templateId":"1","aConditions":[{"deviceId":"device-001","targetType":"state","key":"state","relation":"!=","value":"Cooling"}]}],
    "isAttack": false,
    "intensity": 3
  }'
```

---

### Test Case 2: Unsafe Configuration (Violation Detected)

**Scenario:** Temperature can rise to 30, rule triggers when temperature > 28, spec requires state != Cooling.

**Expected Result:** `safe: false`, `traces` contains counterexample

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [{"id":"device-001","templateName":"AC Cooler","label":"AC Cooler","position":{"x":100,"y":200},"state":"Off","variables":[{"name":"temperature","value":"24","trust":"untrusted"}],"privacies":[{"name":"temperature","privacy":"private"}]}],
    "rules": [{"id":"rule-001","sources":[{"fromId":"AC Cooler","targetType":"variable","property":"temperature","relation":">","value":"28"}],"toId":"device-001","toApi":"turnOn"}],
    "specs": [{"id":"spec-001","templateId":"1","aConditions":[{"deviceId":"device-001","targetType":"state","key":"state","relation":"!=","value":"Cooling"}]}],
    "isAttack": false,
    "intensity": 3
  }'
```

**Expected Trace Flow:**
1. State: Off, Temperature: 24
2. State: Off, Temperature: 30 (temperature rises)
3. Rule triggers: temperature > 28
4. State: Cooling (API called)
5. Violation: state = Cooling (spec requires != Cooling)

---

### Test Case 3: Multiple Devices

**Scenario:** Two AC units, one triggers the other.

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [
      {"id":"device-001","templateName":"AC Cooler","label":"AC Living Room","position":{"x":100,"y":200},"state":"Off","variables":[{"name":"temperature","value":"24","trust":"trusted"}],"privacies":[]},
      {"id":"device-002","templateName":"AC Cooler","label":"AC Bedroom","position":{"x":300,"y":200},"state":"Off","variables":[{"name":"temperature","value":"22","trust":"trusted"}],"privacies":[]}
    ],
    "rules": [{"id":"rule-001","sources":[{"fromId":"AC Living Room","targetType":"api","property":"turnOn"}],"toId":"device-002","toApi":"turnOn"}],
    "specs": [{"id":"spec-001","templateId":"1","aConditions":[{"deviceId":"device-002","targetType":"state","key":"state","relation":"!=","value":"Heating"}]}],
    "isAttack": false,
    "intensity": 3
  }'
```

---

### Test Case 4: IF-THEN Specification (Response Type)

**Scenario:** When living room AC turns on, bedroom AC should also turn on.

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [
      {"id":"device-001","templateName":"AC Cooler","label":"AC Living Room","position":{"x":100,"y":200},"state":"Off","variables":[],"privacies":[]},
      {"id":"device-002","templateName":"AC Cooler","label":"AC Bedroom","position":{"x":300,"y":200},"state":"Off","variables":[],"privacies":[]}
    ],
    "rules": [{"id":"rule-001","sources":[{"fromId":"AC Living Room","targetType":"api","property":"turnOn_a","relation":"=","value":"TRUE"}],"toId":"device-002","toApi":"turnOn"}],
    "specs": [{"id":"spec-001","templateId":"5","templateLabel":"response","ifConditions":[{"deviceId":"device-001","targetType":"api","key":"turnOn_a","relation":"=","value":"TRUE"}],"thenConditions":[{"deviceId":"device-002","targetType":"state","key":"state","relation":"=","value":"Cooling"}]}],
    "isAttack": false,
    "intensity": 3
  }'
```

---

## 8. Configuration

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `DB_URL` | Database connection URL | jdbc:mysql://localhost:3306/iot_verify |
| `DB_USERNAME` | Database username | root |
| `DB_PASSWORD` | Database password | - |
| `SERVER_PORT` | Server port | 8080 |
| `JWT_SECRET` | JWT signing secret (min 256 bits) | - |
| `JWT_EXPIRATION` | Token expiration in ms | 86400000 (24h) |
| `VOLCENGINE_API_KEY` | Volcengine AI API key | - |
| `VOLCENGINE_MODEL_ID` | AI model endpoint ID | - |
| `VOLCENGINE_BASE_URL` | Volcengine API base URL | - |
| `REDIS_HOST` | Redis server host | localhost |
| `REDIS_PORT` | Redis server port | 6379 |
| `NUSMV_PATH` | NuSMV executable path | - |

### application.yaml Example

```yaml
spring:
  datasource:
    url: ${DB_URL:jdbc:mysql://localhost:3306/iot_verify}
    username: ${DB_USERNAME:root}
    password: ${DB_PASSWORD:your_password}
  data:
    redis:
      host: ${REDIS_HOST:localhost}
      port: ${REDIS_PORT:6379}

server:
  port: ${SERVER_PORT:8080}

jwt:
  secret: ${JWT_SECRET:your-secret-key-min-256-bits}
  expiration: ${JWT_EXPIRATION:86400000}

volcengine:
  ark:
    api-key: ${VOLCENGINE_API_KEY}
    model-id: ${VOLCENGINE_MODEL_ID}
    base-url: ${VOLCENGINE_BASE_URL:https://ark.cn-beijing.volces.com/api/v3}

nusmv:
  path: ${NUSMV_PATH:D:/NuSMV/NuSMV-2.7.1-win64/bin/NuSMV.exe}
```

---

## 9. Troubleshooting

### NuSMV Not Found

**Error:** `NuSMV executable not found`

**Solution:**
1. Verify `nusmv.path` in `application.yaml`
2. Ensure NuSMV executable exists at specified path
3. On Windows, use forward slashes: `D:/NuSMV/bin/NuSMV.exe`

### Database Connection Issues

**Error:** Cannot connect to MySQL

**Solution:**
1. Ensure MySQL is running
2. Verify connection URL, username, password
3. Check firewall settings

### Token Issues

**Error:** `401 Unauthorized`

**Solution:**
1. Ensure token is not expired
2. Token is not blacklisted (after logout)
3. Token is properly formatted: `Bearer <token>`

### Verification Not Working

**Error:** All specs show `true` when expecting violations

**Solution:**
1. Check rule triggers are correctly defined
2. Verify device template has required states/APIs
3. Check NuSMV output in response for errors
4. Ensure `targetType`, `property`, `relation`, `value` are correct

### Trace Empty

**Error:** `safe: false` but traces array is empty

**Solution:**
1. Verify the specification was actually violated
2. Check `violatedSpecId` matches your spec ID
3. Look at `nusmvOutput` for debugging info

---

## 10. Quick Reference

### Target Types

| targetType | Description | Example |
|------------|-------------|---------|
| `state` | Check device state | `state = "Cooling"` |
| `variable` | Check variable value | `temperature > 28` |
| `api` | Check API signal | `turnOn_a = "TRUE"` |

### Relation Operators

| relation | Description |
|----------|-------------|
| `=` | Equals |
| `!=` | Not equals |
| `>` | Greater than |
| `>=` | Greater than or equal |
| `<` | Less than |
| `<=` | Less than or equal |

### Specification Types Quick Reference

| templateId | Type | Syntax | Required |
|------------|------|--------|----------|
| "1" | always | AG(A) | aConditions |
| "2" | eventually | AF(A) | aConditions |
| "3" | never | AG !(A) | aConditions |
| "4" | immediate | AG(A → AX(B)) | if + then |
| "5" | response | AG(A → AF(B)) | if + then |
| "6" | persistence | G(A → F G(B)) | if + then |
| "7" | safety | AG(untrusted → !(A)) | if + then |

### Postman Collection

Import the following collection for complete workflow testing:

**File:** `IoT-Verify-Workflow.postman_collection.json`

**Workflow:**
1. Register → Login
2. Create Device Template
3. Create Device Node
4. Create Rules
5. Create Specifications
6. Execute Verification
7. View/Delete Traces
8. Logout

---

## Postman Collection

### Collection Variables

| Variable | Description |
|----------|-------------|
| `baseUrl` | Base URL (`http://localhost:8080/api`) |
| `token` | JWT token (auto-set after login) |
| `userId` | User ID (auto-set after register/login) |
| `phone` | Test phone number |
| `username` | Test username |
| `password` | Test password |
| `templateId` | Created template ID |
| `deviceId1`, `deviceId2` | Created device IDs |
| `ruleId` | Created rule ID |
| `specId` | Created specification ID |

### Import Instructions

1. Open Postman
2. Click Import → Select `IoT-Verify-Workflow.postman_collection.json`
3. Set collection variables (phone, username, password)
4. Run the collection in order

---

## Implementation Status

| Feature | Status | Notes |
|---------|--------|-------|
| Generate NuSMV Model | ✅ Done | `NusmvModelGeneratorServiceImpl` |
| Execute NuSMV | ✅ Done | `NusmvExecutorServiceImpl` |
| Parse Counterexample | ✅ Done | `generateTraceStates()` |
| Trace Persistence | ✅ Done | `TraceRepository` |
| API Verification | ✅ Done | `VerificationServiceImpl` |
| Random Simulation | ❌ Not Implemented | Future enhancement |
| Auto Rule Fix | ❌ Not Implemented | Future enhancement |

---

## License

MIT License

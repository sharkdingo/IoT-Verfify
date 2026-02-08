# IoT-Verifier Testing Guide

## Overview

This document provides test cases and troubleshooting guidance for the IoT-Verifier backend service.

> **Note**: For complete API documentation, see [API-DOCUMENTATION.md](API-DOCUMENTATION.md).

**Base URL**: `http://localhost:8080`

**Authentication**: All endpoints require JWT authentication via `Authorization` header.

```
Authorization: Bearer <your-jwt-token>
```

---

## Test Cases

### Test Case 1: Safe Configuration (No Violation)

**Scenario**: AC is in Off state, temperature is 24, rule triggers when temperature > 28, spec checks that state != Cooling.

**Expected Result**: `safe: true`, `traces: []`

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [
      {
        "id": "device-001",
        "templateName": "AirConditioner",
        "label": "AC Cooler",
        "position": {"x": 100.0, "y": 200.0},
        "state": "Off",
        "variables": [{"name": "temperature", "value": "24", "trust": "trusted"}],
        "privacies": [{"name": "temperature", "privacy": "private"}]
      }
    ],
    "rules": [
      {
        "id": "rule-001",
        "sources": [
          {"fromId": "AC Cooler", "targetType": "variable", "property": "temperature", "relation": ">", "value": "28"}
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

---

### Test Case 2: Unsafe Configuration (Violation Detected)

**Scenario**: Temperature can rise to 30, rule triggers when temperature > 28, spec requires state == Cooling.

**Expected Result**: `safe: false`, `traces` contains counterexample

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [
      {
        "id": "device-001",
        "templateName": "AirConditioner",
        "label": "AC Cooler",
        "position": {"x": 100.0, "y": 200.0},
        "state": "Off",
        "variables": [{"name": "temperature", "value": "24", "trust": "trusted"}],
        "privacies": [{"name": "temperature", "privacy": "private"}]
      }
    ],
    "rules": [
      {
        "id": "rule-001",
        "sources": [
          {"fromId": "AC Cooler", "targetType": "variable", "property": "temperature", "relation": ">", "value": "28"}
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
          {"deviceId": "device-001", "targetType": "state", "key": "state", "relation": "=", "value": "Cooling"}
        ]
      }
    ],
    "isAttack": false,
    "intensity": 3
  }'
```

**Expected Trace Flow**:
1. State: Off, Temperature: 24
2. State: Off, Temperature: 30 (temperature rises)
3. Rule triggers: temperature > 28
4. State: Cooling (API called)
5. Violation: state = Cooling (spec requires != Cooling)

---

### Test Case 3: Multiple Devices

**Scenario**: Two AC units, one triggers the other.

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [
      {
        "id": "device-001",
        "templateName": "AirConditioner",
        "label": "AC Living Room",
        "position": {"x": 100.0, "y": 200.0},
        "state": "Off",
        "variables": [{"name": "temperature", "value": "24", "trust": "trusted"}],
        "privacies": []
      },
      {
        "id": "device-002",
        "templateName": "AirConditioner",
        "label": "AC Bedroom",
        "position": {"x": 300.0, "y": 200.0},
        "state": "Off",
        "variables": [{"name": "temperature", "value": "22", "trust": "trusted"}],
        "privacies": []
      }
    ],
    "rules": [
      {
        "id": "rule-001",
        "sources": [
          {"fromId": "AC Living Room", "targetType": "api", "property": "turnOn"}
        ],
        "toId": "device-002",
        "toApi": "turnOn"
      }
    ],
    "specs": [
      {
        "id": "spec-001",
        "templateId": "1",
        "aConditions": [
          {"deviceId": "device-002", "targetType": "state", "key": "state", "relation": "!=", "value": "Heating"}
        ]
      }
    ],
    "isAttack": false,
    "intensity": 3
  }'
```

---

### Test Case 4: IF-THEN Specification (Response Type)

**Scenario**: When living room AC turns on, bedroom AC should also turn on within 2 time units.

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [
      {
        "id": "device-001",
        "templateName": "AirConditioner",
        "label": "AC Living Room",
        "position": {"x": 100.0, "y": 200.0},
        "state": "Off",
        "variables": [],
        "privacies": []
      },
      {
        "id": "device-002",
        "templateName": "AirConditioner",
        "label": "AC Bedroom",
        "position": {"x": 300.0, "y": 200.0},
        "state": "Off",
        "variables": [],
        "privacies": []
      }
    ],
    "rules": [
      {
        "id": "rule-001",
        "sources": [
          {"fromId": "AC Living Room", "targetType": "api", "property": "turnOn_a", "relation": "=", "value": "TRUE"}
        ],
        "toId": "device-002",
        "toApi": "turnOn"
      }
    ],
    "specs": [
      {
        "id": "spec-001",
        "templateId": "5",
        "templateLabel": "response",
        "ifConditions": [
          {"deviceId": "device-001", "targetType": "api", "key": "turnOn_a", "relation": "=", "value": "TRUE"}
        ],
        "thenConditions": [
          {"deviceId": "device-002", "targetType": "state", "key": "state", "relation": "=", "value": "Cooling"}
        ]
      }
    ],
    "isAttack": false,
    "intensity": 3
  }'
```

---

## Error Responses

### 400 Bad Request

```json
{
  "code": 400,
  "message": "Validation failed",
  "data": null
}
```

### 401 Unauthorized

```json
{
  "code": 401,
  "message": "Unauthorized",
  "data": null
}
```

### 500 Internal Server Error

```json
{
  "code": 500,
  "message": "Internal server error",
  "data": null
}
```

---

## Troubleshooting

### NuSMV Not Found

If you see an error like "NuSMV executable not found", check:

1. The `nusmv.path` configuration in `application.yaml`
2. The NuSMV executable exists at the specified path
3. On Windows, use forward slashes or double backslashes in the path

Example configuration for Windows:
```yaml
nusmv:
  path: D:/NuSMV/NuSMV-2.7.1-win64/NuSMV-2.7.1-win64/bin/NuSMV.exe
```

### Database Connection Issues

Ensure MySQL is running and the connection details are correct in `application.yaml`.

### JWT Token

To get a JWT token, use the login endpoint:
- POST `/api/auth/login`
- POST `/api/auth/register`

### Specification Not Satisfied

If all specifications are marked as `true` but you expect violations:
1. Check that the rule triggers are correctly defined (targetType, property, relation, value)
2. Verify the device template has the required states and transitions
3. Check NuSMV output for parsing errors

### Trace Empty

If `safe: false` but traces array is empty:
1. Verify the specification was actually violated
2. Check that `violatedSpecId` in the response matches your spec ID
3. Look at `nusmvOutput` in the response for debugging info

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

## Quick Reference: Specification Types

| templateId | Type | Syntax | Required Conditions |
|------------|------|--------|---------------------|
| "1" | always | AG(A) | aConditions |
| "2" | eventually | AF(A) | aConditions |
| "3" | never | AG !(A) | aConditions |
| "4" | immediate | AG(A → AX(B)) | ifConditions + thenConditions |
| "5" | response | AG(A → AF(B)) | ifConditions + thenConditions |
| "6" | persistence | G(A → F G(B)) | ifConditions + thenConditions |
| "7" | safety | AG(untrusted → !(A)) | ifConditions + thenConditions |

## Quick Reference: Target Types

| targetType | Description | Example |
|------------|-------------|---------|
| `state` | Check device state | `state = "Cooling"` |
| `variable` | Check variable value | `temperature > 28` |
| `api` | Check API signal | `turnOn_a = TRUE` |

## Quick Reference: Relations

| relation | Description |
|----------|-------------|
| `=` | Equals |
| `!=` | Not equals |
| `>` | Greater than |
| `>=` | Greater than or equal |
| `<` | Less than |
| `<=` | Less than or equal |

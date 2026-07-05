# AI Tools

The IoT-Verify AI assistant is backed by any OpenAI-compatible LLM endpoint (configured via `llm.*`; see [configuration.md](../getting-started/configuration.md)) and uses tool/function-calling: the model selects a tool by its snake_case `name`, and the backend runs the matching implementation. Each tool declares itself via a vendor-neutral `LlmToolSpec` (`getDefinition()`); the `LlmProvider` adapter translates specs and messages to the underlying SDK, so tools never depend on an SDK type. All 30 tools are Spring beans that implement `AiTool` (most extend `AbstractAiTool`) and are dispatched at runtime by `AiToolManager`. `AiToolManager.execute()` wraps every dispatch in a catch-all that logs the exception and returns a generic `Tool execution failed due to an internal error` message, so raw exception detail is never leaked back to the model.

**Tool responses are not the REST `Result<T>` envelope.** Internally each tool returns
a raw JSON string (built by `AiToolResponseHelper`): on error, `{ "error", "errorCode",
"status" }`; on success, a tool-specific body. That envelope only appears when a tool is
also exposed as an HTTP endpoint — e.g. `/api/board/*/recommend`, where the controller
inspects the tool's JSON (`throwIfToolError`) and wraps the result in
`Result<Map<String, Object>>` (see [board.md](board.md) and
[overview.md](overview.md)).

Verified against code on 2026-07-05. Source: component/aitool/, component/ai/.

## Argument Contract Notes

Tool argument schemas are JSON objects declared by each tool's `getDefinition()`.
The backend validates again at execution time and returns `{ "error", "errorCode",
"status" }` for invalid arguments.

| Tool | Required / important arguments | Notes |
| --- | --- | --- |
| `add_device` | `templateName`, `label`, optional `x`, `y`, `state`, `w`, `h` | Mutates the board and triggers a `REFRESH_DATA` command for `device_list`. |
| `delete_device` | One of `identifier`, `label`, or `id` | `identifier` is preferred; `label` and `id` are backward-compatible alternatives. Mutates the board and refreshes `device_list`. |
| `check_duplicate_rule` | `newRule` | `newRule` is the candidate automation rule object to compare with existing rules. |
| `manage_rule` | `action`; for `add`, also `conditions` and `command`; for `delete`, a rule identifier | Mutates rules and refreshes `rule_list`. |
| `recommend_related_devices` | `devices`, `templates` | Both must be arrays. The tool recommends templates; it does not mutate the board. |
| `manage_spec` | `action`; for `add`, spec metadata plus condition lists; for `delete`, a spec identifier | Conditions use `targetType` in `state`, `variable`, `api`, `trust`, `privacy`. State conditions use `targetType: "state"`, `key: "state"`, and a `value` from the device's states. Mutates specs and refreshes `spec_list`. |
| `recommend_specifications` | optional `maxRecommendations`, `category` | Recommendations use the same condition model as `manage_spec`; `templateId` is required in the generated JSON and must be one of `"1"` through `"7"`; `currentState` is not a valid condition key. |
| `add_template` | `name`, `manifest` | `manifest` must define modes/initial state/working states consistently. Mutates templates and refreshes `template_list`. |
| `delete_template` | template identifier | Mutates templates and refreshes `template_list`. |
| Async task tools | `taskId` for status/cancel operations | Start tools return a task id; polling/cancel tools require it. |
| Trace tools | `traceId` or `simulationId` depending on domain | Verification traces use `traceId`; simulation traces use `simulationId`. |

Successful mutating tools are translated by the chat service into frontend refresh
commands: device mutations refresh `device_list`, rule mutations refresh `rule_list`,
spec mutations refresh `spec_list`, and template mutations refresh `template_list`.

## Board

| Tool | Summary |
| --- | --- |
| `board_overview` | Return an overview of the current board: device, rule-derived edge, rule, and specification summaries. Edge summaries are derived from rule conditions and commands, matching the Board UI's visible connections. |

## Devices / Nodes

| Tool | Summary |
| --- | --- |
| `add_device` | Add a new device to the canvas from a template. |
| `delete_device` | Delete a device node, resolved by label or node id. |
| `search_devices` | Search devices on the canvas, filtering by template type or name. |

## Rules

| Tool | Summary |
| --- | --- |
| `check_duplicate_rule` | Use AI to check whether a new rule duplicates existing rules by analyzing its trigger conditions and action. |
| `list_rules` | List automation rules on the current board, optionally filtered by keyword. |
| `manage_rule` | Add or delete an automation rule. |
| `recommend_related_devices` | Use AI to recommend new devices from available templates that enhance the IoT system. |
| `recommend_rules` | Use AI to analyze device capabilities (APIs, variables, states) and recommend automation rules for linkage, security, energy-saving, or comfort scenarios. |

Rule recommendations use board device labels in `conditions[].deviceName`,
`command.deviceName`, and `command.contentDevice`. Legacy node ids are accepted only as a
backend compatibility fallback and are normalized back to labels before returning.
Each returned condition must include a non-empty `value`; invalid relation operators are
filtered out by the tool validator before the result is returned.

## Specifications

| Tool | Summary |
| --- | --- |
| `list_specs` | List formal specifications on the current board. |
| `manage_spec` | Add or delete a formal specification. |
| `recommend_specifications` | Use AI to analyze board devices, rules, and existing specs and recommend new formal specifications for correctness, safety, and reliability. |

Specification recommendations also use device labels (`deviceId`/`deviceLabel` are
normalized to the board label) and filter out recommendations with illegal template ids
or unresolved devices before returning them to the frontend. The prompt schema,
tool-side validator, and backend DTO share the same core contract:
`templateId in "1".."7"`, `targetType in state|variable|api|trust|privacy`, relation in
the supported operator enum, and non-empty `value`.

## Templates

| Tool | Summary |
| --- | --- |
| `add_template` | Add a custom device template defining states, transitions, and APIs. |
| `delete_template` | Delete a device template by its template id. |
| `list_templates` | List available device templates (modes, variables, transitions, and APIs). |

## Simulation

| Tool | Summary |
| --- | --- |
| `simulate_model` | Run a synchronous NuSMV random simulation on the board, returning a sequence of states over N steps. |
| `simulate_model_async` | Start an asynchronous NuSMV simulation task and return a taskId for polling. |
| `simulate_task_status` | Query the status and progress of an async simulation task by taskId. |
| `cancel_simulate_task` | Cancel an async simulation task by taskId. |
| `list_simulation_traces` | List all saved simulation traces for the current user. |
| `get_simulation_trace` | Get a saved simulation trace by simulationId, including its state sequence. |
| `delete_simulation_trace` | Delete a saved simulation trace by simulationId. |

## Verification & Fix

| Tool | Summary |
| --- | --- |
| `verify_model` | Run synchronous NuSMV formal verification on the board and report whether the model is safe plus any property-violation details. |
| `verify_model_async` | Start an asynchronous NuSMV verification task and return a taskId for polling. |
| `verify_task_status` | Query the status and progress of an async verification task by taskId. |
| `cancel_verify_task` | Cancel an async verification task by taskId. |
| `list_traces` | List all saved verification counterexample traces (each a state sequence leading to a violation). |
| `get_trace` | Get a saved verification trace by traceId, including its state sequence. |
| `delete_trace` | Delete a saved verification trace by traceId. |
| `fix_violation` | Analyze a violation trace to localize fault rules and suggest fixes via parameter, condition, or disable strategies (needs a traceId). |

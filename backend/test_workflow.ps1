# ============================================================
# IoT-Verify End-to-End Workflow Test
# 覆盖: Auth / Board CRUD / Verification / Trace
# ============================================================

$BASE_URL = "http://localhost:8080/api"
$PHONE    = "13800138000"
$USERNAME = "testuser"
$PASSWORD = "Test123456"

$PASS = 0; $FAIL = 0; $SKIP = 0

# ==================== 工具函数 ====================

function PostJson($url, $bodyObj, $headers = @{}) {
  # Use -InputObject to avoid pipeline array unwrapping (single-element arrays stay as arrays)
  $json = ConvertTo-Json -InputObject $bodyObj -Depth 50
  return Invoke-RestMethod -Method Post -Uri $url -Headers $headers -ContentType "application/json" -Body $json
}
function GetJson($url, $headers = @{}) {
  return Invoke-RestMethod -Method Get -Uri $url -Headers $headers
}
function DeleteJson($url, $headers = @{}) {
  return Invoke-RestMethod -Method Delete -Uri $url -Headers $headers
}

function Assert-True($condition, $msg) {
  if ($condition) {
    Write-Host "  [PASS] $msg" -ForegroundColor Green
    $script:PASS++
  } else {
    Write-Host "  [FAIL] $msg" -ForegroundColor Red
    $script:FAIL++
  }
}
function Assert-Equal($actual, $expected, $msg) {
  Assert-True ($actual -eq $expected) "$msg (expected=$expected, actual=$actual)"
}
function Skip-Step($msg) {
  Write-Host "  [SKIP] $msg" -ForegroundColor Yellow
  $script:SKIP++
}

function Get-TemplateName($template) {
  if ($null -eq $template) { return $null }
  if ($template.name -and -not [string]::IsNullOrWhiteSpace($template.name)) {
    return [string]$template.name
  }
  if ($template.manifest -and $template.manifest.Name -and -not [string]::IsNullOrWhiteSpace($template.manifest.Name)) {
    return [string]$template.manifest.Name
  }
  return $null
}

function Resolve-TemplateName($templates, [string[]]$candidates) {
  $names = @(
    @($templates) |
      ForEach-Object { Get-TemplateName $_ } |
      Where-Object { -not [string]::IsNullOrWhiteSpace($_) }
  )

  foreach ($candidate in @($candidates)) {
    if ([string]::IsNullOrWhiteSpace($candidate)) { continue }
    $found = $names | Where-Object { $_.Equals($candidate, [System.StringComparison]::OrdinalIgnoreCase) } | Select-Object -First 1
    if ($found) { return $found }
  }

  foreach ($candidate in @($candidates)) {
    if ([string]::IsNullOrWhiteSpace($candidate)) { continue }
    $found = $names | Where-Object {
      $_.IndexOf($candidate, [System.StringComparison]::OrdinalIgnoreCase) -ge 0 -or
      $candidate.IndexOf($_, [System.StringComparison]::OrdinalIgnoreCase) -ge 0
    } | Select-Object -First 1
    if ($found) { return $found }
  }

  return $null
}

function Convert-NodesToVerifyDevices($nodes) {
  $result = @()
  foreach ($node in @($nodes)) {
    if ($null -eq $node) { continue }
    $result += @{
      varName = $node.id
      templateName = $node.templateName
      state = $node.state
      currentStateTrust = $node.currentStateTrust
      variables = if ($null -ne $node.variables) { @($node.variables) } else { @() }
      privacies = if ($null -ne $node.privacies) { @($node.privacies) } else { @() }
    }
  }
  return $result
}

Write-Host "=========================================="
Write-Host " IoT-Verify End-to-End Workflow Test"
Write-Host "=========================================="

# ==================== 1. Auth ====================

Write-Host "`n--- Step 1: Register ---"
# RegisterRequestDto: phone(@NotBlank, 1[3-9]\d{9}), username(@NotBlank, 3-20), password(@NotBlank, 6-20)
try {
  $REG = PostJson "$BASE_URL/auth/register" @{ phone=$PHONE; username=$USERNAME; password=$PASSWORD }
  Assert-Equal $REG.code 200 "Register returns 200"
  Assert-True ($REG.data.userId -gt 0) "Register returns userId"
} catch {
  Write-Host "  [INFO] Register failed (user may already exist): $($_.Exception.Message)" -ForegroundColor Cyan
}

Write-Host "`n--- Step 2: Login ---"
# LoginRequestDto: phone(@NotBlank), password(@NotBlank)
$LOGIN = PostJson "$BASE_URL/auth/login" @{ phone=$PHONE; password=$PASSWORD }
Assert-Equal $LOGIN.code 200 "Login returns 200"
Assert-True ($LOGIN.data.token.Length -gt 10) "Login returns valid token"
$TOKEN = $LOGIN.data.token
$AUTH = @{ Authorization = "Bearer $TOKEN" }

Write-Host "`n--- Step 3: Access without token (expect 401) ---"
try {
  GetJson "$BASE_URL/board/templates" | Out-Null
  Assert-True $false "Should have thrown 401"
} catch {
  Assert-True ($_.Exception.Message -match "401") "Unauthenticated request returns 401"
}

# ==================== 2. Board CRUD ====================

Write-Host "`n--- Step 4: Get Templates ---"
$TPL = GetJson "$BASE_URL/board/templates" $AUTH
Assert-Equal $TPL.code 200 "Get templates returns 200"
$TPL_COUNT = @($TPL.data).Count
Assert-True ($TPL_COUNT -gt 0) "Template count > 0 (actual: $TPL_COUNT)"
$LIGHT_TEMPLATE = Resolve-TemplateName $TPL.data @("Light")
$TEMP_TEMPLATE = Resolve-TemplateName $TPL.data @("Temperature Sensor", "Temp Sensor", "Thermostat")
Assert-True (-not [string]::IsNullOrWhiteSpace($LIGHT_TEMPLATE)) "Resolved Light template name ($LIGHT_TEMPLATE)"
Assert-True (-not [string]::IsNullOrWhiteSpace($TEMP_TEMPLATE)) "Resolved sensor template name ($TEMP_TEMPLATE)"
if ([string]::IsNullOrWhiteSpace($LIGHT_TEMPLATE) -or [string]::IsNullOrWhiteSpace($TEMP_TEMPLATE)) {
  throw "Required templates were not found. Need at least 'Light' and 'Temperature Sensor' (or alias)."
}

Write-Host "`n--- Step 5: Save & Get Nodes ---"
# DeviceNodeDto: id(@NotBlank), templateName(@NotBlank), label(@NotBlank), position(@Valid @NotNull {x:Double, y:Double}), state(@NotBlank), width(@NotNull Integer), height(@NotNull Integer), currentStateTrust, variables, privacies
$NODES = @(
  @{
    id="light_1"; templateName=$LIGHT_TEMPLATE; label="My Light"
    position=@{ x=100.0; y=100.0 }
    state="on"; width=120; height=80
    currentStateTrust="trusted"
    variables=@()
    privacies=@()
  },
  @{
    id="tempsensor_1"; templateName=$TEMP_TEMPLATE; label="Temp Sensor"
    position=@{ x=300.0; y=100.0 }
    # For sensor-like templates without modes, backend ignores state during SMV generation.
    state="monitoring"; width=120; height=80
    currentStateTrust="untrusted"
    variables=@(@{ name="temperature"; value="25"; trust="untrusted" })
    privacies=@(@{ name="temperature"; privacy="public" })
  }
)
$NODES_RESP = PostJson "$BASE_URL/board/nodes" $NODES $AUTH
Assert-Equal $NODES_RESP.code 200 "Save nodes returns 200"
Assert-Equal @($NODES_RESP.data).Count 2 "Saved 2 nodes"
$GET_NODES = GetJson "$BASE_URL/board/nodes" $AUTH
Assert-Equal @($GET_NODES.data).Count 2 "Get nodes returns 2"

Write-Host "`n--- Step 6: Save & Get Edges ---"
# DeviceEdgeDto: id(@NotBlank), from(@NotBlank), to(@NotBlank), fromLabel(@NotBlank), toLabel(@NotBlank), fromPos(@Valid @NotNull {x:Double,y:Double}), toPos(@Valid @NotNull {x:Double,y:Double})
$EDGES = @(
  @{
    id="edge_1"; from="light_1"; to="tempsensor_1"
    fromLabel="My Light"; toLabel="Temp Sensor"
    fromPos=@{ x=220.0; y=140.0 }
    toPos=@{ x=300.0; y=140.0 }
  }
)
$EDGES_RESP = PostJson "$BASE_URL/board/edges" $EDGES $AUTH
Assert-Equal $EDGES_RESP.code 200 "Save edges returns 200"
$GET_EDGES = GetJson "$BASE_URL/board/edges" $AUTH
Assert-Equal @($GET_EDGES.data).Count 1 "Get edges returns 1"

Write-Host "`n--- Step 7: Save & Get Rules ---"
# RuleDto: id(Long), conditions(@NotNull List<Condition>), command(@NotNull Command), ruleString
# Condition: deviceName, attribute, relation, value
# Command: deviceName, action, contentDevice, content
$RULES = @(
  @{
    conditions = @(
      @{ deviceName=$TEMP_TEMPLATE; attribute="temperature"; relation=">"; value="30" }
    )
    command = @{ deviceName=$LIGHT_TEMPLATE; action="off" }
  }
)
$RULES_RESP = PostJson "$BASE_URL/board/rules" $RULES $AUTH
Assert-Equal $RULES_RESP.code 200 "Save rules returns 200"
$GET_RULES = GetJson "$BASE_URL/board/rules" $AUTH
Assert-True (@($GET_RULES.data).Count -ge 1) "Get rules returns >= 1"

Write-Host "`n--- Step 8: Save & Get Specs ---"
# SpecificationDto: id(@NotBlank), templateId(@NotBlank), templateLabel(@NotBlank), aConditions(@NotNull List), ifConditions(@NotNull List), thenConditions(@NotNull List)
# SpecConditionDto: id, side('a'|'if'|'then'), deviceId, deviceLabel, targetType('state'|'variable'|'api'|'trust'|'privacy'), key, relation, value
$SPECS = @(
  @{
    id="spec_1"; templateId="1"; templateLabel="Safety"
    aConditions=@()
    ifConditions=@(
      @{ id="c1"; side="if"; deviceId="light_1"; deviceLabel="My Light"; targetType="state"; key="state"; relation="="; value="on" }
    )
    thenConditions=@(
      @{ id="c2"; side="then"; deviceId="tempsensor_1"; deviceLabel="Temp Sensor"; targetType="variable"; key="temperature"; relation="<"; value="40" }
    )
  }
)
$SPECS_RESP = PostJson "$BASE_URL/board/specs" $SPECS $AUTH
Assert-Equal $SPECS_RESP.code 200 "Save specs returns 200"
$GET_SPECS = GetJson "$BASE_URL/board/specs" $AUTH
Assert-Equal @($GET_SPECS.data).Count 1 "Get specs returns 1"

Write-Host "`n--- Step 9: Save & Get Layout ---"
# BoardLayoutDto: input(PanelPosition{x,y}), status(PanelPosition{x,y}), canvasPan(CanvasPan{x,y}), canvasZoom(Double), dockState(DockStateWrapper{input:DockState, status:DockState})
# DockState: isDocked(Boolean), side(String), lastPos(PanelPosition{x,y})
$LAYOUT = @{
  input=@{ x=24.0; y=24.0 }
  status=@{ x=1040.0; y=80.0 }
  canvasPan=@{ x=0.0; y=0.0 }
  canvasZoom=1.0
  dockState=@{
    input=@{ isDocked=$false; side=$null; lastPos=@{ x=24.0; y=24.0 } }
    status=@{ isDocked=$false; side=$null; lastPos=@{ x=1040.0; y=80.0 } }
  }
}
$LAYOUT_RESP = PostJson "$BASE_URL/board/layout" $LAYOUT $AUTH
Assert-Equal $LAYOUT_RESP.code 200 "Save layout returns 200"
$GET_LAYOUT = GetJson "$BASE_URL/board/layout" $AUTH
Assert-Equal $GET_LAYOUT.code 200 "Get layout returns 200"

Write-Host "`n--- Step 10: Save & Get Active ---"
# BoardActiveDto: input(@NotNull List<String>), status(@NotNull List<String>)
$ACTIVE = @{
  input=@("devices", "templates", "rules", "specs")
  status=@("devices", "edges", "specs")
}
$ACTIVE_RESP = PostJson "$BASE_URL/board/active" $ACTIVE $AUTH
Assert-Equal $ACTIVE_RESP.code 200 "Save active returns 200"
$GET_ACTIVE = GetJson "$BASE_URL/board/active" $AUTH
Assert-Equal $GET_ACTIVE.code 200 "Get active returns 200"
Assert-True (@($GET_ACTIVE.data.input).Count -gt 0) "Active.input is persisted"
Assert-True (@($GET_ACTIVE.data.status).Count -gt 0) "Active.status is persisted"

Write-Host "`n--- Step 11: Add & Delete Custom Template ---"
# DeviceTemplateDto: id(String), name(@NotBlank), manifest(@Valid DeviceManifest)
# DeviceManifest: Name, Description, Modes, InternalVariables(List), ImpactedVariables(List), InitState, WorkingStates(List), Transitions(List), APIs(List), Contents(List)
# WorkingState: Name, Description, Trust, Privacy, Invariant, Dynamics(List<Dynamic>)
# InternalVariable: Name, Description, IsInside, PublicVisible, Trust, Privacy, LowerBound, UpperBound, NaturalChangeRate, Values(List<String>)
# Transition: Name, Description, Signal, StartState, EndState, Trigger({Attribute,Relation,Value}), Assignments(List<{Attribute,Value}>)
# API: Name, Description, Signal, StartState, EndState, Trigger, Assignments
# Content: Name, Privacy, IsChangeable
$CUSTOM_TPL_NAME = "TestDevice_" + [DateTimeOffset]::UtcNow.ToUnixTimeMilliseconds()
$CUSTOM_TPL = @{
  name=$CUSTOM_TPL_NAME
  manifest=@{
    Name=$CUSTOM_TPL_NAME
    Description="A test device"
    Modes=@("normal")
    InitState="idle"
    WorkingStates=@(
      @{ Name="idle"; Description="Device is idle"; Trust="trusted"; Privacy="public"; Invariant="true"; Dynamics=@() },
      @{ Name="running"; Description="Device is running"; Trust="trusted"; Privacy="public"; Invariant="true"; Dynamics=@() }
    )
    InternalVariables=@(
      @{
        Name="speed"; Description="Motor speed"; IsInside=$true; PublicVisible=$true
        Trust="trusted"; Privacy="public"; Values=@("0","1","2","3")
      }
    )
    ImpactedVariables=@()
    Transitions=@(
      @{
        Name="start"; Description="Start transition"; Signal=$true
        StartState="idle"; EndState="running"
        Trigger=@{ Attribute="speed"; Relation=">"; Value="0" }
        Assignments=@()
      },
      @{
        Name="stop"; Description="Stop transition"; Signal=$true
        StartState="running"; EndState="idle"
        Trigger=@{ Attribute="speed"; Relation="="; Value="0" }
        Assignments=@()
      }
    )
    APIs=@(
      @{
        Name="startAPI"; Description="Start the device"; Signal=$true
        StartState="idle"; EndState="running"; Trigger=$null; Assignments=@()
      },
      @{
        Name="stopAPI"; Description="Stop the device"; Signal=$true
        StartState="running"; EndState="idle"; Trigger=$null; Assignments=@()
      }
    )
    Contents=@(
      @{ Name="log"; Privacy="public"; IsChangeable=$true }
    )
  }
}
$ADD_TPL = $null
$TPL_ID = $null
try {
  $ADD_TPL = PostJson "$BASE_URL/board/templates" $CUSTOM_TPL $AUTH
  Assert-Equal $ADD_TPL.code 200 "Add custom template returns 200"
  $TPL_ID = $ADD_TPL.data.id
} catch {
  Write-Host "  [FAIL] Add custom template error: $($_.Exception.Message)" -ForegroundColor Red
  $script:FAIL++
}

if ($TPL_ID) {
  try {
    $DEL_TPL = DeleteJson "$BASE_URL/board/templates/$TPL_ID" $AUTH
    Assert-Equal $DEL_TPL.code 200 "Delete custom template returns 200"
  } catch {
    Write-Host "  [FAIL] Delete custom template error: $($_.Exception.Message)" -ForegroundColor Red
    $script:FAIL++
  }
} else {
  Skip-Step "No template ID returned (or add failed), skip delete"
}

# ==================== 3. Verification ====================

Write-Host "`n--- Step 12: Sync Verify ---"
# VerificationRequestDto: devices(@Valid @NotNull List<DeviceVerificationDto>), rules(List<RuleDto>), specs(@Valid @NotNull List<SpecificationDto>), isAttack(boolean), intensity(@Min(0) @Max(50) int), enablePrivacy(boolean, default false)
# DeviceVerificationDto: varName(@NotBlank), templateName(@NotBlank), state, currentStateTrust, variables(List<VariableStateDto>), privacies(List<PrivacyStateDto>)
# VariableStateDto: name, value, trust
# PrivacyStateDto: name, privacy
$VERIFY_DEVICES = Convert-NodesToVerifyDevices $GET_NODES.data
$VERIFY_RULES = @($GET_RULES.data)
$VERIFY_SPECS = @($GET_SPECS.data)
Assert-Equal @($VERIFY_DEVICES).Count 2 "Verification devices count is 2"
$VERIFY_REQ = @{
  devices=@($VERIFY_DEVICES); rules=@($VERIFY_RULES); specs=@($VERIFY_SPECS)
  isAttack=$false; intensity=3; enablePrivacy=$false
}
try {
  $SYNC = PostJson "$BASE_URL/verify" $VERIFY_REQ $AUTH
  Assert-Equal $SYNC.code 200 "Sync verify returns 200"
  Assert-True ($null -ne $SYNC.data.safe) "Result contains 'safe' field"
  Assert-True ($null -ne $SYNC.data.specResults) "Result contains 'specResults'"
  Assert-True ($null -ne $SYNC.data.checkLogs) "Result contains 'checkLogs'"
  Write-Host "  safe=$($SYNC.data.safe), specResults=$($SYNC.data.specResults -join ',')"
} catch {
  Write-Host "  [FAIL] Sync verify error: $($_.Exception.Message)" -ForegroundColor Red
  $script:FAIL++
}

Write-Host "`n--- Step 12b: Sync Verify with enablePrivacy=true ---"
$VERIFY_REQ_PRIV = @{
  devices=@($VERIFY_DEVICES); rules=@($VERIFY_RULES); specs=@($VERIFY_SPECS)
  isAttack=$false; intensity=3; enablePrivacy=$true
}
try {
  $SYNC_PRIV = PostJson "$BASE_URL/verify" $VERIFY_REQ_PRIV $AUTH
  Assert-Equal $SYNC_PRIV.code 200 "Sync verify (privacy) returns 200"
  Assert-True ($null -ne $SYNC_PRIV.data.safe) "Privacy result contains 'safe' field"
  Write-Host "  safe=$($SYNC_PRIV.data.safe), specResults=$($SYNC_PRIV.data.specResults -join ',')"
} catch {
  Write-Host "  [FAIL] Sync verify (privacy) error: $($_.Exception.Message)" -ForegroundColor Red
  $script:FAIL++
}

Write-Host "`n--- Step 13: Async Verify ---"
try {
  $ASYNC = PostJson "$BASE_URL/verify/async" $VERIFY_REQ $AUTH
  Assert-Equal $ASYNC.code 200 "Async verify returns 200"
  $TASK_ID = $ASYNC.data
  Assert-True ($TASK_ID -gt 0) "Returns task ID (id=$TASK_ID)"

  Write-Host "`n--- Step 14: Get Task Progress ---"
  $PROG = GetJson "$BASE_URL/verify/tasks/$TASK_ID/progress" $AUTH
  Assert-Equal $PROG.code 200 "Get progress returns 200"
  Write-Host "  progress=$($PROG.data)"

  Write-Host "`n  Waiting 5s for async task..."
  Start-Sleep -Seconds 5

  Write-Host "`n--- Step 15: Get Task Status ---"
  # VerificationTaskDto: id, status, createdAt, startedAt, completedAt, processingTimeMs, isSafe, violatedSpecCount, checkLogs, errorMessage
  $TASK = GetJson "$BASE_URL/verify/tasks/$TASK_ID" $AUTH
  Assert-Equal $TASK.code 200 "Get task returns 200"
  Assert-True ($TASK.data.status -eq "COMPLETED" -or $TASK.data.status -eq "FAILED") "Task finished (status=$($TASK.data.status))"
  Write-Host "  status=$($TASK.data.status), isSafe=$($TASK.data.isSafe)"

  Write-Host "`n--- Step 16: Cancel Task (already done, expect false) ---"
  $CANCEL = PostJson "$BASE_URL/verify/tasks/$TASK_ID/cancel" @{} $AUTH
  Assert-Equal $CANCEL.code 200 "Cancel returns 200"
  Write-Host "  cancelled=$($CANCEL.data)"
} catch {
  Write-Host "  [FAIL] Async verify error: $($_.Exception.Message)" -ForegroundColor Red
  $script:FAIL++
}

# ==================== 4. Traces ====================

Write-Host "`n--- Step 17: Get All Traces ---"
# TraceDto: id, userId, verificationTaskId, violatedSpecId, violatedSpecJson, states(List<TraceStateDto>), createdAt
$TRACES = GetJson "$BASE_URL/verify/traces" $AUTH
Assert-Equal $TRACES.code 200 "Get traces returns 200"
$TRACE_COUNT = @($TRACES.data).Count
Write-Host "  trace count=$TRACE_COUNT"

if ($TRACE_COUNT -gt 0) {
  $TID = $TRACES.data[0].id

  Write-Host "`n--- Step 18: Get Single Trace ---"
  $SINGLE = GetJson "$BASE_URL/verify/traces/$TID" $AUTH
  Assert-Equal $SINGLE.code 200 "Get single trace returns 200"
  Assert-True ($null -ne $SINGLE.data.states) "Trace contains 'states'"

  Write-Host "`n--- Step 19: Delete Trace ---"
  $DEL = DeleteJson "$BASE_URL/verify/traces/$TID" $AUTH
  Assert-Equal $DEL.code 200 "Delete trace returns 200"

  # Verify deletion
  $AFTER = GetJson "$BASE_URL/verify/traces" $AUTH
  $NEW_COUNT = @($AFTER.data).Count
  Assert-Equal $NEW_COUNT ($TRACE_COUNT - 1) "Trace count decreased by 1"
} else {
  Skip-Step "No traces to test (Steps 18-19)"
}

# ==================== 5. Validation ====================

Write-Host "`n--- Step 20: Validation - missing devices (expect error) ---"
try {
  $BAD_REQ = PostJson "$BASE_URL/verify" @{ rules=@(); specs=@($VERIFY_SPECS); intensity=3 } $AUTH
  if ($BAD_REQ.code -ne 200) {
    Assert-True $true "Server rejected null devices (code=$($BAD_REQ.code))"
  } else {
    Assert-True $false "Should have rejected null devices"
  }
} catch {
  Assert-True ($_.Exception.Message -match "400|500") "Null devices rejected with error"
}

Write-Host "`n--- Step 21: Validation - intensity out of range (expect error) ---"
try {
  $BAD_INT = PostJson "$BASE_URL/verify" @{ devices=@($VERIFY_DEVICES); rules=@(); specs=@($VERIFY_SPECS); intensity=999 } $AUTH
  if ($BAD_INT.code -ne 200) {
    Assert-True $true "Server rejected intensity=999 (code=$($BAD_INT.code))"
  } else {
    Assert-True $false "Should have rejected intensity=999"
  }
} catch {
  Assert-True ($_.Exception.Message -match "400|500") "intensity=999 rejected with error"
}

# ==================== 6. Auth Teardown ====================

Write-Host "`n--- Step 22: Logout ---"
$LOGOUT = PostJson "$BASE_URL/auth/logout" @{} $AUTH
Assert-Equal $LOGOUT.code 200 "Logout returns 200"

Write-Host "`n--- Step 23: Token invalidated (expect 401) ---"
try {
  GetJson "$BASE_URL/board/templates" $AUTH | Out-Null
  Assert-True $false "Should have thrown 401 after logout"
} catch {
  Assert-True ($_.Exception.Message -match "401") "Stale token returns 401"
}

# ==================== Summary ====================

Write-Host "`n=========================================="
Write-Host " Results: $PASS passed, $FAIL failed, $SKIP skipped"
if ($FAIL -gt 0) {
  Write-Host " STATUS: FAILED" -ForegroundColor Red
} else {
  Write-Host " STATUS: ALL PASSED" -ForegroundColor Green
}
Write-Host "=========================================="

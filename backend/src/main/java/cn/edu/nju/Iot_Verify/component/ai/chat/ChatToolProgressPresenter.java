package cn.edu.nju.Iot_Verify.component.ai.chat;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Set;

/**
 * Turns a raw AI tool result into the short, user-visible progress line shown while a chat turn
 * runs.
 *
 * <p>Purely presentational: it reads the tool's JSON payload and renders a bilingual summary,
 * deliberately reporting an absent or unconfirmed result as such rather than implying success.
 * It holds no chat-session state, which is why it lives outside {@code ChatServiceImpl}.</p>
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class ChatToolProgressPresenter {

    /**
     * Budget for one round's user-visible reasoning. Larger than a tool status line because this is
     * the channel that has to carry a decomposition, the alternatives considered, and the check —
     * the provider caps its own summary at 2000, so this is the binding limit on explanation.
     */
    private static final int REASONING_MAX_CHARS = 1600;

    private final ObjectMapper objectMapper;

    /**
     * A known tool whose payload is structurally incomplete must not be summarised as a result.
     * Exposed because the chat service applies the same check when classifying an execution.
     */
    public boolean hasValidKnownToolPayload(String functionName, JsonNode root) {
        if (!"board_overview".equals(functionName)) return true;
        return hasArray(root, "devices")
                && hasArray(root, "rules")
                && hasArray(root, "specs")
                && hasArray(root, "edges")
                && hasArray(root, "environmentVariables");
    }

    private boolean hasArray(JsonNode root, String field) {
        return root != null && root.has(field) && root.get(field).isArray();
    }

    public String compactProgressDetail(String value) {
        return compactProgressDetail(value, 240);
    }

    public String compactProgressDetail(String value, int maxChars) {
        if (value == null) return null;
        String compact = value.replaceAll("\\s+", " ").trim();
        if (compact.length() <= maxChars) return compact;
        return compact.substring(0, Math.max(0, maxChars - 3)) + "...";
    }

    public String toolProgressDetail(String functionName, String toolResult, boolean preferChinese) {
        if (toolResult == null || toolResult.isBlank()) {
            return preferChinese ? "工具没有返回可用结果。" : "The tool returned no usable result.";
        }
        try {
            JsonNode root = objectMapper.readTree(toolResult);
            if (!root.isObject() || root.path("skipped").asBoolean(false)) {
                return null;
            }
            if (!root.path("error").asText("").isBlank()) {
                String errorCode = root.path("errorCode").asText("").trim();
                String code = errorCode.matches("[A-Z0-9_-]{1,64}") ? " (" + errorCode + ")" : "";
                return preferChinese
                        ? "工具未能完成该操作" + code + "，具体原因见助手回复。"
                        : "The tool could not complete the operation" + code
                        + "; see the assistant response for the specific reason.";
            }

            if ("board_overview".equals(functionName)) {
                if (!hasValidKnownToolPayload(functionName, root)) return null;
                return preferChinese
                        ? String.format("已读取画布：%d 个设备、%d 条规则、%d 条规约、%d 个共享环境变量。",
                        arraySize(root, "devices"), arraySize(root, "rules"),
                        arraySize(root, "specs"), arraySize(root, "environmentVariables"))
                        : String.format("Read the board: %d devices, %d rules, %d specifications, and %d shared environment variables.",
                        arraySize(root, "devices"), arraySize(root, "rules"),
                        arraySize(root, "specs"), arraySize(root, "environmentVariables"));
            }
            if ("add_device".equals(functionName) && "created".equals(root.path("operation").asText())) {
                JsonNode device = root.path("device");
                String label = device.path("label").asText("").trim();
                String state = device.path("state").asText("").trim();
                int environmentChanges = arraySize(root, "environmentChanges");
                return compactToolProgressDetail(preferChinese
                        ? String.format("已创建设备%s%s；环境池变化 %d 项。",
                        quotedName(label), state.isBlank() ? "" : "，初始状态为 " + state,
                        environmentChanges)
                        : String.format("Created device%s%s with %d Environment Pool change(s).",
                        quotedName(label), state.isBlank() ? "" : " in initial state " + state,
                        environmentChanges));
            }
            if ("delete_device".equals(functionName)) {
                boolean preview = "preview".equals(root.path("operation").asText());
                JsonNode device = preview ? root.path("device") : root.path("deletedDevice");
                String label = device.path("label").asText("").trim();
                if (preview) {
                    return compactToolProgressDetail(preferChinese
                            ? String.format("已预览删除设备%s：将移除 %d 条规则、%d 条规约并改变 %d 个环境变量；尚未写入。",
                            quotedName(label), root.path("wouldRemoveRuleCount").asInt(0),
                            root.path("wouldRemoveSpecificationCount").asInt(0),
                            root.path("wouldChangeEnvironmentVariableCount").asInt(0))
                            : String.format("Previewed deletion of device%s: %d rule(s), %d specification(s), and %d environment variable(s) would be affected; nothing was written.",
                            quotedName(label), root.path("wouldRemoveRuleCount").asInt(0),
                            root.path("wouldRemoveSpecificationCount").asInt(0),
                            root.path("wouldChangeEnvironmentVariableCount").asInt(0)));
                }
                if ("deleted".equals(root.path("operation").asText())) {
                    return compactToolProgressDetail(preferChinese
                            ? String.format("已删除设备%s，并移除 %d 条规则和 %d 条规约。",
                            quotedName(label), root.path("removedRuleCount").asInt(0),
                            root.path("removedSpecificationCount").asInt(0))
                            : String.format("Deleted device%s and removed %d rule(s) and %d specification(s).",
                            quotedName(label), root.path("removedRuleCount").asInt(0),
                            root.path("removedSpecificationCount").asInt(0)));
                }
            }
            if ("manage_rule".equals(functionName)) {
                String operation = root.path("operation").asText("").trim();
                JsonNode rule = "deleted".equals(operation) ? root.path("deletedRule") : root.path("rule");
                String description = rule.path("description").asText("").trim();
                if (!operation.isBlank()) {
                    String action = "created".equals(operation)
                            ? (preferChinese ? "已创建规则" : "Created rule")
                            : (preferChinese ? "已删除规则" : "Deleted rule");
                    return compactToolProgressDetail(description.isBlank()
                            ? action + (preferChinese ? "。" : ".")
                            : action + (preferChinese ? "：" : ": ") + description);
                }
            }
            if ("apply_fix".equals(functionName)) {
                String operation = root.path("operation").asText("").trim();
                if ("preview".equals(operation)) {
                    return compactToolProgressDetail(preferChinese
                            ? "已预览形式化修复建议；尚未修改规则，等待明确确认。"
                            : "Previewed the formal fix; no rules changed and explicit confirmation is pending.");
                }
                if ("applied".equals(operation)) {
                    return compactToolProgressDetail(preferChinese
                            ? String.format("已应用形式化修复：规则数由 %d 变为 %d。",
                            root.path("previousRuleCount").asInt(0), root.path("currentRuleCount").asInt(0))
                            : String.format("Applied the formal fix; rule count changed from %d to %d.",
                            root.path("previousRuleCount").asInt(0), root.path("currentRuleCount").asInt(0)));
                }
            }
            if ("manage_spec".equals(functionName)) {
                String operation = root.path("operation").asText("").trim();
                JsonNode spec = "deleted".equals(operation)
                        ? root.path("deletedSpecification") : root.path("specification");
                String formula = spec.path("formulaPreview").asText("").trim();
                if (!operation.isBlank()) {
                    String action = "created".equals(operation)
                            ? (preferChinese ? "已创建规约" : "Created specification")
                            : (preferChinese ? "已删除规约" : "Deleted specification");
                    return compactToolProgressDetail(formula.isBlank()
                            ? action + (preferChinese ? "。" : ".")
                            : action + (preferChinese ? "：" : ": ") + formula);
                }
            }
            if ("add_template".equals(functionName) && "created".equals(root.path("operation").asText())) {
                String name = root.path("template").path("name").asText("").trim();
                return compactToolProgressDetail(preferChinese
                        ? "已创建设备模板" + quotedName(name) + "。"
                        : "Created device template" + quotedName(name) + ".");
            }
            if (Set.of("recommend_rules", "recommend_specifications", "recommend_related_devices")
                    .contains(functionName)) {
                int kept = root.path("validatedCount").asInt(root.path("count").asInt(0));
                int filtered = root.path("filteredCount").asInt(0);
                String firstReason = root.path("filteredItems").path(0).path("reason").asText("").trim();
                String summary = preferChinese
                        ? "AI 候选经后端校验后保留 " + kept + " 项，过滤 " + filtered + " 项。"
                        : "Backend validation kept " + kept + " AI candidate(s) and filtered " + filtered + ".";
                if (!firstReason.isBlank()) {
                    summary += (preferChinese ? " 首个过滤原因：" : " First filter reason: ") + firstReason;
                }
                return compactToolProgressDetail(summary);
            }
            if ("recommend_scenario".equals(functionName)) {
                JsonNode scene = root.path("scene");
                String name = root.path("scenarioName").asText("").trim();
                String summary = preferChinese
                        ? String.format("已生成场景%s：%d 个设备、%d 条规则、%d 条规约；过滤 %d 个无效候选。",
                        quotedName(name), arraySize(scene, "devices"), arraySize(scene, "rules"),
                        arraySize(scene, "specs"), root.path("filteredCount").asInt(0))
                        : String.format("Generated scenario%s with %d devices, %d rules, and %d specifications; filtered %d invalid candidate(s).",
                        quotedName(name), arraySize(scene, "devices"), arraySize(scene, "rules"),
                        arraySize(scene, "specs"), root.path("filteredCount").asInt(0));
                if (!root.path("verificationReady").asBoolean(false)) {
                    summary += preferChinese ? " 该草案目前尚不能启动验证。" : " The draft is not verification-ready yet.";
                }
                return compactToolProgressDetail(summary);
            }
            if ("apply_scenario".equals(functionName)) {
                String name = root.path("scenarioName").asText("").trim();
                boolean preview = "preview".equals(root.path("operation").asText());
                if (preview) {
                    return compactToolProgressDetail(preferChinese
                            ? String.format("已生成场景%s的全量替换预览，尚未写入，正在等待确认。", quotedName(name))
                            : String.format("Prepared a full-board replacement preview for scenario%s; nothing was written and confirmation is required.", quotedName(name)));
                }
                return compactToolProgressDetail(preferChinese
                        ? String.format("已应用场景%s：%d 个设备、%d 条规则、%d 条规约。",
                        quotedName(name), root.path("deviceCount").asInt(0),
                        root.path("ruleCount").asInt(0), root.path("specificationCount").asInt(0))
                        : String.format("Applied scenario%s with %d devices, %d rules, and %d specifications.",
                        quotedName(name), root.path("deviceCount").asInt(0),
                        root.path("ruleCount").asInt(0), root.path("specificationCount").asInt(0)));
            }
            if ("reset_default_templates".equals(functionName)) {
                if (root.path("requiresUserConfirmation").asBoolean(false)) {
                    JsonNode preview = root.path("preview");
                    return preferChinese
                            ? String.format("已预览默认模板刷新：%d 个模板变化、%d 个受影响设备，尚未写入，正在等待确认。",
                            arraySize(preview, "templateChanges"), arraySize(preview, "affectedDevices"))
                            : String.format("Previewed the default-template refresh: %d template change(s) and %d affected device(s); nothing was written and confirmation is required.",
                            arraySize(preview, "templateChanges"), arraySize(preview, "affectedDevices"));
                }
                if ("reset".equals(root.path("operation").asText())) {
                    return preferChinese
                            ? String.format("已刷新默认模板：%d 个模板变化、%d 个受影响设备、%d 个环境变量变化。",
                            root.path("templateChangeCount").asInt(0),
                            root.path("affectedDeviceCount").asInt(0),
                            root.path("environmentChangeCount").asInt(0))
                            : String.format("Refreshed default templates: %d template change(s), %d affected device(s), and %d environment-variable change(s).",
                            root.path("templateChangeCount").asInt(0),
                            root.path("affectedDeviceCount").asInt(0),
                            root.path("environmentChangeCount").asInt(0));
                }
            }
            if ("manage_environment".equals(functionName)) {
                JsonNode variable = root.path("currentVariable");
                String name = variable.path("name").asText("").trim();
                if (!name.isBlank()) {
                    return compactToolProgressDetail(preferChinese
                            ? "环境变量“" + name + "”当前值为 " + variable.path("value").asText("")
                            + "，trust=" + variable.path("trust").asText("")
                            + "，privacy=" + variable.path("privacy").asText("") + "。"
                            : "Environment variable '" + name + "' is now " + variable.path("value").asText("")
                            + " with trust=" + variable.path("trust").asText("")
                            + " and privacy=" + variable.path("privacy").asText("") + ".");
                }
            }

            String operation = root.path("operation").asText("").trim();
            if (!operation.isBlank()) {
                return compactToolProgressDetail(preferChinese
                        ? "工具操作结果：" + operation + "。"
                        : "Tool operation result: " + operation + ".");
            }
            return preferChinese ? "工具已返回结构化结果。" : "The tool returned a structured result.";
        } catch (Exception e) {
            return preferChinese ? "工具结果无法生成摘要。" : "The tool result could not be summarized.";
        }
    }

    private int arraySize(JsonNode root, String field) {
        JsonNode value = root == null ? null : root.path(field);
        return value != null && value.isArray() ? value.size() : 0;
    }

    private String quotedName(String name) {
        return name == null || name.isBlank() ? "" : " '" + name + "'";
    }

    private String compactToolProgressDetail(String value) {
        return sanitizeProgressDetail(value, 240);
    }

    /**
     * Sanitizes the model's user-visible reasoning while keeping it readable <em>as</em> reasoning.
     *
     * <p>Deliberately different from {@link #compactToolProgressDetail}, which formats a one-line
     * status. Reasoning is the only channel carrying actual analysis, so three things that are
     * right for a status line are wrong here:
     *
     * <ul>
     *   <li><b>Line structure is preserved.</b> Collapsing all whitespace turned a decomposition
     *       ("Goal … / Observed … / Next …") into one run-on line.</li>
     *   <li><b>Prose is left alone.</b> Identifier redaction is anchored to real identifier shapes,
     *       so ordinary hyphenated English — "rule-based", "device-level", "trace-driven" — is no
     *       longer replaced by a redaction marker mid-sentence.</li>
     *   <li><b>The budget is larger and the cut lands on a boundary</b>, not mid-clause.</li>
     * </ul>
     */
    public String compactReasoningProgressDetail(String value) {
        if (value == null) return null;
        // Collapse horizontal runs and excess blank lines, but keep single newlines.
        String structured = redactIdentifiers(value)
                .replaceAll("[ \\t\\x0B\\f\\r]+", " ")
                .replaceAll(" ?\\n ?", "\n")
                .replaceAll("\\n{3,}", "\n\n")
                .trim();
        return truncateAtBoundary(structured, REASONING_MAX_CHARS);
    }

    /**
     * Cuts at the last sentence end or line break inside the budget, so the user never reads a
     * sentence that stops mid-clause. Falls back to a hard cut only when no usable boundary exists.
     */
    private String truncateAtBoundary(String value, int maxChars) {
        if (value.length() <= maxChars) return value;
        String head = value.substring(0, maxChars);
        int boundary = -1;
        for (String terminator : new String[] {"\n", ". ", "。", "; ", "；"}) {
            boundary = Math.max(boundary, head.lastIndexOf(terminator));
        }
        // Only honour a boundary in the last third; earlier would discard usable reasoning. A short
        // decomposition followed by one long unbroken paragraph therefore takes the hard cut — that is
        // the intended trade: losing two thirds of the explanation to end on a period reads worse than
        // an ellipsis mid-clause.
        if (boundary > maxChars / 3 * 2) {
            return head.substring(0, boundary).trim() + " …";
        }
        return head.substring(0, Math.max(0, maxChars - 2)).trim() + " …";
    }

    private String sanitizeProgressDetail(String value, int maxChars) {
        if (value == null) return null;
        return compactProgressDetail(redactIdentifiers(value), maxChars);
    }

    /**
     * Removes confirmation tokens and internal identifiers.
     *
     * <p>The hyphenated form requires a digit in the tail, which is what distinguishes a generated id
     * ({@code rule-4a}) from an English compound adjective ({@code rule-based}, {@code device-level});
     * without it, the redaction corrupted the explanation it was protecting. The underscore form needs
     * no digit: English prose does not join words with underscores, so {@code device_a} is an id too —
     * requiring a digit there leaked every non-numeric node id past the only mechanical guard.
     */
    private String redactIdentifiers(String value) {
        return value
                .replaceAll("(?i)(impactToken|confirmationToken|domainImpactToken|suggestionToken)\\s*[:=]\\s*[^,;\\s]+", "$1=[hidden]")
                .replaceAll("(?i)\\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\\b", "[internal reference]")
                .replaceAll("(?i)\\b(?:device|node|rule|spec|task|trace|simulation)_[a-z0-9_-]+\\b", "[internal reference]")
                .replaceAll("(?i)\\b(?:device|node|rule|spec|task|trace|simulation)-[a-z0-9_-]*[0-9][a-z0-9_-]*\\b", "[internal reference]")
                .replaceAll("(?i)\\b(?:device|node|rule|spec(?:ification)?|task|trace|simulation|session|user)\\s+id\\s*[:=#]?\\s*[a-z0-9_-]+", "[internal reference]");
    }
}

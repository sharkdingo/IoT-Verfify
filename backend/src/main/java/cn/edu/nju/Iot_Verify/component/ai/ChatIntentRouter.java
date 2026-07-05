package cn.edu.nju.Iot_Verify.component.ai;

import org.springframework.stereotype.Component;

import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.regex.Pattern;

/**
 * Deterministic intent router for deciding whether a message should enter the tool loop.
 *
 * <p>The router is a small chain of strategies. High-confidence guardrails run before
 * actionable platform rules, so conceptual questions and content-generation requests do not
 * accidentally trigger platform mutations. An embedding-backed semantic strategy can be added
 * later between the guardrail strategies and {@link ActionablePlatformStrategy}.
 */
@Component
public class ChatIntentRouter {

    private static final Pattern EXPLICIT_TOOL_NAME = pattern("""
            \\b(add_device|delete_device|search_devices|list_rules|manage_rule|check_duplicate_rule|recommend_rules|
            recommend_related_devices|list_specs|manage_spec|recommend_specifications|list_templates|add_template|
            delete_template|verify_model|verify_model_async|verify_task_status|cancel_verify_task|list_traces|
            get_trace|delete_trace|fix_violation|simulate_model|simulate_model_async|simulate_task_status|cancel_simulate_task|
            list_simulation_traces|get_simulation_trace|delete_simulation_trace|board_overview)\\b
            """.replaceAll("\\s+", ""));

    private static final List<MatcherGroup> MUTATION_ACTIONS = List.of(
            regex("\\b(add|create|build|generate|delete|remove|update|modify|change|save|apply|fix|repair|configure|setup|set\\s+up|set)\\b"),
            words("\u6dfb\u52a0", "\u65b0\u589e", "\u521b\u5efa", "\u5efa\u7acb", "\u65b0\u5efa",
                    "\u751f\u6210", "\u5220\u9664", "\u79fb\u9664", "\u66f4\u65b0", "\u4fee\u6539",
                    "\u4fdd\u5b58", "\u5e94\u7528", "\u4fee\u590d", "\u8c03\u6574", "\u914d\u7f6e",
                    "\u8bbe\u4e3a", "\u8bbe\u7f6e", "\u6539\u6210", "\u6539\u4e3a")
    );

    private static final List<MatcherGroup> INSPECTION_ACTIONS = List.of(
            regex("\\b(list|show|view|inspect|check|search|find|get|display|summarize|overview|status)\\b"),
            words("\u5217\u51fa", "\u5c55\u793a", "\u67e5\u770b", "\u68c0\u67e5", "\u641c\u7d22",
                    "\u67e5\u627e", "\u67e5\u8be2", "\u83b7\u53d6", "\u663e\u793a", "\u6982\u89c8",
                    "\u72b6\u6001", "\u770b\u770b", "\u770b\u4e00\u4e0b", "\u6709\u6ca1\u6709",
                    "\u6709\u54ea\u4e9b")
    );

    private static final List<MatcherGroup> EXECUTION_ACTIONS = List.of(
            regex("\\b(run|execute|start|cancel|verify|simulate|model\\s+check|model-check|formal\\s+verification)\\b"),
            words("\u8fd0\u884c", "\u6267\u884c", "\u542f\u52a8", "\u53d6\u6d88", "\u9a8c\u8bc1",
                    "\u5f62\u5f0f\u5316\u9a8c\u8bc1", "\u6a21\u578b\u68c0\u67e5", "\u4eff\u771f",
                    "\u6a21\u62df")
    );

    private static final List<MatcherGroup> RECOMMENDATION_ACTIONS = List.of(
            regex("\\b(recommend|suggest|propose|advise|what\\s+.+\\s+should|should\\s+i)\\b"),
            words("\u63a8\u8350", "\u5efa\u8bae", "\u5e94\u8be5")
    );

    private static final List<MatcherGroup> DUPLICATE_OR_CONFLICT_ACTIONS = List.of(
            regex("\\b(duplicate|conflict|overlap|inconsistent)\\b"),
            words("\u91cd\u590d", "\u51b2\u7a81", "\u91cd\u53e0", "\u4e0d\u4e00\u81f4")
    );

    private static final List<MatcherGroup> DEVICE_TARGETS = List.of(
            regex("\\b(devices?|nodes?|sensors?|actuators?|appliances?|air\\s*conditioners?|purifiers?|lights?|windows?|doors?|thermostats?|alarms?|cameras?|sprinklers?|humidifiers?|washers?|dryers?|ovens?|refrigerators?)\\b"),
            words("\u8bbe\u5907", "\u8282\u70b9", "\u4f20\u611f\u5668", "\u6267\u884c\u5668",
                    "\u7a7a\u8c03", "\u51c0\u5316\u5668", "\u706f", "\u7a97\u6237", "\u95e8",
                    "\u6e29\u63a7\u5668", "\u8b66\u62a5", "\u6444\u50cf\u5934", "\u55b7\u6dcb",
                    "\u52a0\u6e7f\u5668", "\u6d17\u8863\u673a", "\u70d8\u5e72\u673a", "\u70e4\u7bb1",
                    "\u51b0\u7bb1")
    );

    private static final List<MatcherGroup> RULE_TARGETS = List.of(
            regex("\\b(rules?|automations?|triggers?|conditions?|actions?|routines?)\\b"),
            words("\u89c4\u5219", "\u81ea\u52a8\u5316", "\u8054\u52a8", "\u89e6\u53d1",
                    "\u6761\u4ef6", "\u52a8\u4f5c", "\u4f8b\u7a0b")
    );

    private static final List<MatcherGroup> SPEC_TARGETS = List.of(
            regex("\\b(specs?|specifications?|properties|invariants?|constraints?|ctl|ltl|safety)\\b"),
            words("\u89c4\u7ea6", "\u7ea6\u675f", "\u6027\u8d28", "\u5c5e\u6027",
                    "\u4e0d\u53d8\u91cf", "\u5b89\u5168\u6027", "\u5b89\u5168\u7ea6\u675f")
    );

    private static final List<MatcherGroup> TEMPLATE_TARGETS = List.of(
            regex("\\b(templates?|manifests?|capability|capabilities)\\b"),
            words("\u6a21\u677f", "\u6e05\u5355", "\u80fd\u529b")
    );

    private static final List<MatcherGroup> BOARD_TARGETS = List.of(
            regex("\\b(boards?|canvases|canvas|models?|current\\s+setup|smart\\s+home\\s+systems?)\\b"),
            words("\u753b\u5e03", "\u9762\u677f", "\u6a21\u578b", "\u5f53\u524d\u7cfb\u7edf",
                    "\u667a\u80fd\u5bb6\u5c45\u7cfb\u7edf")
    );

    private static final List<MatcherGroup> TRACE_TARGETS = List.of(
            regex("\\b(traces?|counterexamples?|counter-examples?|verification\\s+results?|simulation\\s+results?)\\b"),
            words("\u8f68\u8ff9", "\u53cd\u4f8b", "\u9a8c\u8bc1\u7ed3\u679c",
                    "\u4eff\u771f\u7ed3\u679c", "\u6a21\u62df\u7ed3\u679c")
    );

    private static final List<MatcherGroup> VERIFICATION_TARGETS = List.of(
            regex("\\b(verifications?|verify|nusmv|model\\s+checking|formal\\s+verification)\\b"),
            words("\u9a8c\u8bc1", "\u5f62\u5f0f\u5316", "\u6a21\u578b\u68c0\u67e5")
    );

    private static final List<MatcherGroup> SIMULATION_TARGETS = List.of(
            regex("\\b(simulations?|simulate|scenarios?)\\b"),
            words("\u4eff\u771f", "\u6a21\u62df", "\u573a\u666f")
    );

    private static final List<MatcherGroup> CURRENT_CONTEXT = List.of(
            regex("\\b(current|existing|my|this|our|in\\s+this\\s+project|in\\s+my\\s+system|on\\s+the\\s+board|on\\s+the\\s+canvas)\\b"),
            words("\u5f53\u524d", "\u73b0\u5728", "\u73b0\u6709", "\u5df2\u6709", "\u6211\u7684",
                    "\u8fd9\u4e2a", "\u672c\u9879\u76ee", "\u7cfb\u7edf\u4e2d", "\u753b\u5e03\u4e0a",
                    "\u6a21\u578b\u4e2d", "\u5f53\u524d\u7cfb\u7edf")
    );

    private static final List<MatcherGroup> DELEGATION_MARKERS = List.of(
            regex("\\b(please|help\\s+me|can\\s+you|could\\s+you|for\\s+me|i\\s+want\\s+you\\s+to|let'?s|do\\s+it)\\b"),
            words("\u8bf7", "\u5e2e\u6211", "\u7ed9\u6211", "\u66ff\u6211", "\u5e2e\u5fd9",
                    "\u76f4\u63a5", "\u73b0\u5728", "\u9a6c\u4e0a", "\u9ebb\u70e6", "\u6211\u60f3\u8ba9\u4f60",
                    "\u6211\u8981\u4f60")
    );

    private static final List<MatcherGroup> CONCEPTUAL_MARKERS = List.of(
            regex("\\b(what\\s+is|what\\s+are|why|how\\s+does|explain|describe|definition|concept|difference|best\\s+practice|principle|tell\\s+me\\s+about)\\b"),
            words("\u662f\u4ec0\u4e48", "\u4e3a\u4ec0\u4e48", "\u4e3a\u4f55", "\u600e\u4e48\u7406\u89e3",
                    "\u89e3\u91ca", "\u8bf4\u660e", "\u4ecb\u7ecd", "\u5b9a\u4e49", "\u6982\u5ff5",
                    "\u533a\u522b", "\u539f\u7406", "\u6700\u4f73\u5b9e\u8df5")
    );

    private static final List<MatcherGroup> CODE_OR_DOC_ARTIFACTS = List.of(
            regex("\\b(code|script|python|java|typescript|javascript|mqtt|example|tutorial|doc|document)\\b"),
            words("\u4ee3\u7801", "\u811a\u672c", "\u793a\u4f8b", "\u6559\u7a0b", "\u6587\u6863",
                    "\u7f16\u5199", "\u5199\u4e00\u6bb5", "\u5199\u4e2a", "\u5b9e\u73b0\u4e00\u4e2a")
    );

    private static final List<MatcherGroup> SCENARIO_QUESTIONS = List.of(
            regex("\\b(if|when|whether|will|would|trigger|happen)\\b"),
            words("\u5982\u679c", "\u662f\u5426", "\u4f1a\u4e0d\u4f1a", "\u89e6\u53d1",
                    "\u53d1\u751f", "\u80fd\u4e0d\u80fd")
    );

    private final List<IntentStrategy> strategies;

    public ChatIntentRouter() {
        this(defaultStrategies());
    }

    ChatIntentRouter(List<IntentStrategy> strategies) {
        this.strategies = strategies == null || strategies.isEmpty()
                ? defaultStrategies()
                : List.copyOf(strategies);
    }

    public Decision route(String content) {
        IntentContext context = IntentContext.from(content);
        for (IntentStrategy strategy : strategies) {
            Optional<Decision> decision = strategy.decide(context);
            if (decision.isPresent()) {
                return decision.get();
            }
        }
        return Decision.conversation("no_strategy_decision");
    }

    private static List<IntentStrategy> defaultStrategies() {
        return List.of(
                new BlankMessageStrategy(),
                new ExplicitToolNameStrategy(),
                new NoPlatformTargetStrategy(),
                new ContentGenerationGuardStrategy(),
                new ConceptualQuestionGuardStrategy(),
                // Future semantic embedding fallback belongs here: after hard guardrails,
                // before deterministic action rules.
                new ActionablePlatformStrategy(),
                new ConversationFallbackStrategy()
        );
    }

    private interface IntentStrategy {
        Optional<Decision> decide(IntentContext context);
    }

    private static final class BlankMessageStrategy implements IntentStrategy {
        @Override
        public Optional<Decision> decide(IntentContext context) {
            return context.blank()
                    ? Optional.of(Decision.conversation("blank_message"))
                    : Optional.empty();
        }
    }

    private static final class ExplicitToolNameStrategy implements IntentStrategy {
        @Override
        public Optional<Decision> decide(IntentContext context) {
            return !context.blank() && EXPLICIT_TOOL_NAME.matcher(context.normalized()).find()
                    ? Optional.of(Decision.tools("explicit_tool_name"))
                    : Optional.empty();
        }
    }

    private static final class NoPlatformTargetStrategy implements IntentStrategy {
        @Override
        public Optional<Decision> decide(IntentContext context) {
            return !context.blank() && !context.targets().any()
                    ? Optional.of(Decision.conversation("no_platform_target"))
                    : Optional.empty();
        }
    }

    private static final class ContentGenerationGuardStrategy implements IntentStrategy {
        @Override
        public Optional<Decision> decide(IntentContext context) {
            if (context.codeOrDocArtifact()
                    && !context.targets().rule()
                    && !context.targets().spec()
                    && !context.targets().template()) {
                return Optional.of(Decision.conversation("content_generation_request"));
            }
            return Optional.empty();
        }
    }

    private static final class ConceptualQuestionGuardStrategy implements IntentStrategy {
        @Override
        public Optional<Decision> decide(IntentContext context) {
            if (context.conceptual()
                    && !context.recommendation()
                    && !context.duplicateOrConflict()
                    && !(context.currentContext()
                    && (context.inspection() || context.scenarioQuestion() || context.execution()))
                    && !(context.delegated() && (context.mutation() || context.execution()))) {
                return Optional.of(Decision.conversation("conceptual_question"));
            }
            return Optional.empty();
        }
    }

    private static final class ActionablePlatformStrategy implements IntentStrategy {
        @Override
        public Optional<Decision> decide(IntentContext context) {
            TargetFlags targets = context.targets();
            if ((context.mutation() || context.duplicateOrConflict()) && targets.actionableMutationTarget()) {
                return Optional.of(Decision.tools("mutation_or_conflict_on_platform_target"));
            }
            if (context.recommendation() && targets.recommendationTarget()) {
                return Optional.of(Decision.tools("recommendation_on_platform_target"));
            }
            if (context.execution() && targets.executionTarget()) {
                return Optional.of(Decision.tools("execution_on_platform_target"));
            }
            if (context.scenarioQuestion() && (context.currentContext() || targets.board()) && targets.scenarioTarget()) {
                return Optional.of(Decision.tools("scenario_question_on_current_model"));
            }
            if (context.inspection() && targets.readableTarget()
                    && (context.currentContext() || context.delegated() || targets.trace())) {
                return Optional.of(Decision.tools("inspection_on_platform_target"));
            }
            return Optional.empty();
        }
    }

    private static final class ConversationFallbackStrategy implements IntentStrategy {
        @Override
        public Optional<Decision> decide(IntentContext context) {
            return Optional.of(Decision.conversation("no_actionable_platform_intent"));
        }
    }

    private record IntentContext(String normalized,
                                 boolean blank,
                                 boolean mutation,
                                 boolean inspection,
                                 boolean execution,
                                 boolean recommendation,
                                 boolean duplicateOrConflict,
                                 boolean currentContext,
                                 boolean delegated,
                                 boolean conceptual,
                                 boolean codeOrDocArtifact,
                                 boolean scenarioQuestion,
                                 TargetFlags targets) {
        static IntentContext from(String content) {
            if (content == null || content.isBlank()) {
                return new IntentContext("", true, false, false, false, false, false,
                        false, false, false, false, false, TargetFlags.empty());
            }
            String normalized = normalize(content);
            return new IntentContext(
                    normalized,
                    false,
                    matchesAny(MUTATION_ACTIONS, normalized),
                    matchesAny(INSPECTION_ACTIONS, normalized),
                    matchesAny(EXECUTION_ACTIONS, normalized),
                    matchesAny(RECOMMENDATION_ACTIONS, normalized),
                    matchesAny(DUPLICATE_OR_CONFLICT_ACTIONS, normalized),
                    matchesAny(CURRENT_CONTEXT, normalized),
                    matchesAny(DELEGATION_MARKERS, normalized),
                    matchesAny(CONCEPTUAL_MARKERS, normalized),
                    matchesAny(CODE_OR_DOC_ARTIFACTS, normalized),
                    matchesAny(SCENARIO_QUESTIONS, normalized),
                    TargetFlags.from(normalized)
            );
        }
    }

    public record Decision(boolean requiresToolLoop, String reason) {
        private static Decision tools(String reason) {
            return new Decision(true, reason);
        }

        private static Decision conversation(String reason) {
            return new Decision(false, reason);
        }
    }

    private record TargetFlags(boolean device,
                               boolean rule,
                               boolean spec,
                               boolean template,
                               boolean board,
                               boolean trace,
                               boolean verification,
                               boolean simulation) {
        static TargetFlags empty() {
            return new TargetFlags(false, false, false, false, false, false, false, false);
        }

        static TargetFlags from(String normalized) {
            return new TargetFlags(
                    matchesAny(DEVICE_TARGETS, normalized),
                    matchesAny(RULE_TARGETS, normalized),
                    matchesAny(SPEC_TARGETS, normalized),
                    matchesAny(TEMPLATE_TARGETS, normalized),
                    matchesAny(BOARD_TARGETS, normalized),
                    matchesAny(TRACE_TARGETS, normalized),
                    matchesAny(VERIFICATION_TARGETS, normalized),
                    matchesAny(SIMULATION_TARGETS, normalized)
            );
        }

        boolean any() {
            return device || rule || spec || template || board || trace || verification || simulation;
        }

        boolean actionableMutationTarget() {
            return device || rule || spec || template || board;
        }

        boolean recommendationTarget() {
            return device || rule || spec || template || board;
        }

        boolean executionTarget() {
            return verification || simulation || board || spec || trace;
        }

        boolean scenarioTarget() {
            return device || rule || spec || board || simulation;
        }

        boolean readableTarget() {
            return any();
        }
    }

    private interface MatcherGroup {
        boolean matches(String value);
    }

    private static MatcherGroup regex(String regex) {
        Pattern compiled = pattern(regex);
        return value -> compiled.matcher(value).find();
    }

    private static MatcherGroup words(String... words) {
        List<String> values = Arrays.asList(words);
        return value -> values.stream().anyMatch(value::contains);
    }

    private static boolean matchesAny(List<MatcherGroup> groups, String value) {
        for (MatcherGroup group : groups) {
            if (group.matches(value)) {
                return true;
            }
        }
        return false;
    }

    private static String normalize(String value) {
        return value.toLowerCase(Locale.ROOT)
                .replace('\u3000', ' ')
                .replaceAll("\\s+", " ")
                .trim();
    }

    private static Pattern pattern(String regex) {
        return Pattern.compile(regex, Pattern.CASE_INSENSITIVE | Pattern.UNICODE_CASE);
    }
}

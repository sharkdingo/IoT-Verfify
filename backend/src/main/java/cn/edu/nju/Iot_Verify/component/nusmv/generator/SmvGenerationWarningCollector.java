package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

final class SmvGenerationWarningCollector {

    private final List<String> checkLogWarnings = new ArrayList<>();
    private final Set<String> disabledRuleKeys = new HashSet<>();
    private final Set<String> skippedSpecKeys = new HashSet<>();

    public synchronized void disabledRule(RuleDto rule, String reason) {
        String key = ruleKey(rule);
        if (disabledRuleKeys.add(key)) {
            checkLogWarnings.add("Generation warning [rule-disabled]: " + sanitize(reason));
        }
    }

    public synchronized void skippedSpec(SpecificationDto spec, String reason) {
        String key = specKey(spec);
        if (skippedSpecKeys.add(key)) {
            checkLogWarnings.add("Generation warning [spec-skipped]: " + sanitize(reason));
        }
    }

    public synchronized List<String> checkLogWarnings() {
        return List.copyOf(checkLogWarnings);
    }

    public synchronized int disabledRuleCount() {
        return disabledRuleKeys.size();
    }

    public synchronized int skippedSpecCount() {
        return skippedSpecKeys.size();
    }

    private String ruleKey(RuleDto rule) {
        if (rule == null) {
            return "rule:null";
        }
        if (rule.getId() != null) {
            return "rule:id:" + rule.getId();
        }
        return "rule:identity:" + System.identityHashCode(rule);
    }

    private String specKey(SpecificationDto spec) {
        if (spec == null) {
            return "spec:null";
        }
        if (spec.getId() != null && !spec.getId().isBlank()) {
            return "spec:id:" + spec.getId();
        }
        return "spec:identity:" + System.identityHashCode(spec);
    }

    private String sanitize(String reason) {
        if (reason == null || reason.isBlank()) {
            return "unknown reason";
        }
        return reason.replaceAll("[\\r\\n]+", " ").trim();
    }
}

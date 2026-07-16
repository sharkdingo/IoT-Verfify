package cn.edu.nju.Iot_Verify.component.fuzz.paper;

import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/** Compiles IoT-Verify structured templates 1, 3, and 4 into explicit paper-style monitors. */
public final class PaperStructuredMonitorFactory {

    public static final String ACTIVE = "active";
    public static final String AWAITING_THEN = "awaitingThen";
    public static final String VIOLATION = "violation";

    private PaperStructuredMonitorFactory() {
    }

    public static PaperMonitorFsm from(SpecificationDto specification) {
        Objects.requireNonNull(specification, "specification");
        String templateId = specification.getTemplateId();
        return switch (templateId == null ? "" : templateId) {
            case "1" -> {
                requireEmpty(specification.getIfConditions(), "ifConditions", templateId);
                requireEmpty(specification.getThenConditions(), "thenConditions", templateId);
                yield always(group(specification.getAConditions(), "aConditions"));
            }
            case "3" -> {
                requireEmpty(specification.getIfConditions(), "ifConditions", templateId);
                requireEmpty(specification.getThenConditions(), "thenConditions", templateId);
                yield never(group(specification.getAConditions(), "aConditions"));
            }
            case "4" -> immediate(
                    group(specification.getIfConditions(), "ifConditions"),
                    group(specification.getThenConditions(), "thenConditions"),
                    specification.getAConditions());
            default -> throw new IllegalArgumentException(
                    "Paper monitor supports only structured templates 1, 3, and 4");
        };
    }

    private static PaperMonitorFsm always(PaperCondition condition) {
        return baseBuilder()
                .transition(ACTIVE, ACTIVE, condition)
                .transition(ACTIVE, VIOLATION, PaperCondition.not(condition))
                .build();
    }

    private static PaperMonitorFsm never(PaperCondition condition) {
        return baseBuilder()
                .transition(ACTIVE, VIOLATION, condition)
                .transition(ACTIVE, ACTIVE, PaperCondition.not(condition))
                .build();
    }

    private static PaperMonitorFsm immediate(
            PaperCondition antecedent,
            PaperCondition consequent,
            List<SpecConditionDto> aConditions) {
        if (aConditions != null && !aConditions.isEmpty()) {
            throw new IllegalArgumentException("Template 4 cannot contain aConditions");
        }
        return PaperMonitorFsm.builder(ACTIVE)
                .state(ACTIVE, PaperTruthValue.INCONCLUSIVE)
                .state(AWAITING_THEN, PaperTruthValue.INCONCLUSIVE)
                .state(VIOLATION, PaperTruthValue.FALSE)
                .transition(ACTIVE, AWAITING_THEN, antecedent)
                .transition(ACTIVE, ACTIVE, PaperCondition.not(antecedent))
                .transition(AWAITING_THEN, VIOLATION, PaperCondition.not(consequent))
                .transition(AWAITING_THEN, AWAITING_THEN, PaperCondition.allOf(consequent, antecedent))
                .transition(AWAITING_THEN, ACTIVE,
                        PaperCondition.allOf(consequent, PaperCondition.not(antecedent)))
                .transition(VIOLATION, VIOLATION, PaperCondition.TRUE)
                .build();
    }

    private static PaperMonitorFsm.Builder baseBuilder() {
        return PaperMonitorFsm.builder(ACTIVE)
                .state(ACTIVE, PaperTruthValue.INCONCLUSIVE)
                .state(VIOLATION, PaperTruthValue.FALSE)
                .transition(VIOLATION, VIOLATION, PaperCondition.TRUE);
    }

    private static PaperCondition group(List<SpecConditionDto> conditions, String field) {
        if (conditions == null || conditions.isEmpty()) {
            throw new IllegalArgumentException(field + " must contain at least one condition");
        }
        List<PaperCondition> atoms = new ArrayList<>(conditions.size());
        for (SpecConditionDto condition : conditions) {
            atoms.add(PaperCondition.atom(PaperAtom.from(condition)));
        }
        return PaperCondition.allOf(atoms);
    }

    private static void requireEmpty(List<?> values, String field, String templateId) {
        if (values != null && !values.isEmpty()) {
            throw new IllegalArgumentException("Template " + templateId + " cannot contain " + field);
        }
    }
}

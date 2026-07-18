package cn.edu.nju.Iot_Verify.dto.model;

import com.fasterxml.jackson.annotation.JsonIgnore;
import jakarta.validation.Valid;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/** Per-run attack scenario, independent from persistent trust labels on the board. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class AttackScenarioDto {

    public enum Mode {
        NONE,
        EXACT_POINTS,
        ANY_UP_TO_BUDGET
    }

    @Builder.Default
    private Mode mode = Mode.NONE;

    private Integer budget;

    @Valid
    @Builder.Default
    private List<AttackPointDto> points = new ArrayList<>();

    public static AttackScenarioDto none() {
        return AttackScenarioDto.builder().mode(Mode.NONE).budget(0).points(List.of()).build();
    }

    public static AttackScenarioDto anyUpToBudget(int budget) {
        return AttackScenarioDto.builder()
                .mode(Mode.ANY_UP_TO_BUDGET)
                .budget(budget)
                .points(List.of())
                .build();
    }

    public static AttackScenarioDto exactPoints(List<AttackPointDto> points) {
        List<AttackPointDto> safePoints = points == null ? List.of() : List.copyOf(points);
        return AttackScenarioDto.builder()
                .mode(Mode.EXACT_POINTS)
                .budget(null)
                .points(safePoints)
                .build();
    }

    @JsonIgnore
    public boolean isEnabled() {
        return mode != null && mode != Mode.NONE;
    }

    @JsonIgnore
    public int effectiveBudget() {
        if (mode == Mode.EXACT_POINTS) {
            return points == null ? 0 : points.size();
        }
        return mode == Mode.ANY_UP_TO_BUDGET && budget != null ? budget : 0;
    }

    @JsonIgnore
    public Set<String> selectedDeviceIds() {
        Set<String> result = new LinkedHashSet<>();
        if (points == null) {
            return result;
        }
        for (AttackPointDto point : points) {
            if (point != null && point.getKind() == AttackPointDto.Kind.DEVICE
                    && point.getDeviceId() != null) {
                result.add(point.getDeviceId());
            }
        }
        return result;
    }

    @JsonIgnore
    public Set<Long> selectedAutomationLinkRuleIds() {
        Set<Long> result = new LinkedHashSet<>();
        if (points == null) {
            return result;
        }
        for (AttackPointDto point : points) {
            if (point != null && point.getKind() == AttackPointDto.Kind.AUTOMATION_LINK
                    && point.getRuleId() != null) {
                result.add(point.getRuleId());
            }
        }
        return result;
    }
}

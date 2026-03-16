package cn.edu.nju.Iot_Verify.dto.fix;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import lombok.Data;

import java.util.List;
import java.util.Map;

@Data
@JsonIgnoreProperties(ignoreUnknown = true)
public class FixRequestDto {
    /** Strategies to attempt, e.g. ["parameter","condition","disable"]. When null/empty, defaults to all three in order. */
    private List<String> strategies;

    /**
     * Optional per-parameter preferred ranges, keyed by "r{ruleIdx}_c{condIdx}".
     * Validation is handled by {@link cn.edu.nju.Iot_Verify.service.impl.FixServiceImpl#validatePreferredRanges}
     * rather than Bean Validation, because {@code @Valid} on Map values has inconsistent
     * cascade behavior across Spring Boot versions.
     */
    private Map<String, PreferredRange> preferredRanges;
}

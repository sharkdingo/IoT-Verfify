package cn.edu.nju.Iot_Verify.dto.fuzz;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FuzzEligibilityDto {
    @Builder.Default
    private List<String> eligibleSpecIds = new ArrayList<>();
    @Builder.Default
    private Map<String, String> eligibleSpecLabels = new LinkedHashMap<>();
    @Builder.Default
    private List<FuzzIneligibleSpecDto> ineligibleSpecs = new ArrayList<>();
    private int requestedSpecCount;
    private int eligibleSpecCount;
}

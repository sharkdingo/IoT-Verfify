package cn.edu.nju.Iot_Verify.dto.fuzz;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.List;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FuzzPaperEnvironmentDomainDto {

    private String name;
    private String targetId;
    private String property;
    private String eventValueKind;
    private Integer initialLowerBound;
    private Integer initialUpperBound;
    private Integer eventRateLowerBound;
    private Integer eventRateUpperBound;

    @Builder.Default
    private List<String> initialValues = new ArrayList<>();

    @Builder.Default
    private List<String> eventValues = new ArrayList<>();
}

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
public class FuzzPaperDomainPreviewDto {

    private int pathLength;
    private String initializationPolicy;
    private String modelFingerprint;

    @Builder.Default
    private List<String> paperSemanticsCodes = new ArrayList<>();

    @Builder.Default
    private List<FuzzPaperDeviceDomainDto> deviceDomains = new ArrayList<>();

    @Builder.Default
    private List<FuzzPaperDeviceDomainDto> localVariableDomains = new ArrayList<>();

    @Builder.Default
    private List<FuzzPaperEnvironmentDomainDto> environmentDomains = new ArrayList<>();
}

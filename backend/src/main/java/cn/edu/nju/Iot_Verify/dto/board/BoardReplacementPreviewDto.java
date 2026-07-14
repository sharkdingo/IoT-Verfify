package cn.edu.nju.Iot_Verify.dto.board;

import lombok.Builder;
import lombok.Data;

/** Authoritative current-board impact shown before an explicit full-scene replacement. */
@Data
@Builder
public class BoardReplacementPreviewDto {
    private String impactToken;
    private int deviceCount;
    private int environmentVariableCount;
    private int ruleCount;
    private int specificationCount;
}

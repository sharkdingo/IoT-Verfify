package cn.edu.nju.Iot_Verify.dto.model;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

/** Display-ready snapshot of one exact attack point selected for a completed run. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class SelectedAttackPointDto {
    private AttackPointDto.Kind kind;
    private String deviceId;
    private Long ruleId;
    private String displayLabel;
}

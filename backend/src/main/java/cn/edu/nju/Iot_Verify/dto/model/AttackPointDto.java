package cn.edu.nju.Iot_Verify.dto.model;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

/** One behavior-changing compromise point selected for a single model run. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class AttackPointDto {

    public enum Kind {
        DEVICE,
        AUTOMATION_LINK
    }

    private Kind kind;
    private String deviceId;
    private Long ruleId;

    public static AttackPointDto device(String deviceId) {
        return AttackPointDto.builder()
                .kind(Kind.DEVICE)
                .deviceId(deviceId)
                .build();
    }

    public static AttackPointDto automationLink(Long ruleId) {
        return AttackPointDto.builder()
                .kind(Kind.AUTOMATION_LINK)
                .ruleId(ruleId)
                .build();
    }

    public String identityKey() {
        if (kind == Kind.DEVICE) {
            return "DEVICE:" + (deviceId == null ? "" : deviceId);
        }
        if (kind == Kind.AUTOMATION_LINK) {
            return "AUTOMATION_LINK:" + (ruleId == null ? "" : ruleId);
        }
        return "UNKNOWN";
    }
}

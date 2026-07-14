package cn.edu.nju.Iot_Verify.dto.recommendation;

import com.fasterxml.jackson.annotation.JsonInclude;
import lombok.Data;

import java.util.List;

@Data
@JsonInclude(JsonInclude.Include.NON_NULL)
public class DeviceRecommendationDto {
    private String templateName;
    private String suggestedLabel;
    /** Advisory context only; not persisted as a device-instance or formal-model field. */
    private String intendedUse;
    /** Advisory placement only; not persisted as a device-instance or formal-model field. */
    private String suggestedPlacement;
    private String description;
    private String reason;
    private String initialState;
    private String currentStateTrust;
    private String currentStatePrivacy;
    private List<InitialVariableDto> initialVariables;
    private List<InitialPrivacyDto> initialPrivacies;

    @Data
    @JsonInclude(JsonInclude.Include.NON_NULL)
    public static class InitialVariableDto {
        private String name;
        private String value;
        private String trust;
    }

    @Data
    @JsonInclude(JsonInclude.Include.NON_NULL)
    public static class InitialPrivacyDto {
        private String name;
        private String privacy;
    }
}

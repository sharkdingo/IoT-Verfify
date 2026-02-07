package cn.edu.nju.Iot_Verify.dto.device;

import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

@Data
public class DeviceNodeDto {

    @NotBlank(message = "Node ID is required")
    private String id;

    @NotBlank(message = "Template name is required")
    private String templateName;

    private String label;

    @Valid
    @NotNull(message = "Position is required")
    private Position position;

    private String state;

    private Integer width;

    private Integer height;

    // 运行时状态
    private String currentStateTrust;
    private List<VariableStateDto> variables;
    private List<PrivacyStateDto> privacies;

    @Data
    public static class Position {
        @NotNull(message = "X coordinate is required")
        private Double x;

        @NotNull(message = "Y coordinate is required")
        private Double y;
    }

    /**
     * 设备变量状态
     */
    @Data
    @NoArgsConstructor
    @AllArgsConstructor
    public static class VariableStateDto {
        private String name;
        private String value;
        private String trust;
    }

    /**
     * 设备隐私状态
     */
    @Data
    @NoArgsConstructor
    @AllArgsConstructor
    public static class PrivacyStateDto {
        private String name;
        private String privacy;
    }
}

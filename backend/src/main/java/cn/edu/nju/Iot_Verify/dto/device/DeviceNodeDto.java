package cn.edu.nju.Iot_Verify.dto.device;

import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Size;
import lombok.Data;

import java.util.List;

@Data
public class DeviceNodeDto {

    @NotBlank(message = "Node ID is required")
    @Size(max = 100, message = "Node ID must be at most 100 characters")
    private String id;

    @NotBlank(message = "Template name is required")
    @Size(max = 100, message = "Template name must be at most 100 characters")
    private String templateName;

    @NotBlank(message = "Label is required")
    @Size(max = 255, message = "Label must be at most 255 characters")
    private String label;

    @Valid
    @NotNull(message = "Position is required")
    private Position position;

    @NotBlank(message = "State is required")
    @Size(max = 50, message = "State must be at most 50 characters")
    private String state;

    @NotNull(message = "Width is required")
    private Integer width;

    @NotNull(message = "Height is required")
    private Integer height;

    // 运行时状态（持久化需要，同时可用于从画布数据转换为验证数据）
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
}

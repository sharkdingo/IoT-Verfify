package cn.edu.nju.Iot_Verify.dto;

import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import lombok.Data;

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

    @Data
    public static class Position {
        @NotNull(message = "X coordinate is required")
        private Double x;

        @NotNull(message = "Y coordinate is required")
        private Double y;
    }
}

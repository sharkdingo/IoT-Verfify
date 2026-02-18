package cn.edu.nju.Iot_Verify.dto.rule;

import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import lombok.Data;

@Data
public class DeviceEdgeDto {

    @NotBlank(message = "Edge ID is required")
    private String id;

    @NotBlank(message = "Source node ID is required")
    private String from;

    @NotBlank(message = "Target node ID is required")
    private String to;

    @NotBlank(message = "Source label is required")
    private String fromLabel;

    @NotBlank(message = "Target label is required")
    private String toLabel;

    @Valid
    @NotNull(message = "Source position is required")
    private Point fromPos;

    @Valid
    @NotNull(message = "Target position is required")
    private Point toPos;

    @Data
    public static class Point {
        @NotNull(message = "X coordinate is required")
        private Double x;

        @NotNull(message = "Y coordinate is required")
        private Double y;
    }
}

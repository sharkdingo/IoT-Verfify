package cn.edu.nju.Iot_Verify.dto.rule;

import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Size;
import lombok.Data;

@Data
public class DeviceEdgeDto {

    @NotBlank(message = "Edge ID is required")
    @Size(max = 100, message = "Edge ID must be at most 100 characters")
    private String id;

    @NotBlank(message = "Source node ID is required")
    @Size(max = 100, message = "Source node ID must be at most 100 characters")
    private String from;

    @NotBlank(message = "Target node ID is required")
    @Size(max = 100, message = "Target node ID must be at most 100 characters")
    private String to;

    @NotBlank(message = "Source label is required")
    @Size(max = 255, message = "Source label must be at most 255 characters")
    private String fromLabel;

    @NotBlank(message = "Target label is required")
    @Size(max = 255, message = "Target label must be at most 255 characters")
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

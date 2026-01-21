package cn.edu.nju.Iot_Verify.dto;

import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import lombok.Data;

@Data
public class DeviceEdgeDto {

    @NotBlank(message = "Edge ID is required")
    private String id;

    @NotBlank(message = "Source node ID is required")
    private String from;

    @NotBlank(message = "Target node ID is required")
    private String to;

    private String fromLabel;
    private String toLabel;
    private String fromApi;
    private String toApi;

    @Valid
    private Point fromPos;

    @Valid
    private Point toPos;

    @Data
    public static class Point {
        private Double x;
        private Double y;
    }
}

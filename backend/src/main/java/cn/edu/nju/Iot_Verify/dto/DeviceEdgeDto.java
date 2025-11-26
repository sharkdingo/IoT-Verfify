// src/main/java/cn/edu/nju/Iot_Verify/dto/DeviceEdgeDto.java
package cn.edu.nju.Iot_Verify.dto;

import lombok.Data;

@Data
public class DeviceEdgeDto {
    private String id;
    private String from;
    private String to;
    private String fromLabel;
    private String toLabel;
    private String fromApi;
    private String toApi;
    private Point fromPos;
    private Point toPos;

    @Data
    public static class Point {
        private Double x;
        private Double y;
    }
}

// src/main/java/cn/edu/nju/Iot_Verify/dto/DeviceNodeDto.java
package cn.edu.nju.Iot_Verify.dto;

import lombok.Data;

@Data
public class DeviceNodeDto {
    private String id;
    private String templateName;
    private String label;
    private Position position;
    private String state;
    private Integer width;
    private Integer height;

    @Data
    public static class Position {
        private Double x;
        private Double y;
    }
}

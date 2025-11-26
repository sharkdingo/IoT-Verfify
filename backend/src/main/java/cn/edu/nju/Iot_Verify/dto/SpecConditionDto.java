// src/main/java/cn/edu/nju/Iot_Verify/dto/SpecConditionDto.java
package cn.edu.nju.Iot_Verify.dto;

import lombok.Data;

@Data
public class SpecConditionDto {
    private String id;
    private String side;        // 'a' | 'if' | 'then'
    private String deviceId;
    private String deviceLabel;
    private String targetType;  // 'state' | 'variable' | 'api'
    private String key;
    private String relation;
    private String value;
}

// src/main/java/cn/edu/nju/Iot_Verify/dto/BoardActiveDto.java
package cn.edu.nju.Iot_Verify.dto;

import lombok.Data;

import java.util.List;

@Data
public class BoardActiveDto {
    private List<String> input;
    private List<String> status;
}

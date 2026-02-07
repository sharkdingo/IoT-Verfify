// src/main/java/cn/edu/nju/Iot_Verify/dto/board/BoardActiveDto.java
package cn.edu.nju.Iot_Verify.dto.board;

import lombok.Data;

import java.util.List;

@Data
public class BoardActiveDto {
    private List<String> input;
    private List<String> status;
}

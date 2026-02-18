// src/main/java/cn/edu/nju/Iot_Verify/dto/board/BoardActiveDto.java
package cn.edu.nju.Iot_Verify.dto.board;

import jakarta.validation.constraints.NotNull;
import lombok.Data;

import java.util.List;

@Data
public class BoardActiveDto {
    @NotNull(message = "Input tabs cannot be null")
    private List<String> input;

    @NotNull(message = "Status tabs cannot be null")
    private List<String> status;
}

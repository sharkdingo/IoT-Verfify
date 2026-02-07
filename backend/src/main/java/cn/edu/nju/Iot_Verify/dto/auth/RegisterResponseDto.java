package cn.edu.nju.Iot_Verify.dto.auth;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class RegisterResponseDto {
    private Long userId;
    private String phone;
    private String username;
}

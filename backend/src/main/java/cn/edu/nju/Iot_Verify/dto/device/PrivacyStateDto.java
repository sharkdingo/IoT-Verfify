package cn.edu.nju.Iot_Verify.dto.device;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import jakarta.validation.constraints.Size;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * 设备隐私状态
 *
 * 用于表示设备实例的隐私等级覆盖。
 * - name: 目标名称（可以是状态隐私键或 InternalVariable.Name）
 * - privacy: 隐私等级覆盖（如 "public" / "private"）
 */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class PrivacyStateDto {
    @Size(max = RequestLimits.MAX_IDENTIFIER_LENGTH, message = "Privacy target name must be at most 200 characters")
    private String name;
    @Size(max = 20, message = "Privacy label must be at most 20 characters")
    private String privacy;
}

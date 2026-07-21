package cn.edu.nju.Iot_Verify.dto.device;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import jakarta.validation.constraints.Size;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * 设备变量状态
 *
 * 用于表示设备实例的变量运行时值和信任等级。
 * - name: 变量名（对应模板 InternalVariable.Name）
 * - value: 当前值
 * - trust: 信任等级覆盖（如 "trusted" / "untrusted"）
 */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class VariableStateDto {
    @Size(max = RequestLimits.MAX_IDENTIFIER_LENGTH, message = "Variable name must be at most 200 characters")
    private String name;
    @Size(max = RequestLimits.MAX_VALUE_LENGTH, message = "Variable value must be at most 1000 characters")
    private String value;
    @Size(max = 20, message = "Variable trust must be at most 20 characters")
    private String trust;
}

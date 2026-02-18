package cn.edu.nju.Iot_Verify.dto.device;

import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * 设备变量状态
 *
 * 用于表示设备实例的变量运行时值和信任等级。
 * - name: 变量名（对应模板 InternalVariable.Name 或 Mode 名）
 * - value: 当前值
 * - trust: 信任等级覆盖（如 "trusted" / "untrusted"）
 */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class VariableStateDto {
    private String name;
    private String value;
    private String trust;
}

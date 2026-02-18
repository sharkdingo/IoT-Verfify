package cn.edu.nju.Iot_Verify.dto.device;

import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * 设备隐私状态
 *
 * 用于表示设备实例的隐私等级覆盖。
 * - name: 目标名称（可以是状态名、变量名或内容名）
 * - privacy: 隐私等级覆盖（如 "public" / "private"）
 */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class PrivacyStateDto {
    private String name;
    private String privacy;
}

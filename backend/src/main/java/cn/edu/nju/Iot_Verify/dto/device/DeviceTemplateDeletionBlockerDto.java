package cn.edu.nju.Iot_Verify.dto.device;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class DeviceTemplateDeletionBlockerDto {
    private String reasonCode;
    private String itemId;
    private String itemLabel;
    private String reason;
}

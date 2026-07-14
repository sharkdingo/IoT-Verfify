package cn.edu.nju.Iot_Verify.dto.device;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class DefaultTemplateResetBlockerDto {
    private String itemLabel;
    private String reasonCode;
    private String reason;
}

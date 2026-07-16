package cn.edu.nju.Iot_Verify.dto.fuzz;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FuzzIneligibleSpecDto {
    private String specId;
    private String specificationLabel;
    private String reasonCode;
    private String reason;
}

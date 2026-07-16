package cn.edu.nju.Iot_Verify.dto.fuzz;

import cn.edu.nju.Iot_Verify.component.fuzz.FuzzInputEventSource;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FuzzInputEventDto {
    private int step;
    private String kind;
    private String targetId;
    private String property;
    private String value;
    @Builder.Default
    private String source = FuzzInputEventSource.MODEL_CHOICE.name();
}

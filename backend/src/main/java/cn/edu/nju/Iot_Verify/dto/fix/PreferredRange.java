package cn.edu.nju.Iot_Verify.dto.fix;

import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@NoArgsConstructor
@AllArgsConstructor
public class PreferredRange {
    @NotNull private Integer lower;
    @NotNull private Integer upper;
}

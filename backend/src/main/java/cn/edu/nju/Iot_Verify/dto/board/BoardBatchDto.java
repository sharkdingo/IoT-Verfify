// src/main/java/cn/edu/nju/Iot_Verify/dto/board/BoardBatchDto.java
package cn.edu.nju.Iot_Verify.dto.board;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * Batch save of the three interdependent board collections in one transaction.
 *
 * <p>Used by device delete / rename where nodes, rules and specs must change together — persisting
 * them via three separate requests risks a partial save (e.g. node renamed but specs still reference
 * the old label, or a device deleted but its rules left dangling).</p>
 *
 * <p>A {@code null} collection means "leave this collection unchanged" (the server returns the current
 * persisted value for it); a non-null collection fully replaces / upserts per the same semantics as the
 * dedicated {@code saveNodes}/{@code saveRules}/{@code saveSpecs} endpoints.</p>
 */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class BoardBatchDto {

    @Valid
    private List<@Valid @NotNull(message = "Node item cannot be null") DeviceNodeDto> nodes;

    @Valid
    private List<@Valid @NotNull(message = "Rule item cannot be null") RuleDto> rules;

    @Valid
    private List<@Valid @NotNull(message = "Specification item cannot be null") SpecificationDto> specs;
}

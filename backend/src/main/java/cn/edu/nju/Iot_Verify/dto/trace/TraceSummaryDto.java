package cn.edu.nju.Iot_Verify.dto.trace;

import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import com.fasterxml.jackson.annotation.JsonInclude;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;

/** Lightweight counterexample evidence for run-history lists. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class TraceSummaryDto {
    private Long id;
    private Long verificationTaskId;
    private String violatedSpecId;
    private SpecificationDto violatedSpec;
    private Integer stateCount;
    private LocalDateTime createdAt;

    /**
     * Whether this counterexample's run still holds the SMV model it checked, gating
     * {@code GET /api/verify/traces/{id}/smv}. Presence only — the model itself runs to tens of
     * thousands of characters and would dominate a history list.
     *
     * <p>The history panel already gated its per-counterexample download on this, but the field was
     * never populated here, so the button never appeared. Null on an unavailable record, where nothing
     * about the model can be asserted.
     */
    private Boolean hasSmvModel;

    @Builder.Default
    private Boolean dataAvailable = true;
    private String unavailableReasonCode;
}

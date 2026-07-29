package cn.edu.nju.Iot_Verify.dto.board;

import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.Pattern;
import lombok.Data;
import lombok.ToString;

/** Confirmation token for clearing exactly the journal state the user reviewed. */
@Data
public class BoardEditHistoryClearRequestDto {
    @NotBlank(message = "Undo-history impactToken is required")
    @Pattern(regexp = "^[0-9a-f]{64}$", message = "Undo-history impactToken must be a SHA-256 token")
    @ToString.Exclude
    private String impactToken;
}

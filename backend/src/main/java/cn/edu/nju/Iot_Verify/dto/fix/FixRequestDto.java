package cn.edu.nju.Iot_Verify.dto.fix;

import com.fasterxml.jackson.annotation.JsonIgnore;
import jakarta.validation.Valid;
import jakarta.validation.constraints.AssertTrue;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Pattern;
import jakarta.validation.constraints.Size;
import lombok.Data;

import java.util.HashSet;
import java.util.List;

@Data
public class FixRequestDto {
    /** Strategies to attempt. Null/omitted uses the default order; an explicit list is exact. */
    @Size(min = 1, message = "strategies must be non-empty when provided; omit it to use defaults")
    private List<
            @NotBlank(message = "strategy item must not be blank")
            @Pattern(regexp = "parameter|condition|remove",
                    message = "strategy must be one of parameter, condition, remove")
            String> strategies;

    /**
     * Optional preferred ranges chosen from concrete parameter-adjustment targets.
     * The controller converts these selections to the fixer's internal locator map.
     */
    private List<@Valid @NotNull(message = "preferredRangeSelections item must not be null")
            PreferredRangeSelection> preferredRangeSelections;

    @JsonIgnore
    @AssertTrue(message = "strategies must not contain duplicates")
    public boolean isStrategyOrderUnique() {
        return strategies == null || new HashSet<>(strategies).size() == strategies.size();
    }
}

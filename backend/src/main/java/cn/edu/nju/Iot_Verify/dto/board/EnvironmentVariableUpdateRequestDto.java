package cn.edu.nju.Iot_Verify.dto.board;

import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonSetter;
import com.fasterxml.jackson.annotation.Nulls;
import jakarta.validation.Valid;
import jakarta.validation.constraints.AssertTrue;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Size;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

/** Compare-and-set field patch for one Board Environment Pool variable. */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class EnvironmentVariableUpdateRequestDto {

    @NotBlank(message = "Environment variable name is required")
    @Size(max = 100, message = "Environment variable name must be at most 100 characters")
    private String name;

    @Valid
    @NotNull(message = "Expected environment variable configuration is required")
    private ExpectedValue expected;

    @Valid
    @NotNull(message = "Desired environment variable patch is required")
    private DesiredPatch desired;

    /** Complete baseline returned by the Environment Pool read. */
    @Data
    @NoArgsConstructor
    @AllArgsConstructor
    public static class ExpectedValue {

        @NotBlank(message = "Expected environment variable value is required")
        @Size(max = 255, message = "Expected environment variable value must be at most 255 characters")
        private String value;

        @NotBlank(message = "Expected environment variable trust is required")
        @Size(max = 20, message = "Expected environment variable trust must be at most 20 characters")
        private String trust;

        @NotBlank(message = "Expected environment variable privacy is required")
        @Size(max = 20, message = "Expected environment variable privacy must be at most 20 characters")
        private String privacy;
    }

    /** Supplied fields replace their matching values after the baseline still matches. */
    @Data
    @NoArgsConstructor
    @AllArgsConstructor
    public static class DesiredPatch {

        @JsonSetter(nulls = Nulls.FAIL)
        @Size(max = 255, message = "Environment variable value must be at most 255 characters")
        private String value;

        @JsonSetter(nulls = Nulls.FAIL)
        @Size(max = 20, message = "Environment variable trust must be at most 20 characters")
        private String trust;

        @JsonSetter(nulls = Nulls.FAIL)
        @Size(max = 20, message = "Environment variable privacy must be at most 20 characters")
        private String privacy;

        @JsonIgnore
        @AssertTrue(message = "At least one desired environment variable field is required")
        public boolean isFieldProvided() {
            return value != null || trust != null || privacy != null;
        }
    }
}

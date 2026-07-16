package cn.edu.nju.Iot_Verify.dto.fuzz;

import jakarta.validation.constraints.Max;
import jakarta.validation.constraints.Min;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Pattern;
import jakarta.validation.constraints.Size;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.List;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FuzzRequestDto {

    public static final long JS_SAFE_SEED_MAX = 9_007_199_254_740_991L;

    @NotNull(message = "Exploration mode cannot be null")
    @Builder.Default
    private FuzzExplorationMode explorationMode = FuzzExplorationMode.BOARD_SNAPSHOT;

    @Pattern(
            regexp = "^[0-9a-f]{64}$",
            message = "Input-range fingerprint must be a 64-character lowercase SHA-256 value")
    private String paperDomainFingerprint;

    @Builder.Default
    @Size(max = 100, message = "At most 100 target specifications can be selected")
    private List<@NotBlank(message = "Target specification ID cannot be blank")
            @Size(max = 100, message = "Target specification ID must be at most 100 characters") String>
            targetSpecIds = new ArrayList<>();

    @NotNull(message = "Maximum iterations cannot be null")
    @Min(value = 1, message = "Maximum iterations must be at least 1")
    @Max(value = 5_000, message = "Maximum iterations must be at most 5000")
    @Builder.Default
    private Integer maxIterations = 1_000;

    @NotNull(message = "Path length cannot be null")
    @Min(value = 1, message = "Path length must be at least 1")
    @Max(value = 50, message = "Path length must be at most 50")
    @Builder.Default
    private Integer pathLength = 20;

    @NotNull(message = "Population size cannot be null")
    @Min(value = 1, message = "Population size must be at least 1")
    @Max(value = 50, message = "Population size must be at most 50")
    @Builder.Default
    private Integer populationSize = 10;

    @Min(value = 0, message = "Seed must not be negative")
    @Max(value = JS_SAFE_SEED_MAX, message = "Seed exceeds JavaScript's safe integer range")
    private Long seed;
}

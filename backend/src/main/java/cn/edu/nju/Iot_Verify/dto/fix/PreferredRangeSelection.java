package cn.edu.nju.Iot_Verify.dto.fix;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonIgnore;
import jakarta.validation.constraints.AssertTrue;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Base64;
import java.util.regex.Pattern;

/**
 * User/API-facing target for a preferred parameter-adjustment range.
 *
 * <p>Clients select an opaque {@code targetId} returned on a {@link ParameterTarget}.
 * The fixer matches this id against currently available parameter-adjustment targets; REST/AI
 * callers no longer type zero-based indices or {@code r*_c*} locator keys.</p>
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class PreferredRangeSelection {
    private static final String TARGET_PREFIX = "param_";
    private static final Pattern TARGET_ID_PATTERN = Pattern.compile("param_[A-Za-z0-9_-]{24}");

    @NotBlank(message = "targetId must not be blank")
    @jakarta.validation.constraints.Pattern(regexp = "param_[A-Za-z0-9_-]{24}",
            message = "targetId must be a valid parameter-adjustment selector")
    private String targetId;
    @NotNull(message = "lower must not be null")
    private Integer lower;
    @NotNull(message = "upper must not be null")
    private Integer upper;

    @JsonIgnore
    @AssertTrue(message = "lower must be less than or equal to upper")
    public boolean isRangeOrdered() {
        return lower == null || upper == null || lower <= upper;
    }

    public static String targetIdFor(int ruleIndex, int conditionIndex) {
        return targetIdFor(null, ruleIndex, conditionIndex);
    }

    public static String targetIdFor(Long traceId, int ruleIndex, int conditionIndex) {
        String key = "r" + ruleIndex + "_c" + conditionIndex;
        String scope = traceId == null ? "trace:none" : "trace:" + traceId;
        byte[] digest = sha256("preferred-range-target:" + scope + ":" + key);
        return TARGET_PREFIX + Base64.getUrlEncoder().withoutPadding()
                .encodeToString(Arrays.copyOf(digest, 18));
    }

    public static boolean isValidTargetId(String targetId) {
        return targetId != null && TARGET_ID_PATTERN.matcher(targetId).matches();
    }

    private static byte[] sha256(String value) {
        try {
            return MessageDigest.getInstance("SHA-256").digest(value.getBytes(StandardCharsets.UTF_8));
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException("SHA-256 is not available", e);
        }
    }

    public PreferredRange toPreferredRange() {
        return new PreferredRange(lower, upper);
    }
}

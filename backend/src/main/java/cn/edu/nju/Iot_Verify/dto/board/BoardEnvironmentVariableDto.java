package cn.edu.nju.Iot_Verify.dto.board;

import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.Size;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * Board-level environment variable value.
 *
 * <p>Device templates declare which environment variables a device may read or affect. The actual
 * value, trust and privacy are owned by the board's environment pool, not by any individual device node.</p>
 */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class BoardEnvironmentVariableDto {

    @NotBlank(message = "Environment variable name is required")
    @Size(max = 100, message = "Environment variable name must be at most 100 characters")
    private String name;

    @Size(max = 255, message = "Environment variable value must be at most 255 characters")
    private String value;

    private String trust;

    private String privacy;
}

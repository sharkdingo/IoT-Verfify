package cn.edu.nju.Iot_Verify.dto.device;

import jakarta.validation.Valid;
import jakarta.validation.constraints.Max;
import jakarta.validation.constraints.Min;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

/** Canvas-only position and dimensions for one device instance. */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class DeviceLayoutDto {

    public static final int MIN_WIDTH = 80;
    public static final int MAX_WIDTH = 2000;
    public static final int MIN_HEIGHT = 60;
    public static final int MAX_HEIGHT = 2000;
    public static final double MAX_ABS_POSITION = 1_000_000;

    @Valid
    @NotNull(message = "Position is required")
    private DeviceNodeDto.Position position;

    @NotNull(message = "Width is required")
    @Min(value = MIN_WIDTH, message = "Width must be at least 80")
    @Max(value = MAX_WIDTH, message = "Width must be at most 2000")
    private Integer width;

    @NotNull(message = "Height is required")
    @Min(value = MIN_HEIGHT, message = "Height must be at least 60")
    @Max(value = MAX_HEIGHT, message = "Height must be at most 2000")
    private Integer height;
}

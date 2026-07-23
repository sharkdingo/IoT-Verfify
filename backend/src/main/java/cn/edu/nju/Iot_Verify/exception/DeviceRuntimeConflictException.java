package cn.edu.nju.Iot_Verify.exception;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import lombok.Getter;

/** The device runtime changed after the caller captured its edit baseline. */
@Getter
public class DeviceRuntimeConflictException extends ConflictException {

    public static final String REASON_CODE = "DEVICE_RUNTIME_STALE";

    private final DeviceNodeDto currentDevice;

    public DeviceRuntimeConflictException(DeviceNodeDto currentDevice) {
        super("The device configuration changed after editing began. Review the latest values before saving again.");
        this.currentDevice = currentDevice;
    }
}

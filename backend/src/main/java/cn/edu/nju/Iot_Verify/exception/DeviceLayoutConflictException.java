package cn.edu.nju.Iot_Verify.exception;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import lombok.Getter;

/** The device layout changed after the caller captured its edit baseline. */
@Getter
public class DeviceLayoutConflictException extends ConflictException {

    private final DeviceNodeDto currentDevice;

    public DeviceLayoutConflictException(DeviceNodeDto currentDevice) {
        super("The device layout changed after editing began. Review its latest position and size before saving again.");
        this.currentDevice = currentDevice;
    }
}

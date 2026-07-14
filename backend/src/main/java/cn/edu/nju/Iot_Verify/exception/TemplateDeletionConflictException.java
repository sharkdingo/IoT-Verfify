package cn.edu.nju.Iot_Verify.exception;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDeletionResultDto;
import lombok.Getter;

@Getter
public class TemplateDeletionConflictException extends ConflictException {
    private final String reasonCode;
    private final DeviceTemplateDeletionResultDto currentPreview;

    public TemplateDeletionConflictException(
            String reasonCode, String message, DeviceTemplateDeletionResultDto currentPreview) {
        super(message);
        this.reasonCode = reasonCode;
        this.currentPreview = currentPreview;
    }
}

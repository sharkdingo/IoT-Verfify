package cn.edu.nju.Iot_Verify.exception;

import lombok.Getter;

/** An explicitly requested device display name is already used on the board. */
@Getter
public class DeviceLabelConflictException extends ConflictException {

    private final String requestedLabel;
    private final String suggestedLabel;

    public DeviceLabelConflictException(String requestedLabel, String suggestedLabel) {
        super("Display name '" + requestedLabel + "' is already in use. No device was created; "
                + "use '" + suggestedLabel + "' or choose another name.");
        this.requestedLabel = requestedLabel;
        this.suggestedLabel = suggestedLabel;
    }
}

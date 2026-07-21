package cn.edu.nju.Iot_Verify.exception;

import lombok.Getter;

@Getter
public class UserOperationBusyException extends BaseException {

    private final String reasonCode;
    private final String operationKind;
    private final String scope;
    private final int limit;

    public UserOperationBusyException(
            String operationKind, String scope, int limit, String message) {
        super(429, message);
        this.operationKind = operationKind;
        this.reasonCode = "USER_" + operationKind + "_OPERATION_BUSY";
        this.scope = scope;
        this.limit = limit;
    }
}

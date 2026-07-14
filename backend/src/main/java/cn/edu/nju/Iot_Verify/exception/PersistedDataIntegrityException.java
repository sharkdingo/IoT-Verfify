package cn.edu.nju.Iot_Verify.exception;

import lombok.Getter;

/** Raised when persisted semantic data cannot be reconstructed without changing its meaning. */
@Getter
public class PersistedDataIntegrityException extends BaseException {

    private final String reasonCode;
    private final String recordType;
    private final String recordId;
    private final String field;

    public PersistedDataIntegrityException(String recordType, Object recordId, String field, Throwable cause) {
        super(500, "Stored " + recordType + " data is invalid in field '" + field + "'", cause);
        this.reasonCode = "PERSISTED_SEMANTIC_DATA_INVALID";
        this.recordType = recordType;
        this.recordId = recordId != null ? String.valueOf(recordId) : null;
        this.field = field;
    }

    public PersistedDataIntegrityException(String recordType, Object recordId, String field, String detail) {
        super(500, "Stored " + recordType + " data is invalid in field '" + field + "': " + detail);
        this.reasonCode = "PERSISTED_SEMANTIC_DATA_INVALID";
        this.recordType = recordType;
        this.recordId = recordId != null ? String.valueOf(recordId) : null;
        this.field = field;
    }
}

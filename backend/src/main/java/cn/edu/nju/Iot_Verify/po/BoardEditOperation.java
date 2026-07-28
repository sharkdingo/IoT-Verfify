package cn.edu.nju.Iot_Verify.po;

/** What the recorded edit did, which determines its inverse. */
public enum BoardEditOperation {
    /** Inverse: delete the record. */
    CREATE,
    /** Inverse: restore {@code beforeJson}. */
    UPDATE,
    /** Inverse: re-create the record from {@code beforeJson}. */
    DELETE
}

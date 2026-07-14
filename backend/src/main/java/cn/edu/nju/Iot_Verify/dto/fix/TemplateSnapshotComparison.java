package cn.edu.nju.Iot_Verify.dto.fix;

/** Whether current device templates still match the frozen verification snapshot used for a fix. */
public enum TemplateSnapshotComparison {
    NOT_CHECKED,
    UNCHANGED,
    CHANGED,
    UNAVAILABLE
}

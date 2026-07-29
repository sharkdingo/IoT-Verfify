package cn.edu.nju.Iot_Verify.po;

/**
 * Board record kinds that participate in undo.
 *
 * <p>Previously excluded devices because deletion cascaded into rules and specifications,
 * requiring a compound inverse. Now devices are reversible: deletion records the device itself
 * plus every rule and specification that was removed, so undo can atomically restore the entire
 * cascade as one operation.
 *
 * <p>Device entries snapshot the complete pool because device creation/deletion can add, remove,
 * or patch shared values atomically. Direct pool edits and automatic-fix rule rewrites use their
 * own complete collection snapshots.
 */
public enum BoardEditEntityType {
    DEVICE,
    ENVIRONMENT,
    RULE,
    SPECIFICATION,
    /**
     * Rule execution order, whose inverse is the previous ordering rather than a record snapshot.
     * Users reach it through explicit up/down buttons, so they read one press as one reversible
     * edit and expect the same undo they get for a deletion.
     */
    RULE_ORDER,
    /** An automatic fix is one user action even when it edits or removes several rules. */
    RULE_SET
}

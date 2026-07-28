package cn.edu.nju.Iot_Verify.po;

/**
 * Board record kinds that participate in undo.
 *
 * <p>Deliberately narrow. Devices are excluded because deleting one cascades into rules and
 * specifications that reference it, so its inverse is not a single-record restore; environment
 * variables are excluded because they are a shared pool whose value other readers depend on.
 * Both need their own design before they can be reversed safely.
 */
public enum BoardEditEntityType {
    RULE,
    SPECIFICATION,
    /**
     * Rule execution order, whose inverse is the previous ordering rather than a record snapshot.
     * Users reach it through explicit up/down buttons, so they read one press as one reversible
     * edit and expect the same undo they get for a deletion.
     */
    RULE_ORDER
}

package cn.edu.nju.Iot_Verify.service.board;

import java.util.List;

/**
 * A rule execution ordering, as stored in the edit journal.
 *
 * <p>Reorder is the one reversible board edit whose inverse is not a record snapshot: nothing about
 * any individual rule changes, only their relative order. Storing the id list keeps the entry small
 * and makes the conflict check exact — if the current ordering is no longer the one this edit
 * produced, some other change intervened and the reorder can no longer be reversed safely.
 *
 * @param ruleIds rule ids in execution order
 */
public record RuleOrderSnapshot(List<Long> ruleIds) {

    /** Jackson needs a no-arg path for deserialization of the empty case. */
    public RuleOrderSnapshot {
        ruleIds = ruleIds == null ? List.of() : List.copyOf(ruleIds);
    }
}

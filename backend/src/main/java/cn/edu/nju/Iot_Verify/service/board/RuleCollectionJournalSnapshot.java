package cn.edu.nju.Iot_Verify.service.board;

import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;

import java.util.List;

/** Complete ordered rule collection on one side of an automatic-fix edit. */
public record RuleCollectionJournalSnapshot(List<RuleDto> rules) {

    public RuleCollectionJournalSnapshot {
        rules = rules == null ? List.of() : List.copyOf(rules);
    }
}

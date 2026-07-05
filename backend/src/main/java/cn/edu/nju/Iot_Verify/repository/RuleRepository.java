package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.RulePo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.List;

public interface RuleRepository extends JpaRepository<RulePo, Long> {
    List<RulePo> findByUserId(Long userId);

    // Stable, deterministic order for rule reads. The fix apply drift check aligns board rules against
    // the trace snapshot positionally (ruleIndex is an ordinal), so an unstable JPA iteration order could
    // make it compare the wrong rules or edit the wrong one. Use this for any read that feeds indexing.
    List<RulePo> findByUserIdOrderByIdAsc(Long userId);

    void deleteByUserId(Long userId);
}

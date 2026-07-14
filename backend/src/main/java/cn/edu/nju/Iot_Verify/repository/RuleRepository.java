package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.RulePo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.List;

public interface RuleRepository extends JpaRepository<RulePo, Long> {
    List<RulePo> findByUserId(Long userId);

    // Explicit execution order is part of the model. ID is only a deterministic tie-breaker for
    // pre-migration rows whose execution_order is still null or duplicated.
    List<RulePo> findByUserIdOrderByExecutionOrderAscIdAsc(Long userId);

    void deleteByUserId(Long userId);
}

package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.RulePo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.List;

public interface RuleRepository extends JpaRepository<RulePo, Long> {
    List<RulePo> findByUserId(Long userId);
    void deleteByUserId(Long userId);
}

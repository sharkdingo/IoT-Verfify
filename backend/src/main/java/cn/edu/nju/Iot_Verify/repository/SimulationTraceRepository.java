package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.stereotype.Repository;

import java.util.List;
import java.util.Optional;

@Repository
public interface SimulationTraceRepository extends JpaRepository<SimulationTracePo, Long> {

    /**
     * 根据用户ID查询所有模拟轨迹
     */
    List<SimulationTracePo> findByUserIdOrderByCreatedAtDesc(Long userId);

    /**
     * 根据ID和用户ID查询模拟轨迹
     */
    Optional<SimulationTracePo> findByIdAndUserId(Long id, Long userId);
}

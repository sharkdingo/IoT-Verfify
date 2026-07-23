package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.repository.projection.SimulationTraceSummaryProjection;
import org.springframework.data.domain.Pageable;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;
import org.springframework.stereotype.Repository;

import java.util.List;
import java.util.Optional;

@Repository
public interface SimulationTraceRepository extends JpaRepository<SimulationTracePo, Long> {

    List<SimulationTraceSummaryProjection> findByUserIdOrderByCreatedAtDescIdDesc(
            Long userId, Pageable pageable);

    @Query("SELECT COUNT(trace) FROM SimulationTracePo trace "
            + "WHERE trace.userId = :userId AND NOT EXISTS ("
            + "SELECT task.id FROM SimulationTaskPo task "
            + "WHERE task.userId = :userId AND task.simulationTraceId = trace.id)")
    long countStandaloneByUserId(@Param("userId") Long userId);

    /**
     * 根据ID和用户ID查询模拟轨迹
     */
    Optional<SimulationTracePo> findByIdAndUserId(Long id, Long userId);

    void deleteByUserId(Long userId);
}

package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.stereotype.Repository;

import java.util.List;
import java.util.Optional;

@Repository
public interface SimulationTaskRepository extends JpaRepository<SimulationTaskPo, Long> {

    Optional<SimulationTaskPo> findByIdAndUserId(Long id, Long userId);

    List<SimulationTaskPo> findByStatusIn(List<SimulationTaskPo.TaskStatus> statuses);
}


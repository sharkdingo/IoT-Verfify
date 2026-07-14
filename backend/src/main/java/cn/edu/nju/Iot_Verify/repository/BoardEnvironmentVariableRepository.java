package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.BoardEnvironmentVariableId;
import cn.edu.nju.Iot_Verify.po.BoardEnvironmentVariablePo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.List;

public interface BoardEnvironmentVariableRepository extends JpaRepository<BoardEnvironmentVariablePo, BoardEnvironmentVariableId> {
    List<BoardEnvironmentVariablePo> findByUserIdOrderByNameAsc(Long userId);
    void deleteByUserId(Long userId);
}

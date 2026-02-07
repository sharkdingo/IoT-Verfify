package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.stereotype.Repository;

import java.util.List;
import java.util.Optional;

/**
 * 验证任务仓储接口
 */
@Repository
public interface VerificationTaskRepository extends JpaRepository<VerificationTaskPo, Long> {

    /**
     * 根据用户ID查询所有任务（按创建时间降序）
     */
    List<VerificationTaskPo> findByUserIdOrderByCreatedAtDesc(Long userId);

    /**
     * 根据ID和用户ID查询任务
     */
    Optional<VerificationTaskPo> findByIdAndUserId(Long id, Long userId);

    /**
     * 根据用户ID和状态查询任务
     */
    List<VerificationTaskPo> findByUserIdAndStatus(Long userId, VerificationTaskPo.TaskStatus status);

    /**
     * 删除用户的所有任务
     */
    void deleteByUserId(Long userId);
}

package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.TracePo;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.stereotype.Repository;

import java.util.List;
import java.util.Optional;

@Repository
public interface TraceRepository extends JpaRepository<TracePo, Long> {
    
    /**
     * 根据用户ID查询所有轨迹
     */
    List<TracePo> findByUserIdOrderByCreatedAtDesc(Long userId);
    
    /**
     * 根据ID和用户ID查询轨迹
     */
    Optional<TracePo> findByIdAndUserId(Long id, Long userId);
    
    /**
     * 根据用户ID和验证任务ID查询所有轨迹
     */
    List<TracePo> findByUserIdAndVerificationTaskId(Long userId, Long verificationTaskId);
    
    /**
     * 删除用户的所有轨迹
     */
    void deleteByUserId(Long userId);
}

package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.List;
import java.util.Optional;

public interface DeviceNodeRepository extends JpaRepository<DeviceNodePo, String> {
    List<DeviceNodePo> findByUserId(Long userId);
    List<DeviceNodePo> findByUserIdAndLabelContaining(Long userId, String label);
    List<DeviceNodePo> findByUserIdAndTemplateNameContainingIgnoreCaseOrUserIdAndLabelContainingIgnoreCase(
            Long userId1, String templateKeyword, Long userId2, String labelKeyword);
    Optional<DeviceNodePo> findByUserIdAndLabel(Long userId, String label);
    void deleteByUserId(Long userId);
}

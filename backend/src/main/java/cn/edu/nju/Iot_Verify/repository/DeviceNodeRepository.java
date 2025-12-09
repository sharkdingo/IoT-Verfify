// src/main/java/cn/edu/nju/Iot_Verify/repository/DeviceNodeRepository.java
package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.List;
import java.util.Optional;

public interface DeviceNodeRepository extends JpaRepository<DeviceNodePo, String> {
    List<DeviceNodePo> findByLabelContaining(String label);

    List<DeviceNodePo> findByTemplateNameContainingIgnoreCaseOrLabelContainingIgnoreCase(String templateKeyword, String labelKeyword);

    Optional<DeviceNodePo> findByLabel(String label);
}

// src/main/java/cn/edu/nju/Iot_Verify/repository/DeviceNodeRepository.java
package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import org.springframework.data.jpa.repository.JpaRepository;

public interface DeviceNodeRepository extends JpaRepository<DeviceNodePo, String> {
}

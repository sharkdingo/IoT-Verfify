// src/main/java/cn/edu/nju/Iot_Verify/repository/DeviceEdgeRepository.java
package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.DeviceEdgePo;
import org.springframework.data.jpa.repository.JpaRepository;

public interface DeviceEdgeRepository extends JpaRepository<DeviceEdgePo, String> {}
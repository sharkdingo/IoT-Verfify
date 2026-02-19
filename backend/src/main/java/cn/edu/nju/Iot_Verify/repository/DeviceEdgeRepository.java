package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.DeviceEdgeId;
import cn.edu.nju.Iot_Verify.po.DeviceEdgePo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.List;

public interface DeviceEdgeRepository extends JpaRepository<DeviceEdgePo, DeviceEdgeId> {
    List<DeviceEdgePo> findByUserId(Long userId);
    void deleteByUserId(Long userId);
}

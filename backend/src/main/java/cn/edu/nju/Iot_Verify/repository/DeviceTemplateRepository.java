// src/main/java/cn/edu/nju/Iot_Verify/repository/DeviceTemplateRepository.java
package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.stereotype.Repository;

@Repository
public interface DeviceTemplateRepository extends JpaRepository<DeviceTemplatePo, Long> {

    // 检查名称是否存在，用于创建时的查重
    boolean existsByName(String name);
}
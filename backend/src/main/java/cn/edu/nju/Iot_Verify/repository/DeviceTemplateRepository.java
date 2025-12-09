// src/main/java/cn/edu/nju/Iot_Verify/repository/DeviceTemplateRepository.java
package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Query;
import org.springframework.stereotype.Repository;

import java.util.List;
import java.util.Optional;

@Repository
public interface DeviceTemplateRepository extends JpaRepository<DeviceTemplatePo, Long> {

    // 检查名称是否存在，用于创建时的查重
    boolean existsByName(String name);

    // 获取所有模板名称（用于业务层的模糊匹配算法）
    @Query("SELECT t.name FROM DeviceTemplatePo t")
    List<String> findAllNames();

    Optional<DeviceTemplatePo> findByName(String templateName);
}
// src/main/java/cn/edu/nju/Iot_Verify/repository/SpecificationRepository.java
package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.SpecificationPo;
import org.springframework.data.jpa.repository.JpaRepository;

public interface SpecificationRepository extends JpaRepository<SpecificationPo, String> {}
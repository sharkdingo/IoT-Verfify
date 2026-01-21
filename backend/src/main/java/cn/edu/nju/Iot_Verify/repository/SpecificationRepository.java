package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.SpecificationPo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.List;

public interface SpecificationRepository extends JpaRepository<SpecificationPo, String> {
    List<SpecificationPo> findByUserId(Long userId);
    void deleteByUserId(Long userId);
}

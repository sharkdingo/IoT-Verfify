package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.SpecificationPo;
import cn.edu.nju.Iot_Verify.po.SpecificationId;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;

import java.util.List;

public interface SpecificationRepository extends JpaRepository<SpecificationPo, SpecificationId> {
    @Query("SELECT specification FROM SpecificationPo specification "
            + "WHERE specification.userId = :userId "
            + "ORDER BY specification.listOrder ASC, specification.id ASC")
    List<SpecificationPo> findByUserId(@Param("userId") Long userId);
    void deleteByUserId(Long userId);
}

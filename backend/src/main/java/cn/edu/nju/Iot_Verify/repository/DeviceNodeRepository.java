package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;

import java.util.List;
import java.util.Optional;

public interface DeviceNodeRepository extends JpaRepository<DeviceNodePo, String> {
    List<DeviceNodePo> findByUserId(Long userId);
    List<DeviceNodePo> findByUserIdAndLabelContaining(Long userId, String label);

    @Query("""
            select n from DeviceNodePo n
            where n.userId = :userId
              and (
                   lower(n.templateName) like lower(concat('%', :keyword, '%'))
                   or lower(n.label) like lower(concat('%', :keyword, '%'))
              )
            """)
    List<DeviceNodePo> searchByUserIdAndTemplateOrLabel(@Param("userId") Long userId,
                                                         @Param("keyword") String keyword);

    Optional<DeviceNodePo> findByUserIdAndLabel(Long userId, String label);
    void deleteByUserId(Long userId);
}

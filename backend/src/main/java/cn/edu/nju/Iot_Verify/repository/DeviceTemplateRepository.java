package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;
import org.springframework.stereotype.Repository;

import java.util.List;
import java.util.Optional;

@Repository
public interface DeviceTemplateRepository extends JpaRepository<DeviceTemplatePo, Long> {
    List<DeviceTemplatePo> findByUserId(Long userId);
    @Query("SELECT COUNT(t) > 0 FROM DeviceTemplatePo t WHERE t.userId = :userId AND LOWER(t.name) = LOWER(:name)")
    boolean existsByUserIdAndNameIgnoreCase(@Param("userId") Long userId, @Param("name") String name);

    @Query("SELECT t.name FROM DeviceTemplatePo t WHERE t.userId = :userId")
    List<String> findAllNamesByUserId(Long userId);

    @Query("SELECT t.manifestJson FROM DeviceTemplatePo t WHERE t.userId = :userId")
    List<String> findAllManifestJsonsByUserId(Long userId);

    Optional<DeviceTemplatePo> findByUserIdAndName(Long userId, String templateName);
}

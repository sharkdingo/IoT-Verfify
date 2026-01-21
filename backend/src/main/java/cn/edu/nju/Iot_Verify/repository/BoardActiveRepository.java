package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.BoardActivePo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.Optional;

public interface BoardActiveRepository extends JpaRepository<BoardActivePo, Long> {
    Optional<BoardActivePo> findByUserId(Long userId);
}

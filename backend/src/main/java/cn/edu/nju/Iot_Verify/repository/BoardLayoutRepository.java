package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.BoardLayoutPo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.Optional;

public interface BoardLayoutRepository extends JpaRepository<BoardLayoutPo, Long> {
    Optional<BoardLayoutPo> findByUserId(Long userId);
}

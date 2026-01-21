package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.UserPo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.Optional;

public interface UserRepository extends JpaRepository<UserPo, Long> {
    Optional<UserPo> findByPhone(String phone);
    Optional<UserPo> findByUsername(String username);
    boolean existsByPhone(String phone);
    boolean existsByUsername(String username);
}

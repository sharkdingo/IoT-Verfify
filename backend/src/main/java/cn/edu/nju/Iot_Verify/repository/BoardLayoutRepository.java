// src/main/java/cn/edu/nju/Iot_Verify/repository/BoardLayoutRepository.java
package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.BoardLayoutPo;
import org.springframework.data.jpa.repository.JpaRepository;

public interface BoardLayoutRepository extends JpaRepository<BoardLayoutPo, Byte> {}
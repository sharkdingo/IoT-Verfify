// src/main/java/cn/edu/nju/Iot_Verify/repository/BoardActiveRepository.java
package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.BoardActivePo;
import org.springframework.data.jpa.repository.JpaRepository;

public interface BoardActiveRepository extends JpaRepository<BoardActivePo, Byte> {}

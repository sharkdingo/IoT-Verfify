package cn.edu.nju.Iot_Verify.repository;

import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.NoRepositoryBean;

import java.time.LocalDateTime;

/** Shared microsecond-precision database clock for persisted lifecycle timestamps. */
@NoRepositoryBean
public interface DatabaseClockRepository {

    @Query(value = "SELECT CURRENT_TIMESTAMP(6)", nativeQuery = true)
    LocalDateTime currentDatabaseTime();
}

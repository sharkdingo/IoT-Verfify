package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.FuzzFindingPo;
import cn.edu.nju.Iot_Verify.repository.projection.FuzzFindingSummaryProjection;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;
import org.springframework.stereotype.Repository;
import org.springframework.transaction.annotation.Transactional;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

@Repository
public interface FuzzFindingRepository extends JpaRepository<FuzzFindingPo, Long> {

    List<FuzzFindingPo> findByUserIdAndFuzzTaskIdOrderByCreatedAtAscIdAsc(
            Long userId, Long fuzzTaskId);

    List<FuzzFindingPo> findByUserIdAndFuzzTaskIdInOrderByCreatedAtAscIdAsc(
            Long userId, Collection<Long> fuzzTaskIds);

    @Query("SELECT f.id AS id, f.userId AS userId, f.fuzzTaskId AS fuzzTaskId, "
         + "f.violatedSpecId AS violatedSpecId, "
         + "f.firstViolationStep AS firstViolationStep, f.seed AS seed, "
         + "f.stateCount AS stateCount, f.createdAt AS createdAt "
         + "FROM FuzzFindingPo f WHERE f.userId = :userId AND f.fuzzTaskId IN :fuzzTaskIds "
         + "ORDER BY f.createdAt ASC, f.id ASC")
    List<FuzzFindingSummaryProjection> findSummariesByUserIdAndFuzzTaskIdIn(
            @Param("userId") Long userId,
            @Param("fuzzTaskIds") Collection<Long> fuzzTaskIds);

    Optional<FuzzFindingPo> findByIdAndUserId(Long id, Long userId);

    @Transactional
    @Modifying(clearAutomatically = true, flushAutomatically = true)
    @Query("DELETE FROM FuzzFindingPo f WHERE f.userId = :userId AND f.fuzzTaskId = :fuzzTaskId")
    int deleteByUserIdAndFuzzTaskId(@Param("userId") Long userId,
                                    @Param("fuzzTaskId") Long fuzzTaskId);

    @Transactional
    @Modifying(clearAutomatically = true, flushAutomatically = true)
    @Query("DELETE FROM FuzzFindingPo f WHERE f.userId = :userId")
    int deleteByUserId(@Param("userId") Long userId);
}

package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.RulePo;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;

import java.time.LocalDateTime;
import java.util.List;

public interface RuleRepository extends JpaRepository<RulePo, Long> {
    List<RulePo> findByUserId(Long userId);

    /**
     * Re-inserts a deleted rule under its original id.
     *
     * <p>Has to be a native insert: the id is {@code GenerationType.IDENTITY}, so neither
     * {@code save()} (which picks UPDATE for a preset id) nor {@code persist()} (which rejects it
     * as detached) can write an explicit one. Restoring the original id matters because rules and
     * specifications reference it, so a new id would silently break them.
     *
     * <p>The JSON columns are written as plain strings, which MySQL parses into JSON. H2 quotes
     * them instead, so the H2-backed slice tests assert this path through MySQL-compatible mode.
     */
    // flushAutomatically: renumberSurvivingRules queues managed-entity UPDATEs via save() before this
    // runs, and Hibernate does not auto-flush the persistence context for a native query — without the
    // flush the raw INSERT could reach the DB before the renumbering it must follow.
    // clearAutomatically: the restored row exists only in the DB, so a stale first-level cache would
    // otherwise serve the in-transaction reads in journalResult.
    @Modifying(flushAutomatically = true, clearAutomatically = true)
    @Query(value = """
            insert into rules
                (id, user_id, conditions_json, command_json, rule_string, execution_order, created_at)
            values
                (:id, :userId, :conditionsJson, :commandJson, :ruleString, :executionOrder,
                 :createdAt)
            """, nativeQuery = true)
    int insertWithId(@Param("id") Long id,
                     @Param("userId") Long userId,
                     @Param("conditionsJson") String conditionsJson,
                     @Param("commandJson") String commandJson,
                     @Param("ruleString") String ruleString,
                     @Param("executionOrder") Integer executionOrder,
                     @Param("createdAt") LocalDateTime createdAt);

    // Explicit execution order is part of the model. ID is only a deterministic tie-breaker for
    // pre-migration rows whose execution_order is still null or duplicated.
    List<RulePo> findByUserIdOrderByExecutionOrderAscIdAsc(Long userId);

    void deleteByUserId(Long userId);
}

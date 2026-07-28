package cn.edu.nju.Iot_Verify.configure;

import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.SmartInitializingSingleton;
import org.springframework.stereotype.Component;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

/**
 * Makes {@code (user_id, sequence)} unique on the board edit journal.
 *
 * <p>Sequence allocation is read-max-then-add-one, guarded only by an in-JVM per-user lock. That is
 * not a cross-instance guarantee: two application instances (or two threads racing a lock rebuild)
 * can read the same maximum and write the same sequence for one account. The journal is ordered by
 * that column, so a duplicate makes "the newest edit still in effect" ambiguous — undo would pick one
 * of the two arbitrarily and the other becomes unreachable, silently losing a reversible edit.
 *
 * <p>The constraint converts that silent corruption into a duplicate-key failure the caller can
 * retry, which is the same fencing strategy the rest of the schema uses (see
 * {@code UsernameCollationMigration}, {@code UserOwnedOrphanCleanup}).
 *
 * <p><b>Rollout.</b> Idempotent and safe to run repeatedly: it inspects
 * {@code information_schema.STATISTICS} first and returns immediately when the index already exists.
 * It is a no-op on a non-MySQL database, so the H2-backed slice tests are unaffected. Because a live
 * table may already hold duplicates written before the constraint existed, those are renumbered first
 * — the alternative, failing startup, would leave the application unable to boot against real data.
 *
 * <p><b>Rollback.</b> {@code DROP INDEX uk_board_edit_journal_user_sequence ON board_edit_journal;}
 * The renumbering is not reversible, but it only ever rewrites rows that were already ambiguous, and
 * it preserves each account's relative ordering.
 */
@Slf4j
@Component
public class BoardEditJournalSequenceUniqueness implements SmartInitializingSingleton {

    static final String INDEX_NAME = "uk_board_edit_journal_user_sequence";

    private static final String INDEX_QUERY = "SELECT COUNT(*) FROM information_schema.STATISTICS "
            + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = 'board_edit_journal' "
            + "AND INDEX_NAME = '" + INDEX_NAME + "'";
    private static final String TABLE_QUERY = "SELECT COUNT(*) FROM information_schema.TABLES "
            + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = 'board_edit_journal'";
    private static final String DUPLICATE_QUERY =
            "SELECT user_id FROM board_edit_journal GROUP BY user_id, sequence HAVING COUNT(*) > 1";
    private static final String CREATE_INDEX_SQL = "ALTER TABLE `board_edit_journal` "
            + "ADD CONSTRAINT `" + INDEX_NAME + "` UNIQUE (`user_id`, `sequence`)";

    private final DataSource dataSource;

    public BoardEditJournalSequenceUniqueness(DataSource dataSource) {
        this.dataSource = dataSource;
    }

    @Override
    public void afterSingletonsInstantiated() {
        migrate();
    }

    boolean migrate() {
        try (Connection connection = dataSource.getConnection()) {
            if (!"MySQL".equalsIgnoreCase(connection.getMetaData().getDatabaseProductName())) {
                return false;
            }
            if (count(connection, TABLE_QUERY) == 0) {
                // Schema not created yet (ddl-auto runs later, or this is a fresh database).
                return false;
            }
            if (count(connection, INDEX_QUERY) > 0) {
                return false;
            }
            renumberDuplicates(connection);
            log.warn("Adding unique constraint {} to board_edit_journal(user_id, sequence)", INDEX_NAME);
            try (Statement statement = connection.createStatement()) {
                statement.executeUpdate(CREATE_INDEX_SQL);
            } catch (SQLException creationFailure) {
                if (count(connection, INDEX_QUERY) > 0) {
                    log.info("Journal sequence uniqueness was added by another application instance");
                    return true;
                }
                throw new IllegalStateException(
                        "Could not add unique constraint on board_edit_journal(user_id, sequence)",
                        creationFailure);
            }
            if (count(connection, INDEX_QUERY) == 0) {
                throw new IllegalStateException(
                        "Journal sequence uniqueness migration completed without creating " + INDEX_NAME);
            }
            log.info("Journal sequence uniqueness migration completed");
            return true;
        } catch (SQLException e) {
            throw new IllegalStateException("Could not inspect board_edit_journal for sequence uniqueness", e);
        }
    }

    /**
     * Renumbers every account that holds a duplicated sequence, oldest-first by {@code (sequence, id)}.
     *
     * <p>Only ambiguous accounts are touched. Ordering by id after sequence keeps the two colliding
     * rows in insertion order, which is the closest thing to the intent that was lost.
     */
    private void renumberDuplicates(Connection connection) throws SQLException {
        java.util.List<Long> affected = new java.util.ArrayList<>();
        try (PreparedStatement statement = connection.prepareStatement(DUPLICATE_QUERY);
             ResultSet resultSet = statement.executeQuery()) {
            while (resultSet.next()) {
                Long userId = resultSet.getLong(1);
                if (!affected.contains(userId)) affected.add(userId);
            }
        }
        if (affected.isEmpty()) return;

        log.warn("Renumbering board edit journal sequences for {} account(s) with duplicates: {}",
                affected.size(), affected);
        for (Long userId : affected) {
            java.util.List<Long> ids = new java.util.ArrayList<>();
            try (PreparedStatement select = connection.prepareStatement(
                    "SELECT id FROM board_edit_journal WHERE user_id = ? ORDER BY sequence ASC, id ASC")) {
                select.setLong(1, userId);
                try (ResultSet resultSet = select.executeQuery()) {
                    while (resultSet.next()) ids.add(resultSet.getLong(1));
                }
            }
            // Two passes through a disjoint range: assigning 1..n directly would collide with a row
            // that still holds one of those values. The staging range starts above this account's
            // current maximum rather than at a fixed constant — row count is capped, but the sequence
            // value itself grows for the life of the account, so a literal offset is an assumption
            // that silently expires.
            long offset = maxSequenceFor(connection, userId) + 1;
            try (PreparedStatement update = connection.prepareStatement(
                    "UPDATE board_edit_journal SET sequence = ? WHERE id = ?")) {
                for (int index = 0; index < ids.size(); index++) {
                    update.setLong(1, offset + index);
                    update.setLong(2, ids.get(index));
                    update.addBatch();
                }
                update.executeBatch();
                for (int index = 0; index < ids.size(); index++) {
                    update.setLong(1, index + 1L);
                    update.setLong(2, ids.get(index));
                    update.addBatch();
                }
                update.executeBatch();
            }
        }
    }

    /** Highest sequence currently held by this account, or 0 when it has none. */
    private long maxSequenceFor(Connection connection, Long userId) throws SQLException {
        try (PreparedStatement statement = connection.prepareStatement(
                "SELECT COALESCE(MAX(sequence), 0) FROM board_edit_journal WHERE user_id = ?")) {
            statement.setLong(1, userId);
            try (ResultSet resultSet = statement.executeQuery()) {
                return resultSet.next() ? resultSet.getLong(1) : 0L;
            }
        }
    }

    private long count(Connection connection, String sql) throws SQLException {        try (PreparedStatement statement = connection.prepareStatement(sql);
             ResultSet resultSet = statement.executeQuery()) {
            return resultSet.next() ? resultSet.getLong(1) : 0L;
        }
    }
}

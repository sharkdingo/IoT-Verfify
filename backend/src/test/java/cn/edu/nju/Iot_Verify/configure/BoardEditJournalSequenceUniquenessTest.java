package cn.edu.nju.Iot_Verify.configure;

import cn.edu.nju.Iot_Verify.service.board.MySqlAvailableCondition;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.springframework.jdbc.datasource.DriverManagerDataSource;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The journal sequence-uniqueness migration, against a real MySQL.
 *
 * <p>MySQL-only by nature: the migration inspects {@code information_schema.STATISTICS} and adds a
 * table constraint, and the failure it prevents is a duplicate-key race. Skipped when no MySQL is
 * reachable so the H2-only CI job stays green.
 */
@ExtendWith(MySqlAvailableCondition.class)
class BoardEditJournalSequenceUniquenessTest {

    private DataSource dataSource;

    @BeforeEach
    void setUp() throws Exception {
        DriverManagerDataSource source = new DriverManagerDataSource();
        source.setDriverClassName("com.mysql.cj.jdbc.Driver");
        source.setUrl(MySqlAvailableCondition.URL);
        source.setUsername(MySqlAvailableCondition.USERNAME);
        source.setPassword(MySqlAvailableCondition.PASSWORD);
        dataSource = source;

        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            statement.executeUpdate("DROP TABLE IF EXISTS board_edit_journal");
            statement.executeUpdate("""
                    CREATE TABLE board_edit_journal (
                        id BIGINT AUTO_INCREMENT PRIMARY KEY,
                        user_id BIGINT NOT NULL,
                        sequence BIGINT NOT NULL,
                        undone BIT(1) NOT NULL DEFAULT 0
                    )""");
        }
    }

    @Test
    void addsTheConstraintAndIsIdempotent() throws Exception {
        BoardEditJournalSequenceUniqueness migration = new BoardEditJournalSequenceUniqueness(dataSource);

        assertTrue(migration.migrate(), "first run must create the constraint");
        // Two rows, not one: information_schema.STATISTICS lists one row per indexed column, and this
        // index spans (user_id, sequence).
        assertEquals(2, indexCount(), "the composite unique index must exist");
        // Running again on an already-migrated schema must change nothing.
        assertTrue(!migration.migrate(), "second run must be a no-op");
        assertEquals(2, indexCount());
    }

    @Test
    void renumbersPreExistingDuplicatesInsteadOfFailingStartup() throws Exception {
        // A live table can already hold duplicates written before the constraint existed. Failing here
        // would leave the application unable to boot against real data.
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            statement.executeUpdate("INSERT INTO board_edit_journal (user_id, sequence) VALUES (1, 1)");
            statement.executeUpdate("INSERT INTO board_edit_journal (user_id, sequence) VALUES (1, 1)");
            statement.executeUpdate("INSERT INTO board_edit_journal (user_id, sequence) VALUES (1, 2)");
            // A second account is untouched: only ambiguous accounts are renumbered.
            statement.executeUpdate("INSERT INTO board_edit_journal (user_id, sequence) VALUES (2, 7)");
        }

        assertTrue(new BoardEditJournalSequenceUniqueness(dataSource).migrate());

        assertEquals("1,2,3", sequencesFor(1L), "duplicates renumbered contiguously, order preserved");
        assertEquals("7", sequencesFor(2L), "an account without duplicates keeps its sequences");
    }

    @Test
    void theConstraintRejectsADuplicateSequence() throws Exception {
        new BoardEditJournalSequenceUniqueness(dataSource).migrate();

        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            statement.executeUpdate("INSERT INTO board_edit_journal (user_id, sequence) VALUES (1, 1)");
            // The whole point: a lost read-max-then-add-one race must fail loudly, not produce two
            // entries sharing an ordinal where "the newest edit still in effect" becomes ambiguous.
            assertThrows(SQLException.class, () -> statement.executeUpdate(
                    "INSERT INTO board_edit_journal (user_id, sequence) VALUES (1, 1)"));
            // The same sequence for a different account is legitimate.
            statement.executeUpdate("INSERT INTO board_edit_journal (user_id, sequence) VALUES (2, 1)");
        }
    }

    private long indexCount() throws Exception {
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement();
             ResultSet resultSet = statement.executeQuery(
                     "SELECT COUNT(*) FROM information_schema.STATISTICS WHERE TABLE_SCHEMA = DATABASE()"
                             + " AND TABLE_NAME = 'board_edit_journal' AND INDEX_NAME = '"
                             + BoardEditJournalSequenceUniqueness.INDEX_NAME + "'")) {
            return resultSet.next() ? resultSet.getLong(1) : 0L;
        }
    }

    private String sequencesFor(long userId) throws Exception {
        StringBuilder sequences = new StringBuilder();
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement();
             ResultSet resultSet = statement.executeQuery(
                     "SELECT sequence FROM board_edit_journal WHERE user_id = " + userId
                             + " ORDER BY id ASC")) {
            while (resultSet.next()) {
                if (!sequences.isEmpty()) sequences.append(',');
                sequences.append(resultSet.getLong(1));
            }
        }
        return sequences.toString();
    }
}

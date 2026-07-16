package cn.edu.nju.Iot_Verify.configure;

import org.junit.jupiter.api.Test;
import org.springframework.jdbc.datasource.DriverManagerDataSource;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

class UserOwnedOrphanCleanupTest {

    private static final List<String> GENERIC_USER_TABLES = List.of(
            "trace",
            "verification_task",
            "simulation_task",
            "simulation_trace",
            "device_node",
            "board_environment_variable",
            "rules",
            "specification",
            "board_layout",
            "device_templates");

    @Test
    void migrate_repairsLegacyRowsAndEnforcesCascadeOwnership() throws Exception {
        DataSource dataSource = dataSource();
        createSchemaAndRows(dataSource);
        UserOwnedOrphanCleanup migration = new UserOwnedOrphanCleanup(dataSource);

        assertEquals(16, migration.migrate());
        assertEquals(0, migration.migrate());

        assertEquals(1, count(dataSource, "chat_message"));
        assertEquals(1, count(dataSource, "chat_session"));
        assertEquals(1, count(dataSource, "fuzz_finding"));
        assertEquals(1, count(dataSource, "fuzz_task"));
        for (String table : GENERIC_USER_TABLES) {
            assertEquals(1, count(dataSource, table), table);
        }
        assertCascadeForeignKeys(dataSource);

        insertSecondUserGraph(dataSource);
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            statement.executeUpdate("DELETE FROM app_user WHERE id = 2");
        }

        assertEquals(1, count(dataSource, "chat_message"));
        assertEquals(1, count(dataSource, "chat_session"));
        assertEquals(1, count(dataSource, "fuzz_finding"));
        assertEquals(1, count(dataSource, "fuzz_task"));
        for (String table : GENERIC_USER_TABLES) {
            assertEquals(1, count(dataSource, table), table);
        }

        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            assertThrows(SQLException.class,
                    () -> statement.executeUpdate("INSERT INTO rules (id, user_id) VALUES (99, 99)"));
            assertThrows(SQLException.class,
                    () -> statement.executeUpdate(
                            "INSERT INTO chat_message (id, session_id) VALUES (99, 'missing')"));
            assertThrows(SQLException.class,
                    () -> statement.executeUpdate(
                            "INSERT INTO fuzz_finding (id, user_id, fuzz_task_id) VALUES (99, 1, 999)"));
            statement.executeUpdate("INSERT INTO app_user (id) VALUES (3)");
            statement.executeUpdate("INSERT INTO fuzz_task (id, user_id) VALUES (30, 3)");
            assertThrows(SQLException.class,
                    () -> statement.executeUpdate(
                            "INSERT INTO fuzz_finding (id, user_id, fuzz_task_id) VALUES (100, 1, 30)"));
        }
    }

    private void createSchemaAndRows(DataSource dataSource) throws Exception {
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            statement.executeUpdate("CREATE TABLE app_user (id BIGINT PRIMARY KEY)");
            statement.executeUpdate("CREATE TABLE chat_session (id VARCHAR(100) PRIMARY KEY, user_id BIGINT NOT NULL)");
            statement.executeUpdate("CREATE TABLE chat_message (id BIGINT PRIMARY KEY, session_id VARCHAR(100) NOT NULL)");
            statement.executeUpdate("CREATE TABLE fuzz_task (id BIGINT PRIMARY KEY, user_id BIGINT NOT NULL)");
            statement.executeUpdate("CREATE TABLE fuzz_finding ("
                    + "id BIGINT PRIMARY KEY, user_id BIGINT NOT NULL, fuzz_task_id BIGINT NOT NULL)");
            for (String table : GENERIC_USER_TABLES) {
                statement.executeUpdate("CREATE TABLE `" + table + "` (id BIGINT PRIMARY KEY, user_id BIGINT NOT NULL)");
            }

            statement.executeUpdate("INSERT INTO app_user (id) VALUES (1)");
            statement.executeUpdate("INSERT INTO chat_session (id, user_id) VALUES ('valid', 1), ('orphan', 99)");
            statement.executeUpdate("INSERT INTO chat_message (id, session_id) VALUES "
                    + "(1, 'valid'), (2, 'orphan'), (3, 'missing')");
            statement.executeUpdate("INSERT INTO fuzz_task (id, user_id) VALUES (1, 1), (2, 99)");
            statement.executeUpdate("INSERT INTO fuzz_finding (id, user_id, fuzz_task_id) VALUES "
                    + "(1, 1, 1), (2, 99, 2), (3, 1, 999)");
            for (String table : GENERIC_USER_TABLES) {
                statement.executeUpdate("INSERT INTO `" + table + "` (id, user_id) VALUES (1, 1), (2, 99)");
            }
        }
    }

    private void insertSecondUserGraph(DataSource dataSource) throws Exception {
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            statement.executeUpdate("INSERT INTO app_user (id) VALUES (2)");
            statement.executeUpdate("INSERT INTO chat_session (id, user_id) VALUES ('cascade', 2)");
            statement.executeUpdate("INSERT INTO chat_message (id, session_id) VALUES (20, 'cascade')");
            statement.executeUpdate("INSERT INTO fuzz_task (id, user_id) VALUES (20, 2)");
            statement.executeUpdate("INSERT INTO fuzz_finding (id, user_id, fuzz_task_id) VALUES (20, 2, 20)");
            for (String table : GENERIC_USER_TABLES) {
                statement.executeUpdate("INSERT INTO `" + table + "` (id, user_id) VALUES (20, 2)");
            }
        }
    }

    private void assertCascadeForeignKeys(DataSource dataSource) throws Exception {
        assertCascadeForeignKey(dataSource, "chat_message", "fk_chat_message_session",
                List.of("session_id"), "chat_session", List.of("id"));
        assertCascadeForeignKey(dataSource, "fuzz_finding", "fk_fuzz_finding_task_owner",
                List.of("user_id", "fuzz_task_id"), "fuzz_task", List.of("user_id", "id"));
        assertCascadeForeignKey(dataSource, "chat_session", "fk_chat_session_user",
                List.of("user_id"), "app_user", List.of("id"));
        assertCascadeForeignKey(dataSource, "fuzz_finding", "fk_fuzz_finding_user",
                List.of("user_id"), "app_user", List.of("id"));
        assertCascadeForeignKey(dataSource, "fuzz_task", "fk_fuzz_task_user",
                List.of("user_id"), "app_user", List.of("id"));
        for (String table : GENERIC_USER_TABLES) {
            assertCascadeForeignKey(dataSource, table, null,
                    List.of("user_id"), "app_user", List.of("id"));
        }
        assertTrue(hasNamedIndex(dataSource, "fuzz_task", "uk_fuzz_task_user_id", true));
        assertTrue(hasNamedIndex(dataSource, "fuzz_finding", "idx_fuzz_finding_user_task", false));
    }

    private void assertCascadeForeignKey(
            DataSource dataSource,
            String table,
            String expectedName,
            List<String> childColumns,
            String parentTable,
            List<String> parentColumns) throws Exception {
        Map<String, List<ImportedColumn>> byName = new LinkedHashMap<>();
        try (Connection connection = dataSource.getConnection();
             ResultSet keys = connection.getMetaData().getImportedKeys(connection.getCatalog(), null, table)) {
            while (keys.next()) {
                String name = keys.getString("FK_NAME");
                byName.computeIfAbsent(name, ignored -> new ArrayList<>()).add(new ImportedColumn(
                        keys.getShort("KEY_SEQ"),
                        keys.getString("FKCOLUMN_NAME"),
                        keys.getString("PKTABLE_NAME"),
                        keys.getString("PKCOLUMN_NAME"),
                        keys.getShort("DELETE_RULE")));
            }
        }
        for (Map.Entry<String, List<ImportedColumn>> entry : byName.entrySet()) {
            if (expectedName != null && !expectedName.equalsIgnoreCase(entry.getKey())) continue;
            List<ImportedColumn> columns = entry.getValue().stream()
                    .sorted(Comparator.comparingInt(ImportedColumn::sequence))
                    .toList();
            if (!sameColumns(childColumns, columns.stream().map(ImportedColumn::childColumn).toList())) continue;
            assertTrue(columns.stream().allMatch(column ->
                    parentTable.equalsIgnoreCase(column.parentTable())));
            assertTrue(sameColumns(parentColumns, columns.stream().map(ImportedColumn::parentColumn).toList()));
            assertTrue(columns.stream().allMatch(column ->
                    column.deleteRule() == DatabaseMetaData.importedKeyCascade));
            return;
        }
        throw new AssertionError("Missing cascade foreign key for " + table + childColumns);
    }

    private boolean hasNamedIndex(
            DataSource dataSource, String table, String expectedName, boolean unique) throws Exception {
        try (Connection connection = dataSource.getConnection();
             ResultSet indexes = connection.getMetaData().getIndexInfo(
                     connection.getCatalog(), null, table, false, false)) {
            while (indexes.next()) {
                if (expectedName.equalsIgnoreCase(indexes.getString("INDEX_NAME"))
                        && unique == !indexes.getBoolean("NON_UNIQUE")) return true;
            }
            return false;
        }
    }

    private boolean sameColumns(List<String> expected, List<String> actual) {
        if (expected.size() != actual.size()) return false;
        for (int i = 0; i < expected.size(); i++) {
            if (!expected.get(i).equalsIgnoreCase(actual.get(i))) return false;
        }
        return true;
    }

    private DataSource dataSource() {
        String name = "orphan_cleanup_" + UUID.randomUUID().toString().replace("-", "");
        return new DriverManagerDataSource(
                "jdbc:h2:mem:" + name + ";MODE=MySQL;DATABASE_TO_LOWER=TRUE;DB_CLOSE_DELAY=-1",
                "sa",
                "");
    }

    private int count(DataSource dataSource, String table) throws Exception {
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement();
             ResultSet resultSet = statement.executeQuery("SELECT COUNT(*) FROM `" + table + "`")) {
            resultSet.next();
            return resultSet.getInt(1);
        }
    }

    private record ImportedColumn(
            short sequence,
            String childColumn,
            String parentTable,
            String parentColumn,
            short deleteRule) {
    }
}

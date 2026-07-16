package cn.edu.nju.Iot_Verify.configure;

import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.SmartInitializingSingleton;
import org.springframework.dao.DataAccessException;
import org.springframework.jdbc.core.JdbcTemplate;
import org.springframework.jdbc.datasource.DataSourceTransactionManager;
import org.springframework.stereotype.Component;
import org.springframework.transaction.support.TransactionTemplate;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/** Repairs legacy orphans and enforces database ownership cascades. */
@Slf4j
@Component
public class UserOwnedOrphanCleanup implements SmartInitializingSingleton {

    private static final List<String> USER_OWNED_TABLES = List.of(
            "trace",
            "verification_task",
            "simulation_task",
            "simulation_trace",
            "fuzz_finding",
            "fuzz_task",
            "chat_session",
            "device_node",
            "board_environment_variable",
            "rules",
            "specification",
            "board_layout",
            "device_templates");

    private static final List<ForeignKeySpec> FOREIGN_KEYS = List.of(
            userForeignKey("trace", "fk_trace_user"),
            userForeignKey("verification_task", "fk_verification_task_user"),
            userForeignKey("simulation_task", "fk_simulation_task_user"),
            userForeignKey("simulation_trace", "fk_simulation_trace_user"),
            userForeignKey("fuzz_finding", "fk_fuzz_finding_user"),
            userForeignKey("fuzz_task", "fk_fuzz_task_user"),
            userForeignKey("chat_session", "fk_chat_session_user"),
            userForeignKey("device_node", "fk_device_node_user"),
            userForeignKey("board_environment_variable", "fk_board_environment_user"),
            userForeignKey("rules", "fk_rules_user"),
            userForeignKey("specification", "fk_specification_user"),
            userForeignKey("board_layout", "fk_board_layout_user"),
            userForeignKey("device_templates", "fk_device_templates_user"),
            new ForeignKeySpec(
                    "chat_message", List.of("session_id"),
                    "chat_session", List.of("id"), "fk_chat_message_session"),
            new ForeignKeySpec(
                    "fuzz_finding", List.of("user_id", "fuzz_task_id"),
                    "fuzz_task", List.of("user_id", "id"), "fk_fuzz_finding_task_owner"));

    private final DataSource dataSource;
    private final JdbcTemplate jdbcTemplate;
    private final TransactionTemplate transactionTemplate;

    public UserOwnedOrphanCleanup(DataSource dataSource) {
        this.dataSource = dataSource;
        this.jdbcTemplate = new JdbcTemplate(dataSource);
        this.transactionTemplate = new TransactionTemplate(new DataSourceTransactionManager(dataSource));
    }

    @Override
    public void afterSingletonsInstantiated() {
        migrate();
    }

    int migrate() {
        int deleted = cleanupLegacyRows();
        ensureIndex("fuzz_task", List.of("user_id", "id"), "uk_fuzz_task_user_id", true);
        ensureIndex("fuzz_finding", List.of("user_id", "fuzz_task_id"),
                "idx_fuzz_finding_user_task", false);
        FOREIGN_KEYS.forEach(this::ensureCascadeForeignKey);
        return deleted;
    }

    private int cleanupLegacyRows() {
        try {
            Integer deleted = transactionTemplate.execute(status -> {
                int count = jdbcTemplate.update(
                        "DELETE FROM chat_message WHERE NOT EXISTS ("
                                + "SELECT 1 FROM chat_session s JOIN app_user u ON u.id = s.user_id "
                                + "WHERE s.id = chat_message.session_id)");
                count += jdbcTemplate.update(
                        "DELETE FROM fuzz_finding WHERE NOT EXISTS ("
                                + "SELECT 1 FROM app_user u WHERE u.id = fuzz_finding.user_id) OR NOT EXISTS ("
                                + "SELECT 1 FROM fuzz_task t WHERE t.id = fuzz_finding.fuzz_task_id "
                                + "AND t.user_id = fuzz_finding.user_id)");
                for (String table : USER_OWNED_TABLES) {
                    count += jdbcTemplate.update(
                            "DELETE FROM `" + table + "` WHERE NOT EXISTS ("
                                    + "SELECT 1 FROM app_user u WHERE u.id = `" + table + "`.user_id)");
                }
                return count;
            });
            int count = deleted == null ? 0 : deleted;
            if (count > 0) {
                log.warn("Removed {} legacy user-owned row(s) without a valid owner", count);
            }
            return count;
        } catch (RuntimeException e) {
            throw new IllegalStateException("Could not remove legacy user-owned orphan rows", e);
        }
    }

    private void ensureIndex(String table, List<String> columns, String indexName, boolean unique) {
        if (hasLeadingIndex(table, columns, unique)) return;
        String uniqueness = unique ? "UNIQUE " : "";
        String columnSql = columns.stream().map(column -> "`" + column + "`")
                .reduce((left, right) -> left + ", " + right).orElseThrow();
        try {
            jdbcTemplate.execute("CREATE " + uniqueness + "INDEX `" + indexName + "` ON `"
                    + table + "` (" + columnSql + ")");
        } catch (DataAccessException e) {
            if (hasLeadingIndex(table, columns, unique)) return;
            throw new IllegalStateException("Could not create ownership index " + indexName, e);
        }
    }

    private void ensureCascadeForeignKey(ForeignKeySpec spec) {
        ForeignKeyState state = readForeignKeyState(spec);
        if (state == ForeignKeyState.VALID) return;
        if (state == ForeignKeyState.INVALID) {
            throw new IllegalStateException("Unsafe foreign key on " + spec.table() + spec.columns()
                    + "; expected ON DELETE CASCADE to " + spec.parentTable() + spec.parentColumns());
        }
        String childColumns = quotedColumns(spec.columns());
        String parentColumns = quotedColumns(spec.parentColumns());
        try {
            jdbcTemplate.execute("ALTER TABLE `" + spec.table() + "` ADD CONSTRAINT `" + spec.name()
                    + "` FOREIGN KEY (" + childColumns + ") REFERENCES `" + spec.parentTable()
                    + "` (" + parentColumns + ") ON DELETE CASCADE");
        } catch (DataAccessException e) {
            if (readForeignKeyState(spec) == ForeignKeyState.VALID) return;
            throw new IllegalStateException("Could not create cascade foreign key " + spec.name(), e);
        }
    }

    private boolean hasLeadingIndex(String table, List<String> columns, boolean requireUnique) {
        try (Connection connection = dataSource.getConnection();
             ResultSet indexes = connection.getMetaData().getIndexInfo(
                     connection.getCatalog(), null, table, false, false)) {
            Map<String, IndexColumns> byName = new LinkedHashMap<>();
            while (indexes.next()) {
                String indexName = indexes.getString("INDEX_NAME");
                String column = indexes.getString("COLUMN_NAME");
                if (indexName == null || column == null) continue;
                byName.computeIfAbsent(indexName, ignored ->
                                new IndexColumns(!indexesBoolean(indexes, "NON_UNIQUE"), new ArrayList<>()))
                        .columns().add(new OrderedColumn(indexes.getShort("ORDINAL_POSITION"), column));
            }
            return byName.values().stream().anyMatch(index -> {
                List<String> actual = index.columns().stream()
                        .sorted(Comparator.comparingInt(OrderedColumn::position))
                        .map(OrderedColumn::name)
                        .toList();
                boolean prefixMatches = actual.size() >= columns.size();
                for (int i = 0; prefixMatches && i < columns.size(); i++) {
                    prefixMatches = columns.get(i).equalsIgnoreCase(actual.get(i));
                }
                return prefixMatches && (!requireUnique || index.unique());
            });
        } catch (SQLException e) {
            throw new IllegalStateException("Could not inspect indexes for " + table, e);
        }
    }

    private boolean indexesBoolean(ResultSet indexes, String column) {
        try {
            return indexes.getBoolean(column);
        } catch (SQLException e) {
            throw new IllegalStateException("Could not inspect index metadata", e);
        }
    }

    private ForeignKeyState readForeignKeyState(ForeignKeySpec spec) {
        Map<String, List<ForeignKeyColumn>> byName = new LinkedHashMap<>();
        try (Connection connection = dataSource.getConnection();
             ResultSet keys = connection.getMetaData().getImportedKeys(
                     connection.getCatalog(), null, spec.table())) {
            while (keys.next()) {
                String name = keys.getString("FK_NAME");
                if (name == null) name = "unnamed-" + byName.size();
                byName.computeIfAbsent(name, ignored -> new ArrayList<>()).add(new ForeignKeyColumn(
                        keys.getShort("KEY_SEQ"),
                        keys.getString("FKCOLUMN_NAME"),
                        keys.getString("PKTABLE_NAME"),
                        keys.getString("PKCOLUMN_NAME"),
                        keys.getShort("DELETE_RULE")));
            }
        } catch (SQLException e) {
            throw new IllegalStateException("Could not inspect foreign keys for " + spec.table(), e);
        }

        boolean invalidExactShape = false;
        for (List<ForeignKeyColumn> columns : byName.values()) {
            List<ForeignKeyColumn> ordered = columns.stream()
                    .sorted(Comparator.comparingInt(ForeignKeyColumn::sequence))
                    .toList();
            List<String> childColumns = ordered.stream().map(ForeignKeyColumn::childColumn).toList();
            if (!sameColumns(spec.columns(), childColumns)) continue;
            boolean parentMatches = ordered.stream().allMatch(column ->
                    spec.parentTable().equalsIgnoreCase(column.parentTable()))
                    && sameColumns(spec.parentColumns(), ordered.stream()
                            .map(ForeignKeyColumn::parentColumn).toList());
            boolean cascades = ordered.stream().allMatch(column ->
                    column.deleteRule() == DatabaseMetaData.importedKeyCascade);
            if (parentMatches && cascades) return ForeignKeyState.VALID;
            invalidExactShape = true;
        }
        return invalidExactShape ? ForeignKeyState.INVALID : ForeignKeyState.MISSING;
    }

    private boolean sameColumns(List<String> expected, List<String> actual) {
        if (expected.size() != actual.size()) return false;
        for (int i = 0; i < expected.size(); i++) {
            if (!expected.get(i).equalsIgnoreCase(actual.get(i))) return false;
        }
        return true;
    }

    private String quotedColumns(List<String> columns) {
        return columns.stream().map(column -> "`" + column + "`")
                .reduce((left, right) -> left + ", " + right).orElseThrow();
    }

    private static ForeignKeySpec userForeignKey(String table, String name) {
        return new ForeignKeySpec(table, List.of("user_id"), "app_user", List.of("id"), name);
    }

    private enum ForeignKeyState {
        MISSING,
        VALID,
        INVALID
    }

    private record ForeignKeySpec(
            String table,
            List<String> columns,
            String parentTable,
            List<String> parentColumns,
            String name) {
    }

    private record ForeignKeyColumn(
            short sequence,
            String childColumn,
            String parentTable,
            String parentColumn,
            short deleteRule) {
    }

    private record OrderedColumn(short position, String name) {
    }

    private record IndexColumns(boolean unique, List<OrderedColumn> columns) {
    }
}

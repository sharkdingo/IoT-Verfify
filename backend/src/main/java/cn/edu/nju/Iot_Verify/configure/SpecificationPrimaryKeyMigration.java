package cn.edu.nju.Iot_Verify.configure;

import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.SmartInitializingSingleton;
import org.springframework.stereotype.Component;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;

/** Migrates the legacy global specification id to the user-scoped JPA identity. */
@Slf4j
@Component
public class SpecificationPrimaryKeyMigration implements SmartInitializingSingleton {

    private static final String TABLE = "specification";
    private static final List<String> LEGACY_PRIMARY_KEY = List.of("id");
    private static final Set<String> TARGET_PRIMARY_KEY = Set.of("id", "user_id");
    private static final String MYSQL_MIGRATION_SQL = "ALTER TABLE `specification` "
            + "DROP PRIMARY KEY, ADD PRIMARY KEY (`id`, `user_id`)";

    private final DataSource dataSource;

    public SpecificationPrimaryKeyMigration(DataSource dataSource) {
        this.dataSource = dataSource;
    }

    @Override
    public void afterSingletonsInstantiated() {
        migrate();
    }

    void migrate() {
        List<String> current = readPrimaryKey();
        if (isTargetPrimaryKey(current)) {
            return;
        }
        if (!LEGACY_PRIMARY_KEY.equals(current)) {
            throw unexpectedPrimaryKey(current, null);
        }

        log.warn("Migrating specification primary key from (id) to (id, user_id)");
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            executeMigration(connection, statement);
        } catch (SQLException migrationFailure) {
            List<String> afterConcurrentAttempt = readPrimaryKey();
            if (isTargetPrimaryKey(afterConcurrentAttempt)) {
                log.info("Specification primary-key migration was completed by another application instance");
                return;
            }
            throw unexpectedPrimaryKey(afterConcurrentAttempt, migrationFailure);
        }

        List<String> migrated = readPrimaryKey();
        if (!isTargetPrimaryKey(migrated)) {
            throw unexpectedPrimaryKey(migrated, null);
        }
        log.info("Specification primary-key migration completed");
    }

    private void executeMigration(Connection connection, Statement statement) throws SQLException {
        String database = connection.getMetaData().getDatabaseProductName().toLowerCase(Locale.ROOT);
        if (database.contains("mysql") || database.contains("mariadb")) {
            statement.executeUpdate(MYSQL_MIGRATION_SQL);
            return;
        }
        if (database.contains("h2")) {
            statement.executeUpdate("ALTER TABLE specification DROP PRIMARY KEY");
            statement.executeUpdate("ALTER TABLE specification ADD PRIMARY KEY (id, user_id)");
            return;
        }
        throw new SQLException("Unsupported database for specification primary-key migration: " + database);
    }

    private List<String> readPrimaryKey() {
        try (Connection connection = dataSource.getConnection()) {
            DatabaseMetaData metadata = connection.getMetaData();
            List<PrimaryKeyColumn> columns = new ArrayList<>();
            try (ResultSet resultSet = metadata.getPrimaryKeys(connection.getCatalog(), null, TABLE)) {
                while (resultSet.next()) {
                    columns.add(new PrimaryKeyColumn(
                            resultSet.getShort("KEY_SEQ"),
                            resultSet.getString("COLUMN_NAME").toLowerCase(Locale.ROOT)));
                }
            }
            return columns.stream()
                    .sorted(Comparator.comparingInt(PrimaryKeyColumn::sequence))
                    .map(PrimaryKeyColumn::name)
                    .toList();
        } catch (SQLException e) {
            throw new IllegalStateException("Could not inspect the specification primary key", e);
        }
    }

    private boolean isTargetPrimaryKey(List<String> columns) {
        return columns.size() == TARGET_PRIMARY_KEY.size()
                && new HashSet<>(columns).equals(TARGET_PRIMARY_KEY);
    }

    private IllegalStateException unexpectedPrimaryKey(List<String> columns, Exception cause) {
        String message = "Unsafe specification primary key " + columns
                + "; expected legacy [id] or user-scoped [id, user_id]";
        return cause == null ? new IllegalStateException(message) : new IllegalStateException(message, cause);
    }

    private record PrimaryKeyColumn(short sequence, String name) {
    }
}

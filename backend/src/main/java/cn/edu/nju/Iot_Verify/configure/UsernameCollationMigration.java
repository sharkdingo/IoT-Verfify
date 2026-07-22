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

/** Keeps normalized username uniqueness case- and accent-sensitive on MySQL. */
@Slf4j
@Component
public class UsernameCollationMigration implements SmartInitializingSingleton {

    static final String TARGET_COLLATION = "utf8mb4_0900_as_cs";
    private static final String COLLATION_QUERY = "SELECT COLLATION_NAME "
            + "FROM information_schema.COLUMNS "
            + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = 'app_user' AND COLUMN_NAME = 'username'";
    private static final String MIGRATION_SQL = "ALTER TABLE `app_user` MODIFY `username` "
            + "VARCHAR(50) CHARACTER SET utf8mb4 COLLATE " + TARGET_COLLATION + " NOT NULL";

    private final DataSource dataSource;

    public UsernameCollationMigration(DataSource dataSource) {
        this.dataSource = dataSource;
    }

    @Override
    public void afterSingletonsInstantiated() {
        migrate();
    }

    boolean migrate() {
        CollationInspection initial = inspectCollation();
        if (!initial.mySql()) return false;
        String current = initial.collation();
        if (TARGET_COLLATION.equalsIgnoreCase(current)) return false;

        log.warn("Migrating app_user.username collation from {} to {}", current, TARGET_COLLATION);
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            statement.executeUpdate(MIGRATION_SQL);
        } catch (SQLException migrationFailure) {
            CollationInspection afterConcurrentAttempt = inspectCollation();
            if (afterConcurrentAttempt.mySql()
                    && TARGET_COLLATION.equalsIgnoreCase(afterConcurrentAttempt.collation())) {
                log.info("Username collation migration was completed by another application instance");
                return true;
            }
            throw new IllegalStateException("Could not migrate app_user.username collation from "
                    + current + " to " + TARGET_COLLATION, migrationFailure);
        }

        CollationInspection migrated = inspectCollation();
        if (!migrated.mySql() || !TARGET_COLLATION.equalsIgnoreCase(migrated.collation())) {
            throw new IllegalStateException("Username collation migration completed without reaching "
                    + TARGET_COLLATION + "; current collation is " + migrated.collation());
        }
        log.info("Username collation migration completed");
        return true;
    }

    private CollationInspection inspectCollation() {
        try (Connection connection = dataSource.getConnection()) {
            if (!"MySQL".equalsIgnoreCase(connection.getMetaData().getDatabaseProductName())) {
                return new CollationInspection(false, null);
            }
            try (PreparedStatement statement = connection.prepareStatement(COLLATION_QUERY);
                 ResultSet resultSet = statement.executeQuery()) {
                if (!resultSet.next()) {
                    throw new IllegalStateException("Could not find app_user.username in the active MySQL schema");
                }
                String collation = resultSet.getString(1);
                if (collation == null || collation.isBlank()) {
                    throw new IllegalStateException(
                            "app_user.username has no verifiable character collation in the active MySQL schema");
                }
                return new CollationInspection(true, collation);
            }
        } catch (SQLException e) {
            throw new IllegalStateException("Could not inspect app_user.username collation", e);
        }
    }

    private record CollationInspection(boolean mySql, String collation) {
    }
}

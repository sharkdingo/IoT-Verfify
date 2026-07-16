package cn.edu.nju.Iot_Verify.configure;

import org.junit.jupiter.api.Test;
import org.springframework.jdbc.datasource.DriverManagerDataSource;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.ResultSet;
import java.sql.Statement;
import java.util.HashSet;
import java.util.Locale;
import java.util.Set;
import java.util.UUID;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class SpecificationPrimaryKeyMigrationTest {

    @Test
    void migrate_preservesRowsAndAllowsSameIdForDifferentUsers() throws Exception {
        DataSource dataSource = legacyDataSource("legacy");
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            statement.executeUpdate("INSERT INTO specification (id, user_id) VALUES ('shared-spec', 1)");
        }

        SpecificationPrimaryKeyMigration migration = new SpecificationPrimaryKeyMigration(dataSource);
        migration.migrate();
        migration.migrate();

        assertEquals(Set.of("id", "user_id"), primaryKeyColumns(dataSource));
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            statement.executeUpdate("INSERT INTO specification (id, user_id) VALUES ('shared-spec', 2)");
            try (ResultSet rows = statement.executeQuery(
                    "SELECT COUNT(*) FROM specification WHERE id = 'shared-spec'")) {
                rows.next();
                assertEquals(2, rows.getInt(1));
            }
        }
    }

    @Test
    void migrate_rejectsUnknownPrimaryKeyShape() throws Exception {
        DataSource dataSource = dataSource("unknown");
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            statement.executeUpdate("CREATE TABLE specification ("
                    + "id VARCHAR(100) NOT NULL, user_id BIGINT NOT NULL, PRIMARY KEY (user_id))");
        }

        SpecificationPrimaryKeyMigration migration = new SpecificationPrimaryKeyMigration(dataSource);

        assertThrows(IllegalStateException.class, migration::migrate);
    }

    private DataSource legacyDataSource(String suffix) throws Exception {
        DataSource dataSource = dataSource(suffix);
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            statement.executeUpdate("CREATE TABLE specification ("
                    + "id VARCHAR(100) NOT NULL, user_id BIGINT NOT NULL, PRIMARY KEY (id))");
        }
        return dataSource;
    }

    private DataSource dataSource(String suffix) {
        String name = "spec_pk_" + suffix + "_" + UUID.randomUUID().toString().replace("-", "");
        return new DriverManagerDataSource(
                "jdbc:h2:mem:" + name + ";MODE=MySQL;DATABASE_TO_LOWER=TRUE;DB_CLOSE_DELAY=-1",
                "sa",
                "");
    }

    private Set<String> primaryKeyColumns(DataSource dataSource) throws Exception {
        Set<String> columns = new HashSet<>();
        try (Connection connection = dataSource.getConnection()) {
            DatabaseMetaData metadata = connection.getMetaData();
            try (ResultSet resultSet = metadata.getPrimaryKeys(connection.getCatalog(), null, "specification")) {
                while (resultSet.next()) {
                    columns.add(resultSet.getString("COLUMN_NAME").toLowerCase(Locale.ROOT));
                }
            }
        }
        return columns;
    }
}

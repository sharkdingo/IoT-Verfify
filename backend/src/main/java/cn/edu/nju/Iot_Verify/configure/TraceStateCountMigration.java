package cn.edu.nju.Iot_Verify.configure;

import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.SmartInitializingSingleton;
import org.springframework.stereotype.Component;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Locale;

/** Backfills compact trace metadata so history summaries never need to load states_json. */
@Slf4j
@Component
public class TraceStateCountMigration implements SmartInitializingSingleton {

    private static final String STATE_COUNT_EXPRESSION = "CASE "
            + "WHEN states_json IS NOT NULL AND JSON_VALID(states_json) "
            + "THEN COALESCE(JSON_LENGTH(states_json), 0) ELSE 0 END";
    private static final String TRACE_BACKFILL = "UPDATE trace SET state_count = "
            + STATE_COUNT_EXPRESSION + " WHERE state_count IS NULL";
    private static final String SIMULATION_BACKFILL = "UPDATE simulation_trace SET state_count = "
            + STATE_COUNT_EXPRESSION + " WHERE state_count IS NULL";

    private final DataSource dataSource;

    public TraceStateCountMigration(DataSource dataSource) {
        this.dataSource = dataSource;
    }

    @Override
    public void afterSingletonsInstantiated() {
        migrate();
    }

    boolean migrate() {
        try (Connection connection = dataSource.getConnection()) {
            String product = connection.getMetaData().getDatabaseProductName().toLowerCase(Locale.ROOT);
            if (!product.contains("mysql") && !product.contains("mariadb")) return false;
            try (Statement statement = connection.createStatement()) {
                int verificationRows = statement.executeUpdate(TRACE_BACKFILL);
                int simulationRows = statement.executeUpdate(SIMULATION_BACKFILL);
                if (verificationRows > 0 || simulationRows > 0) {
                    log.info("Backfilled trace state counts: verification={}, simulation={}",
                            verificationRows, simulationRows);
                }
            }
            return true;
        } catch (SQLException e) {
            throw new IllegalStateException("Could not backfill trace state-count metadata", e);
        }
    }
}

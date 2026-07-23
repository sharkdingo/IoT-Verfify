package cn.edu.nju.Iot_Verify.configure;

import org.junit.jupiter.api.Test;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.Statement;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.contains;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

class TraceStateCountMigrationTest {

    @Test
    void migrate_backfillsBothHistoryTablesOnMySql() throws Exception {
        DataSource dataSource = mock(DataSource.class);
        Connection connection = mock(Connection.class);
        DatabaseMetaData metadata = mock(DatabaseMetaData.class);
        Statement statement = mock(Statement.class);
        when(dataSource.getConnection()).thenReturn(connection);
        when(connection.getMetaData()).thenReturn(metadata);
        when(metadata.getDatabaseProductName()).thenReturn("MySQL");
        when(connection.createStatement()).thenReturn(statement);

        assertTrue(new TraceStateCountMigration(dataSource).migrate());

        verify(statement).executeUpdate(contains("UPDATE trace "));
        verify(statement).executeUpdate(contains("UPDATE simulation_trace "));
        verify(statement, org.mockito.Mockito.times(2)).executeUpdate(contains("JSON_VALID(states_json)"));
    }

    @Test
    void migrate_skipsNonMySqlDatabases() throws Exception {
        DataSource dataSource = mock(DataSource.class);
        Connection connection = mock(Connection.class);
        DatabaseMetaData metadata = mock(DatabaseMetaData.class);
        when(dataSource.getConnection()).thenReturn(connection);
        when(connection.getMetaData()).thenReturn(metadata);
        when(metadata.getDatabaseProductName()).thenReturn("H2");

        assertFalse(new TraceStateCountMigration(dataSource).migrate());

        verify(connection, never()).createStatement();
    }
}

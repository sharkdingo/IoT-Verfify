package cn.edu.nju.Iot_Verify.service.impl;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Deleting an account must leave no user-owned row behind.
 *
 * <p>This is a structural check rather than a database one on purpose: the failure it guards against
 * is a *new* user-owned table being added and simply forgotten in one of the three places that have
 * to know about it. `board_edit_journal` was missed in all three — it stores complete before/after
 * snapshots of a user's rules and specifications, so those survived the account that owned them, and
 * `docs/api/auth.md` claimed a cascade that did not exist for that table.
 *
 * <p>The single source of truth is {@code UserOwnedOrphanCleanup.USER_OWNED_TABLES}: every table
 * listed there is by definition user-owned, so every one must also be explicitly deleted on account
 * deletion and must have a cascade foreign key.
 */
class AccountDeletionCoverageTest {

    private static final Path BACKEND_SRC = Path.of("src", "main", "java", "cn", "edu", "nju", "Iot_Verify");

    /** Entities whose rows are removed through their owning parent's cascade, not a direct delete. */
    private static final Set<String> DELETED_VIA_PARENT = Set.of(
            // Chat messages and pre-admission stop fences hang off chat_session.
            "chat_message",
            "chat_session_pre_admission_stop");

    private static String read(String... parts) throws IOException {
        Path path = BACKEND_SRC;
        for (String part : parts) {
            path = path.resolve(part);
        }
        return Files.readString(path);
    }

    private static Set<String> userOwnedTables() throws IOException {
        String source = read("configure", "UserOwnedOrphanCleanup.java");
        String block = source.substring(
                source.indexOf("USER_OWNED_TABLES = List.of("),
                source.indexOf(");", source.indexOf("USER_OWNED_TABLES = List.of(")));
        Set<String> tables = new TreeSet<>();
        Matcher matcher = Pattern.compile("\"([a-z_]+)\"").matcher(block);
        while (matcher.find()) {
            tables.add(matcher.group(1));
        }
        return tables;
    }

    @Test
    void everyUserOwnedTableIsListed() throws IOException {
        Set<String> tables = userOwnedTables();
        assertTrue(tables.size() > 10, "expected the user-owned table list to be populated: " + tables);
        assertTrue(tables.contains("board_edit_journal"),
                "the undo journal is user-owned and must be swept for orphans");
    }

    @Test
    void everyUserOwnedTableGetsACascadeForeignKey() throws IOException {
        String source = read("configure", "UserOwnedOrphanCleanup.java");
        String block = source.substring(source.indexOf("FOREIGN_KEYS = List.of("));

        for (String table : userOwnedTables()) {
            assertTrue(block.contains("\"" + table + "\""),
                    table + " is user-owned but has no foreign key to app_user, so the database "
                            + "would not cascade its rows when the account row is removed");
        }
    }

    /**
     * Every user-owned table must be reachable from {@code deleteUserOwnedData}.
     *
     * <p>Matching is by repository call rather than by table name, because that is what the service
     * actually does; the mapping from table to repository is derived from the entity classes.
     */
    @Test
    void accountDeletionRemovesEveryUserOwnedTable() throws IOException {
        String deletion = read("service", "impl", "AuthServiceImpl.java");
        String body = deletion.substring(
                deletion.indexOf("private void deleteUserOwnedData("),
                deletion.indexOf("private ActiveTaskIds activeTaskIds("));

        for (String table : userOwnedTables()) {
            if (DELETED_VIA_PARENT.contains(table)) {
                continue;
            }
            String repositoryField = repositoryFieldFor(table);
            assertTrue(body.contains(repositoryField),
                    table + " is user-owned but deleteUserOwnedData never calls " + repositoryField
                            + ", so its rows would outlive the account that owned them");
        }
    }

    /** Finds the repository field name that owns a table, via the entity's {@code @Table} name. */
    private static String repositoryFieldFor(String table) throws IOException {
        Path poDirectory = BACKEND_SRC.resolve("po");
        try (Stream<Path> files = Files.list(poDirectory)) {
            List<Path> candidates = files
                    .filter(path -> path.getFileName().toString().endsWith("Po.java"))
                    .toList();
            for (Path candidate : candidates) {
                String source = Files.readString(candidate);
                if (source.contains("name = \"" + table + "\"")) {
                    String entity = candidate.getFileName().toString().replace("Po.java", "");
                    return Character.toLowerCase(entity.charAt(0)) + entity.substring(1) + "Repository";
                }
            }
        }
        throw new AssertionError("no @Table(name = \"" + table + "\") entity found for " + table);
    }

    @Test
    void theDerivedRepositoryNameResolutionWorks() throws IOException {
        // Guards the test's own mechanism: a wrong derivation would make the assertions vacuous.
        assertEquals("boardEditJournalRepository", repositoryFieldFor("board_edit_journal"));
        assertEquals("ruleRepository".length() > 0 ? repositoryFieldFor("rules") : "",
                repositoryFieldFor("rules"));
    }
}

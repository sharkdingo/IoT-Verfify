package cn.edu.nju.Iot_Verify.service.board;

import cn.edu.nju.Iot_Verify.po.BoardEditEntityType;
import cn.edu.nju.Iot_Verify.po.BoardEditJournalPo;
import cn.edu.nju.Iot_Verify.po.BoardEditOperation;
import cn.edu.nju.Iot_Verify.repository.BoardEditJournalRepository;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.jdbc.AutoConfigureTestDatabase;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Ordering and invalidation rules of the edit journal. These are the rules that decide whether an
 * undo can silently discard newer work, so they are asserted on the store rather than only through
 * the board service.
 */
@DataJpaTest(properties = {
        "spring.jpa.database-platform=org.hibernate.dialect.H2Dialect",
        "spring.jpa.properties.hibernate.dialect=org.hibernate.dialect.H2Dialect",
        "spring.jpa.hibernate.ddl-auto=create-drop"
})
@AutoConfigureTestDatabase(replace = AutoConfigureTestDatabase.Replace.ANY)
class BoardEditJournalTest {

    private static final Long USER = 7L;
    private static final Long OTHER_USER = 8L;

    @Autowired
    private BoardEditJournalRepository repository;

    private BoardEditJournal journal;

    @BeforeEach
    void setUp() {
        journal = new BoardEditJournal(repository, new ObjectMapper());
    }

    private void recordRuleDelete(String key, String payload) {
        journal.record(USER, BoardEditEntityType.RULE, BoardEditOperation.DELETE, key,
                new Payload(payload), null);
    }

    @Test
    void undoTakesTheNewestEditAndRedoTakesTheOldestUndoneOne() {
        recordRuleDelete("1", "first");
        recordRuleDelete("2", "second");

        BoardEditJournalPo newest = journal.nextToUndo(USER).orElseThrow();
        assertEquals("2", newest.getEntityKey());

        journal.markUndone(newest, true);
        BoardEditJournalPo next = journal.nextToUndo(USER).orElseThrow();
        assertEquals("1", next.getEntityKey());
        journal.markUndone(next, true);

        // Redo replays in the order the user originally worked, oldest first.
        assertEquals("1", journal.nextToRedo(USER).orElseThrow().getEntityKey());
    }

    @Test
    void aNewEditDiscardsTheAbandonedRedoBranch() {
        recordRuleDelete("1", "first");
        journal.markUndone(journal.nextToUndo(USER).orElseThrow(), true);
        assertTrue(journal.availability(USER).canRedo());

        // Editing after an undo makes the undone entry unreachable: redoing it would overwrite the
        // edit just made, so it must not remain offered.
        recordRuleDelete("2", "second");

        assertFalse(journal.availability(USER).canRedo());
        assertEquals(Optional.empty(), journal.nextToRedo(USER));
        assertTrue(journal.availability(USER).canUndo());
    }

    @Test
    void sequencesAreMonotonicPerUserAndNotSharedBetweenAccounts() {
        recordRuleDelete("1", "first");
        recordRuleDelete("2", "second");
        journal.record(OTHER_USER, BoardEditEntityType.RULE, BoardEditOperation.DELETE, "9",
                new Payload("other"), null);

        assertEquals(2L, journal.nextToUndo(USER).orElseThrow().getSequence());
        // A second account starts its own history rather than continuing the first one's.
        assertEquals(1L, journal.nextToUndo(OTHER_USER).orElseThrow().getSequence());
    }

    @Test
    void availabilityIsFalseOnBothSidesForAnAccountWithNoHistory() {
        BoardUndoAvailability availability = journal.availability(USER);
        assertFalse(availability.canUndo());
        assertFalse(availability.canRedo());
    }

    @Test
    void clearRemovesOnlyTheRequestedAccountsHistory() {
        recordRuleDelete("1", "first");
        journal.record(OTHER_USER, BoardEditEntityType.RULE, BoardEditOperation.DELETE, "9",
                new Payload("other"), null);

        journal.clear(USER);

        assertFalse(journal.availability(USER).canUndo());
        assertTrue(journal.availability(OTHER_USER).canUndo());
    }

    @Test
    void anUnreadablePayloadIsReportedAsUnusableRatherThanThrowing() {
        BoardEditJournalPo entry = repository.save(BoardEditJournalPo.builder()
                .userId(USER).sequence(1L)
                .entityType(BoardEditEntityType.RULE).operation(BoardEditOperation.DELETE)
                .entityKey("1").beforeJson("{not json").undone(false)
                .createdAt(java.time.LocalDateTime.now())
                .build());

        assertNull(journal.readJson(entry.getBeforeJson(), Payload.class));
        assertNull(journal.readJson(null, Payload.class));
    }

    @Test
    void historyIsCappedByDroppingTheOldestEntries() {
        for (int i = 1; i <= 55; i++) {
            recordRuleDelete(String.valueOf(i), "edit-" + i);
        }

        // Bounded so a long-lived account cannot grow the journal without limit.
        assertEquals(50, repository.findByUserIdOrderBySequenceAsc(USER).size());
        // The newest edit is still the next undo, and the oldest have been dropped.
        assertEquals("55", journal.nextToUndo(USER).orElseThrow().getEntityKey());
        assertEquals("6", repository.findByUserIdOrderBySequenceAsc(USER).get(0).getEntityKey());
    }

    /** Minimal serializable stand-in; the journal is payload-agnostic. */
    public record Payload(String name) {
    }
}

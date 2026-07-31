package cn.edu.nju.Iot_Verify.service.board;

import cn.edu.nju.Iot_Verify.po.BoardEditEntityType;
import cn.edu.nju.Iot_Verify.po.BoardEditOperation;
import cn.edu.nju.Iot_Verify.repository.BoardEditJournalRepository;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class BoardEditJournalRecordTest {

    private static final Long USER_ID = 7L;

    @Mock
    private BoardEditJournalRepository repository;

    private BoardEditJournal journal;

    @BeforeEach
    void setUp() {
        journal = new BoardEditJournal(repository, new ObjectMapper());
    }

    @Test
    void firstEditDoesNotIssueAnEmptyRedoBranchDelete() {
        journal.record(USER_ID, BoardEditEntityType.RULE, BoardEditOperation.DELETE,
                "1", new Payload("before"), null);

        verify(repository, never()).deleteByUserIdAndUndoneTrue(USER_ID);
    }

    @Test
    void editAfterUndoDeletesTheAbandonedRedoBranch() {
        when(repository.existsByUserIdAndUndoneTrue(USER_ID)).thenReturn(true);

        journal.record(USER_ID, BoardEditEntityType.RULE, BoardEditOperation.DELETE,
                "1", new Payload("before"), null);

        verify(repository).deleteByUserIdAndUndoneTrue(USER_ID);
    }

    private record Payload(String name) {
    }
}

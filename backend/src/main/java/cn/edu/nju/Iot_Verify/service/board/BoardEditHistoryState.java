package cn.edu.nju.Iot_Verify.service.board;

/** Snapshot used to bind destructive history clearing to the entries the user confirmed. */
public record BoardEditHistoryState(
        int entryCount,
        BoardUndoAvailability availability,
        String impactToken
) {
}

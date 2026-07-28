package cn.edu.nju.Iot_Verify.service.board;

/**
 * Whether the account currently has an edit to undo and/or one to redo.
 *
 * <p>Returned with every board mutation and undo result so the client never has to guess at
 * availability from its own local history — the journal is the authority.
 */
public record BoardUndoAvailability(boolean canUndo, boolean canRedo) {
}

package cn.edu.nju.Iot_Verify.dto.board;

import lombok.Builder;
import lombok.Data;
import lombok.ToString;

/** Authoritative journal impact shown before all undo/redo history is discarded. */
@Data
@Builder
public class BoardEditHistoryClearPreviewDto {
    @ToString.Exclude
    private String impactToken;
    private int entryCount;
    private boolean canUndo;
    private boolean canRedo;
}

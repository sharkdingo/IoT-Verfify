package cn.edu.nju.Iot_Verify.exception;

import cn.edu.nju.Iot_Verify.dto.board.BoardReplacementPreviewDto;
import lombok.Getter;

/** The board changed after a destructive scene-replacement preview was confirmed. */
@Getter
public class BoardReplacementStaleException extends ConflictException {

    private final BoardReplacementPreviewDto currentPreview;

    public BoardReplacementStaleException(BoardReplacementPreviewDto currentPreview) {
        super("The current scene changed after confirmation. No scene data was replaced; "
                + "review the refreshed scene and confirm again.");
        this.currentPreview = currentPreview;
    }
}

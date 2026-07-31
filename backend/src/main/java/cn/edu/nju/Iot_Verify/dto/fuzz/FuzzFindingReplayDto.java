package cn.edu.nju.Iot_Verify.dto.fuzz;

import cn.edu.nju.Iot_Verify.dto.model.ModelPlaybackSceneDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * One candidate finding together with the immutable run context required to replay it.
 * The context is read and validated with the selected finding, not inferred from the
 * user's current Board or sibling findings.
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FuzzFindingReplayDto {
    private FuzzFindingDto finding;
    private ModelRunSnapshotDto modelSnapshot;
    private ModelPlaybackSceneDto playbackScene;
}

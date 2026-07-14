package cn.edu.nju.Iot_Verify.dto.device;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class DefaultTemplateResetChangeDto {
    public enum ChangeType {
        RESTORE_MISSING,
        REFRESH_DEFAULT,
        REPLACE_CUSTOM_NAME_COLLISION,
        REMOVE_OBSOLETE_DEFAULT
    }

    private String templateName;
    private ChangeType changeType;
    private boolean semanticsChanged;
}

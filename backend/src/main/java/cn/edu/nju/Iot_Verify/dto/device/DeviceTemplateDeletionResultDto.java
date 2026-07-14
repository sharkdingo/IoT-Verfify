package cn.edu.nju.Iot_Verify.dto.device;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class DeviceTemplateDeletionResultDto {
    private String operation;
    private String impactToken;
    private boolean canDelete;
    private DeviceTemplateDto template;
    private DeviceTemplateDto deletedTemplate;
    @Builder.Default
    private List<DeviceTemplateDeletionBlockerDto> blockers = List.of();
    @Builder.Default
    private List<DeviceTemplateDto> currentTemplates = List.of();
}

package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import org.springframework.stereotype.Component;

import java.util.List;

/**
 * VerificationTask PO 与 DTO 之间的转换映射器
 */
@Component
public class VerificationTaskMapper {

    /**
     * VerificationTaskPo -> VerificationTaskDto
     */
    public VerificationTaskDto toDto(VerificationTaskPo po) {
        if (po == null) {
            return null;
        }

        return VerificationTaskDto.builder()
                .id(po.getId())
                .status(po.getStatus() != null ? po.getStatus().name() : null)
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .isSafe(po.getIsSafe())
                .violatedSpecCount(po.getViolatedSpecCount())
                .checkLogs(po.getCheckLogs())
                .errorMessage(po.getErrorMessage())
                .build();
    }

    /**
     * List<VerificationTaskPo> -> List<VerificationTaskDto>
     */
    public List<VerificationTaskDto> toDtoList(List<VerificationTaskPo> poList) {
        if (poList == null) {
            return List.of();
        }
        return poList.stream()
                .map(this::toDto)
                .toList();
    }
}

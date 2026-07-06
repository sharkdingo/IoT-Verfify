package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.verification.SpecResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
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
                .disabledRuleCount(po.getDisabledRuleCount())
                .skippedSpecCount(po.getSkippedSpecCount())
                .specResults(readSpecResults(po.getSpecResultsJson()))
                .checkLogs(po.getCheckLogs() != null ? po.getCheckLogs() : JsonUtils.fromJsonToStringList(po.getCheckLogsJson()))
                .nusmvOutput(po.getNusmvOutput())
                .errorMessage(po.getErrorMessage())
                .progress(po.getProgress())
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

    public VerificationTaskSummaryDto toSummaryDto(VerificationTaskPo po) {
        if (po == null) {
            return null;
        }

        return VerificationTaskSummaryDto.builder()
                .id(po.getId())
                .status(po.getStatus() != null ? po.getStatus().name() : null)
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .progress(po.getProgress())
                .isSafe(po.getIsSafe())
                .violatedSpecCount(po.getViolatedSpecCount())
                .disabledRuleCount(po.getDisabledRuleCount())
                .skippedSpecCount(po.getSkippedSpecCount())
                .errorMessage(po.getErrorMessage())
                .build();
    }

    public List<VerificationTaskSummaryDto> toSummaryDtoList(List<VerificationTaskPo> poList) {
        if (poList == null) {
            return List.of();
        }
        return poList.stream()
                .map(this::toSummaryDto)
                .toList();
    }

    private List<SpecResultDto> readSpecResults(String json) {
        // Legacy rows are stored as [true,false]. Detect them before structured parsing
        // because Jackson can otherwise coerce scalar array elements into empty DTO objects.
        // Structured SpecResultDto arrays always start with an object ("[{...}]"), not an
        // unquoted true/false literal.
        if (looksLikeLegacyBooleanArray(json)) {
            return readLegacySpecResults(json);
        }

        List<SpecResultDto> structured = JsonUtils.fromJsonList(json, SpecResultDto.class);
        if (!structured.isEmpty()) {
            return structured;
        }

        return readLegacySpecResults(json);
    }

    private List<SpecResultDto> readLegacySpecResults(String json) {
        List<Boolean> legacy = JsonUtils.fromJsonList(json, Boolean.class);
        if (legacy.isEmpty()) {
            return List.of();
        }

        List<SpecResultDto> converted = new ArrayList<>(legacy.size());
        for (int i = 0; i < legacy.size(); i++) {
            converted.add(SpecResultDto.builder()
                    .specId("legacy-" + (i + 1))
                    .passed(Boolean.TRUE.equals(legacy.get(i)))
                    .expression("")
                    .build());
        }
        return converted;
    }

    private boolean looksLikeLegacyBooleanArray(String json) {
        if (json == null || json.isBlank()) {
            return false;
        }
        String trimmed = json.trim();
        if (!trimmed.startsWith("[")) {
            return false;
        }
        for (int i = 1; i < trimmed.length(); i++) {
            char c = trimmed.charAt(i);
            if (Character.isWhitespace(c)) {
                continue;
            }
            return c == 't' || c == 'f' || c == 'T' || c == 'F';
        }
        return false;
    }
}

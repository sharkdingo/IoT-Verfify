package cn.edu.nju.Iot_Verify.dto.verification;

import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import lombok.Builder;
import lombok.Data;

import java.util.List;

/**
 * 验证结果
 */
@Data
@Builder
public class VerificationResultDto {
    /**
     * 是否安全
     */
    private boolean safe;

    /**
     * 错误轨迹列表
     */
    private List<TraceDto> traces;

    /**
     * 每个规格的检查结果
     */
    private List<Boolean> specResults;

    /**
     * 检查日志
     */
    private List<String> checkLogs;

    /**
     * 原始 NuSMV 输出
     */
    private String nusmvOutput;
}

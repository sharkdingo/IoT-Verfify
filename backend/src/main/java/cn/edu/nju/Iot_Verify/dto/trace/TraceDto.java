package cn.edu.nju.Iot_Verify.dto.trace;

import com.fasterxml.jackson.annotation.JsonInclude;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;
import java.util.List;

/**
 * 验证轨迹传输对象
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class TraceDto {
    /**
     * 数据库ID
     */
    @NotNull(message = "ID is required")
    private Long id;
    
    /**
     * 用户ID
     */
    @NotNull(message = "User ID is required")
    private Long userId;
    
    /**
     * 关联的验证任务ID（同步验证时可为 null）
     */
    private Long verificationTaskId;
    
    /**
     * 违反的规格ID
     */
    private String violatedSpecId;
    
    /**
     * 违反的规格内容（JSON）
     */
    private String violatedSpecJson;
    
    /**
     * 状态序列
     */
    @Valid
    @NotNull(message = "States are required")
    private List<TraceStateDto> states;
    
    /**
     * 创建时间
     */
    private LocalDateTime createdAt;
}

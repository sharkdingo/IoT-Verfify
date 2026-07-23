package cn.edu.nju.Iot_Verify.dto.trace;

import cn.edu.nju.Iot_Verify.dto.model.ModelTokenSource;
import lombok.Data;

/**
 * 轨迹中的变量变化
 */
@Data
public class TraceVariableDto {
    /**
     * 变量名
     */
    private String name;
    
    /**
     * 值
     */
    private String value;
    
    /**
     * 信任度: trusted | untrusted
     */
    private String trust;

    /** Frozen source for environment identifiers/values; absent legacy values are UNKNOWN. */
    private ModelTokenSource modelTokenSource;
}

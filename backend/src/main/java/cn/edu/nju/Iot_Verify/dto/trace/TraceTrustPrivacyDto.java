package cn.edu.nju.Iot_Verify.dto.trace;

import lombok.Data;

/**
 * 轨迹中的信任/隐私变化
 */
@Data
public class TraceTrustPrivacyDto {
    /**
     * 名称（状态名或内容名）
     */
    private String name;
    
    /**
     * 信任度: true=trusted, false=untrusted, null=unknown
     * 使用 Boolean 包装类型以支持 null 值（JSON 序列化时能区分 false 和 null）
     */
    private Boolean trust;
    
    /**
     * 隐私级别: private | public
     */
    private String privacy;
}

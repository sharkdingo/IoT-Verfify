package cn.edu.nju.Iot_Verify.dto.verification;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import lombok.Data;

import java.util.List;

/**
 * 验证请求
 * 
 * 参考 MEDIC-test 中的攻击模式支持，添加 isAttack 和 intensity 参数
 * 
 * 注意：Trace 会自动保存（当检测到违规时），无需前端传入 saveTrace 参数
 */
@Data
public class VerificationRequestDto {
    /**
     * 设备节点列表
     */
    private List<DeviceNodeDto> devices;

    /**
     * 规则列表
     */
    private List<RuleDto> rules;

    /**
     * 规格列表
     */
    private List<SpecificationDto> specs;
    
    /**
     * 是否启用攻击模式
     * 参考 MEDIC-test SMVGeneration.java 中的 isAttack 标志
     */
    private boolean isAttack = false;
    
    /**
     * 攻击强度 (0-50)
     * 参考 MEDIC-test SMVGeneration.java 中的 intensity 参数
     * 
     * MEDIC-test 用法：
     * - intensity 控制攻击的强度，范围 0-50
     * - 在规格中添加 intensity<=N 条件来限制攻击影响
     * - 示例：SPEC AG !(door.state=open & door.trust_LockState=untrusted & intensity<=3)
     */
    private int intensity = 3;
}

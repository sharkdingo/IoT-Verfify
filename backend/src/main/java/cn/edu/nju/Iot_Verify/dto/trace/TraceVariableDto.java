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

    /**
     * Whether {@link #value} is a reading this device actually took.
     *
     * <p>False for an affect-only shared declaration ({@code IsInside=false, Reads=false}): the model
     * declares {@code <device>.<name>} to carry the label and impact machinery, but never constrains
     * it, so NuSMV prints an arbitrary member of the domain. Publishing that number as a device
     * reading contradicted the environment strip in the same view (the demo scene showed
     * {@code light_1.illuminance = 0} beside {@code illuminance = 20}).
     *
     * <p>The row itself must stay: {@code CounterexampleInitialStateConstraints} requires one for
     * every manifest variable and reads this variable's trust from it. So the value is emptied rather
     * than nulled — {@code TraceStateIntegrity} cannot distinguish an affect-only row from a corrupt
     * one (it has no manifest), and a null there is indistinguishable from a parse failure.
     * The true environment value is already published once, in the state's {@code envVariables[]}.
     */
    private boolean observed = true;

    /** Required frozen source for environment identifiers and values. */
    private ModelTokenSource modelTokenSource;
}

package cn.edu.nju.Iot_Verify.repository.projection;

import cn.edu.nju.Iot_Verify.po.FuzzTaskPo;

/** Scalar task state used by high-frequency progress polling. */
public interface FuzzTaskProgressProjection {

    Integer getProgress();

    FuzzTaskPo.TaskStatus getStatus();
}

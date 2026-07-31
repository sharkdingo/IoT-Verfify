package cn.edu.nju.Iot_Verify.service;

/** Account-scoped control for in-flight chat execution lifecycle. */
public interface ChatExecutionControl {

    void requestUserExecutionStop(Long userId);

    void requestLocalUserExecutionStop(Long userId);
}

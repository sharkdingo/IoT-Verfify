package cn.edu.nju.Iot_Verify.service;

/** Local-process control used to stop in-flight chat work after account deletion commits. */
public interface ChatExecutionControl {

    void requestLocalUserExecutionStop(Long userId);
}

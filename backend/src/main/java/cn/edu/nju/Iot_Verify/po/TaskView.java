package cn.edu.nju.Iot_Verify.po;

/**
 * 任务 PO 的公共视图接口，为 {@link cn.edu.nju.Iot_Verify.service.impl.AbstractAsyncTaskService}
 * 的泛型参数提供类型约束。
 *
 * <p>{@link VerificationTaskPo} 和 {@link SimulationTaskPo} 各自实现此接口。
 */
public interface TaskView {

    Long getId();

    Integer getProgress();

    /** 判断任务是否处于终态（COMPLETED / FAILED / CANCELLED）。 */
    boolean isTerminalStatus();

    String getCheckLogsJson();

    void setCheckLogsJson(String json);
}

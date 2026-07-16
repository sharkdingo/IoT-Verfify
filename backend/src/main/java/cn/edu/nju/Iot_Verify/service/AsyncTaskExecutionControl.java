package cn.edu.nju.Iot_Verify.service;

/**
 * Local-process control for an asynchronous task whose durable row may already be gone.
 * Database lifecycle transitions remain owned by the domain service.
 */
public interface AsyncTaskExecutionControl {

    boolean requestLocalExecutionStop(Long taskId);
}

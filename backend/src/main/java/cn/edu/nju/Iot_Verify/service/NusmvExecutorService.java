package cn.edu.nju.Iot_Verify.service;

import java.io.IOException;

/**
 * NuSMV 执行器接口
 */
public interface NusmvExecutorService {
    
    /**
     * 执行 NuSMV 命令
     * 
     * @param smvFile NuSMV 模型文件
     * @return NuSMV 输出结果
     * @throws IOException IO 异常
     * @throws InterruptedException 进程中断异常
     */
    NusmvResult execute(java.io.File smvFile) throws IOException, InterruptedException;
    
    /**
     * NuSMV 执行结果
     */
    class NusmvResult {
        private final String output;
        private final boolean hasCounterexample;
        private final String counterexample;
        private final boolean success;
        private final String errorMessage;
        
        public NusmvResult(String output, boolean hasCounterexample, String counterexample) {
            this.output = output;
            this.hasCounterexample = hasCounterexample;
            this.counterexample = counterexample;
            this.success = true;
            this.errorMessage = null;
        }
        
        public NusmvResult(String errorMessage) {
            this.output = null;
            this.hasCounterexample = false;
            this.counterexample = null;
            this.success = false;
            this.errorMessage = errorMessage;
        }
        
        public String getOutput() { return output; }
        public boolean hasCounterexample() { return hasCounterexample; }
        public String getCounterexample() { return counterexample; }
        public boolean isSuccess() { return success; }
        public String getErrorMessage() { return errorMessage; }
    }
}

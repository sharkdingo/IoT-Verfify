package cn.edu.nju.Iot_Verify.component.fuzz;

@FunctionalInterface
public interface FuzzProgressListener {
    void onProgress(int percent, String message);
}

package cn.edu.nju.Iot_Verify.service;

public interface NodeService {
    String searchNodes(Long userId, String keyword);
    String addNode(Long userId, String templateName, String label, Double x, Double y, String state, Integer w, Integer h);
    String deleteNode(Long userId, String label);
}

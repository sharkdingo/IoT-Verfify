package cn.edu.nju.Iot_Verify.service;

public interface NodeService {

    /**
     * 搜索节点
     * @param keyword 关键词
     * @return JSON 格式的结果字符串
     */
    String searchNodes(String keyword);

    /**
     * 添加节点
     * @param templateName 模板类型 (server, switch)
     * @param label 显示名称
     * @param x X坐标 (可为null)
     * @param y Y坐标 (可为null)
     * @param state 状态 (可为null)
     * @return 执行结果消息
     */
    String addNode(String templateName, String label, Double x, Double y, String state, Integer w, Integer h);

    /**
     * 删除节点
     * @param label 设备的显示名称 (Label)
     */
    String deleteNode(String label);
}
package cn.edu.nju.Iot_Verify.util;

import java.util.List;
import java.util.Map;

/**
 * 辅助类：用于快速构建符合 AI SDK 规范的参数定义
 */
public class FunctionParameterSchema {
    public String type;
    public Map<String, Object> properties;
    public List<String> required;

    public FunctionParameterSchema(String type, Map<String, Object> properties, List<String> required) {
        this.type = type;
        this.properties = properties;
        this.required = required;
    }
}
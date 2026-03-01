package cn.edu.nju.Iot_Verify.component.aitool;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import lombok.RequiredArgsConstructor;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.List;
import java.util.Locale;

/**
 * 共享工具类：将画板设备节点转换为验证/模拟所需的 DTO
 */
@Component
@RequiredArgsConstructor
public class BoardDataHelper {

    private final BoardStorageService boardStorageService;

    /**
     * 从画板读取设备节点并转换为 DeviceVerificationDto 列表
     */
    public List<DeviceVerificationDto> getDevicesForVerification(Long userId) {
        List<DeviceNodeDto> nodes = boardStorageService.getNodes(userId);
        if (nodes == null) {
            nodes = Collections.emptyList();
        }
        return nodes.stream()
                .filter(n -> n != null && !isVariableNode(n))
                .map(n -> {
                    String varName = trimToNull(n.getId());
                    if (varName == null) {
                        varName = trimToNull(n.getLabel());
                    }
                    if (varName == null) {
                        return null;
                    }

                    DeviceVerificationDto dv = new DeviceVerificationDto();
                    dv.setVarName(varName);
                    dv.setTemplateName(n.getTemplateName());
                    dv.setState(n.getState());
                    dv.setCurrentStateTrust(n.getCurrentStateTrust());
                    dv.setVariables(n.getVariables());
                    dv.setPrivacies(n.getPrivacies());
                    return dv;
                })
                .filter(dv -> dv != null)
                .toList();
    }

    private boolean isVariableNode(DeviceNodeDto node) {
        String templateName = node.getTemplateName();
        if (templateName == null) {
            return false;
        }
        return templateName.toLowerCase(Locale.ROOT).startsWith("variable_");
    }

    private String trimToNull(String value) {
        if (value == null) {
            return null;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }
}

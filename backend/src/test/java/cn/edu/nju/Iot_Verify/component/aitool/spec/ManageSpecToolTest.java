package cn.edu.nju.Iot_Verify.component.aitool.spec;

import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;

@ExtendWith(MockitoExtension.class)
class ManageSpecToolTest {

    @Mock
    private BoardStorageService boardStorageService;

    private ManageSpecTool tool;

    @BeforeEach
    void setUp() {
        tool = new ManageSpecTool(boardStorageService, new ObjectMapper());
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void add_withUnknownTemplateId_shouldReject() {
        String argsJson = """
                {
                  "action":"add",
                  "templateId":"99",
                  "aConditions":[
                    {
                      "deviceId":"dev_1",
                      "targetType":"state",
                      "key":"state",
                      "relation":"=",
                      "value":"On"
                    }
                  ]
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("Unsupported templateId"));
        verify(boardStorageService, never()).saveSpecs(anyLong(), any());
    }
}

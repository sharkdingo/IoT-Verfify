package cn.edu.nju.Iot_Verify.component.aitool.rule;

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
class ManageRuleToolTest {

    @Mock
    private BoardStorageService boardStorageService;

    private ManageRuleTool tool;

    @BeforeEach
    void setUp() {
        tool = new ManageRuleTool(boardStorageService, new ObjectMapper());
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void add_withUnsupportedRelation_shouldReject() {
        String argsJson = """
                {
                  "action":"add",
                  "conditions":[
                    {
                      "deviceName":"Light_1",
                      "attribute":"state",
                      "relation":"approx",
                      "value":"On"
                    }
                  ],
                  "command":{
                    "deviceName":"Light_1",
                    "action":"turnOn"
                  }
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("Unsupported relation"));
        verify(boardStorageService, never()).saveRules(anyLong(), any());
    }
}

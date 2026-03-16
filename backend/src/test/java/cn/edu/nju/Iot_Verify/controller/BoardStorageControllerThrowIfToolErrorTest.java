package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.component.aitool.rule.CheckDuplicateRuleTool;
import cn.edu.nju.Iot_Verify.component.aitool.rule.RecommendRelatedDevicesTool;
import cn.edu.nju.Iot_Verify.component.aitool.rule.RecommendRulesTool;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.exception.ForbiddenException;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class BoardStorageControllerThrowIfToolErrorTest {

    @Mock private BoardStorageService boardService;
    @Mock private RecommendRulesTool recommendRulesTool;
    @Mock private RecommendRelatedDevicesTool recommendRelatedDevicesTool;
    @Mock private CheckDuplicateRuleTool checkDuplicateRuleTool;

    private BoardStorageController controller;
    private RuleDto dummyRule;

    @BeforeEach
    void setUp() {
        controller = new BoardStorageController(
                boardService, recommendRulesTool, recommendRelatedDevicesTool,
                checkDuplicateRuleTool, new ObjectMapper());
        dummyRule = new RuleDto();
        dummyRule.setConditions(List.of());
        dummyRule.setCommand(new RuleDto.Command("dev", "on", null, null));
    }

    private void stubToolError(int status, String errorCode) throws Exception {
        String json = String.format(
                "{\"error\":\"test msg\",\"errorCode\":\"%s\",\"status\":%d}",
                errorCode, status);
        when(checkDuplicateRuleTool.execute(anyString())).thenReturn(json);
    }

    @Test
    void throwIfToolError_400_throwsBadRequest() throws Exception {
        stubToolError(400, "VALIDATION_ERROR");
        assertThrows(BadRequestException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_401_throwsUnauthorized() throws Exception {
        stubToolError(401, "UNAUTHORIZED");
        assertThrows(UnauthorizedException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_404_throwsNotFound() throws Exception {
        stubToolError(404, "NOT_FOUND");
        assertThrows(ResourceNotFoundException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_503_throwsServiceUnavailable() throws Exception {
        stubToolError(503, "SERVICE_UNAVAILABLE");
        assertThrows(ServiceUnavailableException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_500_throwsInternalServer() throws Exception {
        stubToolError(500, "INTERNAL_ERROR");
        assertThrows(InternalServerException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_403_throwsForbidden() throws Exception {
        stubToolError(403, "FORBIDDEN");
        assertThrows(ForbiddenException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_409_throwsConflict() throws Exception {
        stubToolError(409, "CONFLICT");
        assertThrows(ConflictException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_422_throwsValidation() throws Exception {
        stubToolError(422, "VALIDATION_ERROR");
        assertThrows(ValidationException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_noErrorCode_returnsSuccess() throws Exception {
        when(checkDuplicateRuleTool.execute(anyString()))
                .thenReturn("{\"isDuplicate\":false}");
        assertDoesNotThrow(() -> controller.checkDuplicateRule(1L, dummyRule));
    }
}

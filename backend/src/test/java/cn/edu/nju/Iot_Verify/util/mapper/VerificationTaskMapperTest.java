package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import org.junit.jupiter.api.Test;

import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.assertEquals;

class VerificationTaskMapperTest {

    private final VerificationTaskMapper mapper = new VerificationTaskMapper();

    @Test
    void mapsStructuredSpecResultsAndLogs() {
        VerificationTaskPo po = VerificationTaskPo.builder()
                .id(7L)
                .userId(1L)
                .status(VerificationTaskPo.TaskStatus.COMPLETED)
                .createdAt(LocalDateTime.now())
                .isSafe(false)
                .specResultsJson("[{\"specId\":\"s1\",\"passed\":true,\"expression\":\"CTLSPEC AG(light.on)\"}]")
                .checkLogsJson("[\"generated\",\"checked\"]")
                .nusmvOutput("raw output")
                .build();

        VerificationTaskDto dto = mapper.toDto(po);

        assertEquals(1, dto.getSpecResults().size());
        assertEquals("s1", dto.getSpecResults().get(0).getSpecId());
        assertEquals(true, dto.getSpecResults().get(0).isPassed());
        assertEquals("CTLSPEC AG(light.on)", dto.getSpecResults().get(0).getExpression());
        assertEquals(java.util.List.of("generated", "checked"), dto.getCheckLogs());
        assertEquals("raw output", dto.getNusmvOutput());
    }

    @Test
    void mapsLegacyBooleanSpecResults() {
        VerificationTaskPo po = VerificationTaskPo.builder()
                .id(8L)
                .userId(1L)
                .status(VerificationTaskPo.TaskStatus.COMPLETED)
                .createdAt(LocalDateTime.now())
                .isSafe(false)
                .specResultsJson("[true,false]")
                .build();

        VerificationTaskDto dto = mapper.toDto(po);

        assertEquals(2, dto.getSpecResults().size());
        assertEquals("legacy-1", dto.getSpecResults().get(0).getSpecId());
        assertEquals(true, dto.getSpecResults().get(0).isPassed());
        assertEquals("legacy-2", dto.getSpecResults().get(1).getSpecId());
        assertEquals(false, dto.getSpecResults().get(1).isPassed());
    }
}

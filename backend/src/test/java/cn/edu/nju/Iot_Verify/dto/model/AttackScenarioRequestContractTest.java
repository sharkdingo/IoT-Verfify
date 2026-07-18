package cn.edu.nju.Iot_Verify.dto.model;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

class AttackScenarioRequestContractTest {

    private final ObjectMapper objectMapper = new ObjectMapper().findAndRegisterModules();

    @Test
    void verificationSerializesStructuredScenarioWithoutLegacyTopLevelFields() throws Exception {
        VerificationRequestDto request = new VerificationRequestDto();
        request.setAttackScenario(AttackScenarioDto.exactPoints(List.of(
                AttackPointDto.device("light_1"))));

        JsonNode json = objectMapper.readTree(objectMapper.writeValueAsString(request));

        assertEquals("EXACT_POINTS", json.path("attackScenario").path("mode").asText());
        assertEquals("light_1",
                json.path("attackScenario").path("points").get(0).path("deviceId").asText());
        assertFalse(json.has("isAttack"));
        assertFalse(json.has("attackBudget"));
    }

    @Test
    void legacyVerificationFieldsRemainReadableAsExhaustiveSelection() throws Exception {
        VerificationRequestDto request = objectMapper.readValue(
                "{\"isAttack\":true,\"attackBudget\":3}", VerificationRequestDto.class);

        assertEquals(AttackScenarioDto.Mode.ANY_UP_TO_BUDGET,
                request.resolvedAttackScenario().getMode());
        assertEquals(3, request.resolvedAttackScenario().effectiveBudget());
    }

    @Test
    void directLegacySettersPreserveBudgetRegardlessOfCallOrder() {
        SimulationRequestDto request = new SimulationRequestDto();
        request.setAttackBudget(4);
        request.setAttack(true);

        assertEquals(AttackScenarioDto.Mode.ANY_UP_TO_BUDGET,
                request.resolvedAttackScenario().getMode());
        assertEquals(4, request.getAttackBudget());
    }
}

package cn.edu.nju.Iot_Verify.dto.model;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.exc.UnrecognizedPropertyException;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;

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
    void obsoleteTopLevelAttackFieldsAreRejected() {
        assertThrows(UnrecognizedPropertyException.class, () -> objectMapper.readValue(
                "{\"isAttack\":true,\"attackBudget\":3}", VerificationRequestDto.class));
    }

    @Test
    void simulationUsesOnlyTheStructuredAttackScenario() {
        SimulationRequestDto request = new SimulationRequestDto();
        request.setAttackScenario(AttackScenarioDto.anyUpToBudget(4));

        assertEquals(AttackScenarioDto.Mode.ANY_UP_TO_BUDGET,
                request.resolvedAttackScenario().getMode());
        assertEquals(4, request.getAttackBudget());
    }

    @Test
    void missingStructuredScenarioIsNotSilentlyReplacedWithNone() {
        assertThrows(NullPointerException.class,
                () -> new VerificationRequestDto().resolvedAttackScenario());
        assertThrows(NullPointerException.class,
                () -> new SimulationRequestDto().resolvedAttackScenario());
    }
}

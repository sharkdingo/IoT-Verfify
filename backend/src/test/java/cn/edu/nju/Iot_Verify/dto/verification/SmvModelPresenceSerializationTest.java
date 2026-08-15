package cn.edu.nju.Iot_Verify.dto.verification;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationResultDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every DTO a client can offer an SMV download from must serialize {@code hasSmvModel}, and must never
 * serialize the model itself.
 *
 * <p>This is the contract whose absence made the feature unreachable. Four download buttons were each
 * gated on {@code hasSmvModel}, and the responses behind them did not carry it —
 * {@code SimulationResultDto} had no such property at all — so every gate read {@code undefined}, no
 * button rendered, and nothing errored. A missing boolean is invisible: it looks exactly like a feature
 * that was never built.
 *
 * <p>Asserted over real serialization rather than by calling the getters, because the failure mode was
 * about the JSON a client receives. The negative half matters just as much: the model runs to tens of
 * thousands of characters, and shipping it inline would bloat every history response.
 */
class SmvModelPresenceSerializationTest {

    private final ObjectMapper objectMapper = new ObjectMapper();

    private JsonNode serialize(Object dto) throws Exception {
        return objectMapper.readTree(objectMapper.writeValueAsString(dto));
    }

    @Test
    void verificationResultReportsModelPresenceWithoutTheModel() throws Exception {
        // Builder-only: this DTO declares no @NoArgsConstructor, unlike its simulation counterpart.
        JsonNode json = serialize(VerificationResultDto.builder()
                .smvModelContent("MODULE main\nVAR x: boolean;\n")
                .build());
        assertTrue(json.hasNonNull("hasSmvModel"), "clients gate the download on this field");
        assertTrue(json.get("hasSmvModel").asBoolean());
        assertFalse(json.has("smvModelContent"), "the model is fetched through its own endpoint");
    }

    @Test
    void verificationResultReportsAbsentModelAsFalse() throws Exception {
        // Blank, not just null: a run whose model failed to capture stores an empty string, and a
        // client cannot distinguish "" from a real model without this being resolved server-side.
        assertFalse(serialize(VerificationResultDto.builder().smvModelContent("   ").build())
                .get("hasSmvModel").asBoolean());
        assertFalse(serialize(VerificationResultDto.builder().build())
                .get("hasSmvModel").asBoolean(), "a null model is absent, not an error");
    }

    /**
     * The simulation counterpart, which is the one that was missing entirely.
     *
     * <p>The UI gated its download on {@code hasSmvModel} while the response had no such property, so
     * the simulation result dialog could never offer the file it had just generated.
     */
    @Test
    void simulationResultReportsModelPresenceWithoutTheModel() throws Exception {
        SimulationResultDto withModel = new SimulationResultDto();
        withModel.setSmvModelContent("MODULE main\nVAR y: boolean;\n");

        JsonNode json = serialize(withModel);
        assertTrue(json.hasNonNull("hasSmvModel"),
                "SimulationResultDto had no such property, which disabled the whole control");
        assertTrue(json.get("hasSmvModel").asBoolean());
        assertFalse(json.has("smvModelContent"));

        assertFalse(serialize(new SimulationResultDto()).get("hasSmvModel").asBoolean());
    }

    /**
     * A saved simulation trajectory reports presence, because the trajectory *is* its own run and its
     * own download is keyed on this id.
     */
    @Test
    void simulationTraceReportsModelPresenceWithoutTheModel() throws Exception {
        SimulationTraceDto trajectory = new SimulationTraceDto();
        trajectory.setSmvModelContent("MODULE main\n");

        JsonNode json = serialize(trajectory);
        assertTrue(json.get("hasSmvModel").asBoolean());
        assertFalse(json.has("smvModelContent"));
    }

    /**
     * A verification counterexample reports neither — the asymmetry with simulation above is the point.
     *
     * <p>A verification run owns many counterexamples and one model, so the model is addressed by run.
     * `TraceDto` carried both a copy of the model and a presence flag to serve a trace-keyed endpoint;
     * all three are gone. A future reader adding "just the flag, for symmetry with SimulationTraceDto"
     * would be reintroducing the level confusion this removal fixed.
     */
    @Test
    void verificationTraceReportsNoModelAtAll() throws Exception {
        JsonNode json = serialize(new TraceDto());

        assertFalse(json.has("hasSmvModel"),
                "a counterexample is not the level the model is addressed at");
        assertFalse(json.has("smvModelContent"));
    }
}

package cn.edu.nju.Iot_Verify.component.fuzz.paper;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Paper-level properties of the HAFuzz seed-distance metric (Algorithm 1), as distinct from the
 * internal-consistency checks in {@link PaperMonitorFsmTest}.
 *
 * <p>Line 25 prints the per-level weight as {@code 2^(l_up-l) / 2^(l_up-1)}. Those weights sum to
 * 1.75 at {@code l_up = 3} rather than to 1, which lets {@code Dist_cond} exceed the integer
 * {@code Dist_graph} and drives the returned {@code Dist_graph - Dist_cond} negative.
 * {@code SeedSelection} (line 10) keeps the seed with the <em>minimum</em> distance, so a negative
 * score inverts the ranking: a seed merely close to satisfying its conditions would outrank one
 * already at the violation state. We therefore normalize with {@code 2^l_up - 1}.
 *
 * <p>These tests pin the consequence, not the arithmetic — they would fail for any denominator that
 * lets the weights sum above 1.
 */
class PaperDistanceMetricPropertyTest {

    private static final double EPSILON = 1.0e-9;

    private static PaperAtom atom(String key) {
        cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto condition =
                new cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto();
        condition.setDeviceId("device_1");
        condition.setTargetType("variable");
        condition.setKey(key);
        condition.setRelation("=");
        condition.setValue("TRUE");
        return PaperAtom.from(condition);
    }

    /** Two states: start, then the violation. One transition, guarded by a single atom. */
    private PaperMonitorFsm oneStepMonitor(PaperAtom guard) {
        return PaperMonitorFsm.builder("start")
                .state("start", PaperTruthValue.INCONCLUSIVE)
                .state("violation", PaperTruthValue.FALSE)
                .transition("start", "violation", PaperCondition.atom(guard))
                .transition("violation", "violation", PaperCondition.TRUE)
                .build();
    }

    @Test
    void aFullySatisfiedConditionChainNeverProducesANegativeDistance() {
        PaperAtom guard = atom("guard");
        PaperMonitorFsm monitor = oneStepMonitor(guard);
        // Every level resolves to a condition that is fully satisfied — the maximum possible
        // Dist_cond. With the printed denominator this sums to 1.75 and the score goes to -0.75.
        PaperAtomValuation allTrue = atom -> true;

        for (int solverLevels = 1; solverLevels <= 3; solverLevels++) {
            PaperMonitorFsm.Distance distance = monitor.distanceToViolation(
                    allTrue,
                    (condition, level) -> PaperCondition.atom(guard),
                    solverLevels).orElseThrow();

            assertEquals(1, distance.graphDistance());
            assertEquals(1.0, distance.weightedConditionSatisfaction(), EPSILON,
                    "fully satisfied conditions must weigh exactly 1, not more");
            assertTrue(distance.combinedDistance() >= 0.0,
                    "combined distance went negative at solverLevels=" + solverLevels
                            + ": " + distance.combinedDistance());
            assertEquals(0.0, distance.combinedDistance(), EPSILON);
        }
    }

    @Test
    void aSeedAtTheViolationStateOutranksOneMerelyCloseToIt() {
        // The ordering SeedSelection depends on: nothing may score below a state that has already
        // reached the violation, whose distance is 0.
        PaperAtom guard = atom("guard");
        PaperMonitorFsm atViolation = oneStepMonitor(guard);
        atViolation.step(atom -> true);
        assertEquals(PaperTruthValue.FALSE, atViolation.currentTruthValue());
        double reached = atViolation.distanceToViolation(
                atom -> true, PaperPredecessorResolver.none(), 3).orElseThrow().combinedDistance();

        double oneStepAway = oneStepMonitor(guard).distanceToViolation(
                atom -> true,
                (condition, level) -> PaperCondition.atom(guard),
                3).orElseThrow().combinedDistance();

        assertEquals(0.0, reached, EPSILON);
        assertTrue(oneStepAway >= reached,
                "a seed one transition away scored " + oneStepAway
                        + ", below the " + reached + " of a seed already at the violation");
    }
}

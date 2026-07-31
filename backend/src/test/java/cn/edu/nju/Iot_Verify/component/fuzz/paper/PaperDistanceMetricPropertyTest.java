package cn.edu.nju.Iot_Verify.component.fuzz.paper;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Paper-level properties of the HAFuzz seed-distance metric (Algorithm 1), as distinct from the
 * internal-consistency checks in {@link PaperMonitorFsmTest}.
 *
 * <p>Line 25 defines the per-level weight as {@code 2^(l_up-l) / (2^l_up-1)}. The denominator is
 * the sum of all powers used by the configured predecessor levels, so fully satisfied conditions
 * contribute exactly one to {@code Dist_cond}. {@code SeedSelection} (line 10) keeps the seed with
 * the <em>minimum</em> distance, making this normalization part of the search ordering rather than a
 * presentation detail.
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
        // Dist_cond. The Algorithm 1 weights must sum to exactly one.
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

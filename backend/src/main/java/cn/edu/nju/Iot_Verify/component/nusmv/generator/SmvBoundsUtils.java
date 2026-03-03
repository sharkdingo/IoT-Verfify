package cn.edu.nju.Iot_Verify.component.nusmv.generator;

/**
 * Shared numeric-bound utilities for SMV generation.
 * Used by SmvMainModuleBuilder and SmvDeviceModuleBuilder.
 */
public final class SmvBoundsUtils {

    private SmvBoundsUtils() {
    }

    /**
     * Compute the effective upper bound for a numeric variable.
     * In attack mode the declared upper bound is expanded proportionally
     * to {@code intensity}: intensity=0 → no expansion, intensity=50 → range/5.
     * Negative intensity is clamped to 0 defensively (callers should pre-validate).
     */
    public static int resolveEffectiveUpperBound(int lower, int upper, boolean isAttack, int intensity) {
        if (!isAttack) {
            return upper;
        }
        int safeIntensity = Math.max(0, intensity);
        int range = upper - lower;
        int expansion = (int) (range / 5.0 * safeIntensity / 50.0);
        return upper + expansion;
    }
}

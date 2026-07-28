package cn.edu.nju.Iot_Verify.util;

/**
 * The one definition of "re-arm the interrupt flag if this exception was an interruption".
 *
 * <p>A broad {@code catch (Exception)} consumes the {@code InterruptedException} thrown by
 * {@code Semaphore.tryAcquire} and similar waits, and throwing it also *clears* the flag — so a
 * cancelled operation would keep launching work whose result nobody can receive. Call this from any
 * catch broad enough to capture an interruption.
 *
 * <p>Re-arming is safe against affecting an unrelated later request:
 * {@code ThreadPoolExecutor.runWorker} clears a worker's interrupt status before each task (pinned by
 * {@code ThreadConfigTest}), so the flag cannot outlive the task that set it. It does affect the rest
 * of the current task, which is the point.
 *
 * <p>Lives here rather than in the fixer package because the chat tool loop needs the same idiom;
 * two copies is how one of them ends up forgetting the case.
 */
public final class InterruptPreservation {

    private InterruptPreservation() {
    }

    /** Re-arms {@link Thread#interrupt()} when {@code e} is, or wraps, an {@link InterruptedException}. */
    public static void preserveInterrupt(Throwable e) {
        if (e instanceof InterruptedException
                || (e != null && e.getCause() instanceof InterruptedException)) {
            Thread.currentThread().interrupt();
        }
    }
}

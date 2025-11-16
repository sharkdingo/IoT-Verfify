export function runWithTimeout(
    task: () => Promise<void>,
    timeout: number,
    timeoutError = new Error(`Task timed out after ${timeout}ms`)
): Promise<void> {
    let timeoutId: ReturnType<typeof setTimeout>;

    const timeoutPromise = new Promise<never>((_, reject) => {
        timeoutId = setTimeout(() => reject(timeoutError), timeout);
    });

    return Promise.race([
        task().finally(() => clearTimeout(timeoutId)),
        timeoutPromise
    ]);
}
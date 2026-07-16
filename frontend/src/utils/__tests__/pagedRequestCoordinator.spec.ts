import { describe, expect, it } from 'vitest'
import { createPagedRequestCoordinator } from '../pagedRequestCoordinator'

const deferred = <T>() => {
  let resolve!: (value: T | PromiseLike<T>) => void
  let reject!: (reason?: unknown) => void
  const promise = new Promise<T>((resolvePromise, rejectPromise) => {
    resolve = resolvePromise
    reject = rejectPromise
  })
  return { promise, resolve, reject }
}

describe('paged request coordinator', () => {
  it('allows only the newest replacement response to update state', () => {
    const coordinator = createPagedRequestCoordinator()
    const older = coordinator.beginReplace()
    const newer = coordinator.beginReplace()

    expect(coordinator.isCurrent(older)).toBe(false)
    expect(coordinator.isCurrent(newer)).toBe(true)

    coordinator.finish(older)
    expect(coordinator.isCurrent(newer)).toBe(true)
    coordinator.finish(newer)
    expect(coordinator.isCurrent(newer)).toBe(false)
  })

  it('keeps append single-flight and prevents it from crossing a replacement boundary', () => {
    const coordinator = createPagedRequestCoordinator()
    const append = coordinator.beginAppend()

    expect(append).not.toBeNull()
    expect(coordinator.beginAppend()).toBeNull()

    const replacement = coordinator.beginReplace()
    expect(coordinator.isCurrent(append!)).toBe(false)
    expect(coordinator.beginAppend()).toBeNull()

    coordinator.finish(append!)
    expect(coordinator.beginAppend()).toBeNull()

    coordinator.finish(replacement)
    const nextAppend = coordinator.beginAppend()
    expect(nextAppend).not.toBeNull()
    expect(coordinator.isCurrent(nextAppend!)).toBe(true)
  })

  it('invalidates in-flight responses without releasing an active append early', () => {
    const coordinator = createPagedRequestCoordinator()
    const append = coordinator.beginAppend()

    coordinator.invalidate()

    expect(coordinator.isCurrent(append!)).toBe(false)
    expect(coordinator.beginAppend()).toBeNull()

    coordinator.finish(append!)
    const nextAppend = coordinator.beginAppend()
    expect(nextAppend).not.toBeNull()
    expect(coordinator.isCurrent(nextAppend!)).toBe(true)
  })

  it('keeps delayed state and loading completion owned by the newest replacement', async () => {
    const coordinator = createPagedRequestCoordinator()
    const older = deferred<string>()
    const newer = deferred<string>()
    let state = 'initial'
    let loading = false
    let loadingEpoch = 0

    const runReplacement = (source: Promise<string>) => {
      const token = coordinator.beginReplace()
      const requestLoadingEpoch = ++loadingEpoch
      loading = true
      return source
        .then(value => {
          if (coordinator.isCurrent(token)) state = value
        })
        .finally(() => {
          if (requestLoadingEpoch === loadingEpoch) loading = false
          coordinator.finish(token)
        })
    }

    const olderRequest = runReplacement(older.promise)
    const newerRequest = runReplacement(newer.promise)

    newer.resolve('newest')
    await newerRequest
    expect(state).toBe('newest')
    expect(loading).toBe(false)

    older.resolve('older')
    await olderRequest
    expect(state).toBe('newest')
    expect(loading).toBe(false)
  })

  it('preserves a local mutation when an invalidated delayed response arrives', async () => {
    const coordinator = createPagedRequestCoordinator()
    const remote = deferred<string>()
    const token = coordinator.beginReplace()
    let state = 'initial'
    const request = remote.promise
      .then(value => {
        if (coordinator.isCurrent(token)) state = value
      })
      .finally(() => coordinator.finish(token))

    coordinator.invalidate()
    state = 'local mutation'
    remote.resolve('stale remote value')
    await request

    expect(state).toBe('local mutation')
  })
})

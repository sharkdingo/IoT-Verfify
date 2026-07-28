/**
 * Roving-tabindex keyboard behaviour for a `role="tablist"`, shared by the board's two
 * side panels so their tab strips stay consistent (ArrowLeft/Right, Home, End).
 *
 * The caller owns selection state and DOM ids; this composable only answers
 * "which tab should become active for this key?" and moves focus there.
 */
export const useRovingTablist = <Id extends string>(options: {
  tabIds: () => readonly Id[]
  select: (id: Id) => void
  /** DOM id of the button rendering `id`, used to move focus after selection. */
  tabElementId: (id: Id) => string
}) => {
  const handleTablistKeydown = (event: KeyboardEvent, currentId: Id) => {
    const ids = options.tabIds()
    const currentIndex = ids.indexOf(currentId)
    if (currentIndex < 0 || ids.length === 0) return

    let nextIndex: number | null = null
    if (event.key === 'ArrowRight') nextIndex = (currentIndex + 1) % ids.length
    if (event.key === 'ArrowLeft') nextIndex = (currentIndex - 1 + ids.length) % ids.length
    if (event.key === 'Home') nextIndex = 0
    if (event.key === 'End') nextIndex = ids.length - 1
    if (nextIndex === null) return

    const nextId = ids[nextIndex]
    if (nextId === undefined) return

    event.preventDefault()
    options.select(nextId)
    const tablist = (event.currentTarget as HTMLElement | null)?.closest('[role="tablist"]')
    tablist?.querySelector<HTMLElement>(`#${options.tabElementId(nextId)}`)?.focus()
  }

  return { handleTablistKeydown }
}

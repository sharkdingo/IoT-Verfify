import { nextTick, onBeforeUnmount, ref, watch, type Ref } from 'vue'

const FOCUSABLE_SELECTOR = [
  'a[href]',
  'button:not([disabled])',
  'textarea:not([disabled])',
  'input:not([disabled])',
  'select:not([disabled])',
  'summary',
  '[tabindex]:not([tabindex="-1"])'
].join(',')

const isActuallyFocusable = (element: HTMLElement): boolean => {
  if (element.matches(':disabled') || element.tabIndex < 0) return false
  if (element.closest('[hidden], [inert], [aria-hidden="true"]')) return false

  const closedDetails = element.closest('details:not([open])')
  if (closedDetails) {
    const summary = Array.from(closedDetails.children)
      .find(child => child.tagName === 'SUMMARY')
    if (!summary?.contains(element)) return false
  }

  const style = getComputedStyle(element)
  const layoutBoxesAvailable = document.documentElement.getClientRects().length > 0
  return (!layoutBoxesAvailable || element.getClientRects().length > 0)
    && style.display !== 'none'
    && style.visibility !== 'hidden'
    && style.visibility !== 'collapse'
}

export const useModalAccessibility = (
  isOpen: Ref<boolean>,
  close: () => void,
  fallbackFocus?: () => HTMLElement | null,
  options: { trapFocus?: boolean; shouldRestoreFocus?: () => boolean } = {}
) => {
  const dialogRef = ref<HTMLElement | null>(null)
  let previousActiveElement: HTMLElement | null = null

  const getFocusableElements = () => {
    const dialog = dialogRef.value
    if (!dialog) return []
    return Array.from(dialog.querySelectorAll<HTMLElement>(FOCUSABLE_SELECTOR))
      .filter(isActuallyFocusable)
  }

  const setDialogRef = (element: unknown) => {
    dialogRef.value = element instanceof HTMLElement ? element : null
  }

  const focusInitialElement = () => {
    const dialog = dialogRef.value
    if (!dialog) return
    const [firstFocusable] = getFocusableElements()
    ;(firstFocusable ?? dialog).focus()
  }

  const restoreFocus = () => {
    if (!previousActiveElement) return
    if (options.shouldRestoreFocus?.() === false) {
      previousActiveElement = null
      return
    }
    const focusIfAvailable = (target: HTMLElement | null | undefined) => {
      if (!target
        || target === document.body
        || !document.contains(target)
        || !isActuallyFocusable(target)) return false
      target.focus()
      return document.activeElement === target
    }
    if (!focusIfAvailable(previousActiveElement)) {
      focusIfAvailable(fallbackFocus?.())
    }
    previousActiveElement = null
  }

  const handleModalKeydown = (event: KeyboardEvent) => {
    if (!isOpen.value) return

    if (event.key === 'Escape') {
      event.preventDefault()
      close()
      return
    }

    if (event.key !== 'Tab' || options.trapFocus === false) return

    const focusableElements = getFocusableElements()
    if (focusableElements.length === 0) {
      event.preventDefault()
      dialogRef.value?.focus()
      return
    }

    const firstElement = focusableElements[0]
    const lastElement = focusableElements[focusableElements.length - 1]
    const activeElement = document.activeElement as HTMLElement | null
    const activeInsideDialog = !!activeElement && !!dialogRef.value?.contains(activeElement)

    if (event.shiftKey && (!activeInsideDialog || activeElement === firstElement)) {
      event.preventDefault()
      lastElement.focus()
      return
    }

    if (!event.shiftKey && activeElement === lastElement) {
      event.preventDefault()
      firstElement.focus()
    }
  }

  watch(isOpen, open => {
    if (open) {
      previousActiveElement = document.activeElement as HTMLElement | null
      void nextTick(focusInitialElement)
    } else {
      restoreFocus()
    }
  }, { flush: 'post', immediate: true })

  onBeforeUnmount(restoreFocus)

  return {
    setDialogRef,
    handleModalKeydown
  }
}

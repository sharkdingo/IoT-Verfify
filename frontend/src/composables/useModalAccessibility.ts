import { nextTick, onBeforeUnmount, ref, watch, type Ref } from 'vue'

const FOCUSABLE_SELECTOR = [
  'a[href]',
  'button:not([disabled])',
  'textarea:not([disabled])',
  'input:not([disabled])',
  'select:not([disabled])',
  '[tabindex]:not([tabindex="-1"])'
].join(',')

export const useModalAccessibility = (
  isOpen: Ref<boolean>,
  close: () => void,
  fallbackFocus?: () => HTMLElement | null
) => {
  const dialogRef = ref<HTMLElement | null>(null)
  let previousActiveElement: HTMLElement | null = null

  const getFocusableElements = () => {
    const dialog = dialogRef.value
    if (!dialog) return []
    return Array.from(dialog.querySelectorAll<HTMLElement>(FOCUSABLE_SELECTOR))
      .filter(element => !element.hasAttribute('disabled') && !element.getAttribute('aria-hidden'))
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
    const previousCanReceiveFocus = previousActiveElement
      && previousActiveElement !== document.body
      && document.contains(previousActiveElement)
    const target = previousCanReceiveFocus ? previousActiveElement : fallbackFocus?.()
    target?.focus()
    previousActiveElement = null
  }

  const handleModalKeydown = (event: KeyboardEvent) => {
    if (!isOpen.value) return

    if (event.key === 'Escape') {
      event.preventDefault()
      close()
      return
    }

    if (event.key !== 'Tab') return

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

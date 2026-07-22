type MarkdownProperties = Record<string, unknown>

export interface MarkdownNode {
  type: string
  tagName?: string
  properties?: MarkdownProperties
  children?: MarkdownNode[]
  value?: string
}

const SAFE_LINK_PROTOCOLS = new Set(['http:', 'https:', 'mailto:', 'tel:'])
const SAFE_DATA_IMAGE = /^data:image\/(png|jpe?g|gif|webp)(;[^,]+)?,/i

const stringProperty = (value: unknown): string => typeof value === 'string' ? value.trim() : ''

const isRelativeUrl = (value: string): boolean => {
  if (value.startsWith('//') || value.includes('\\')) return false
  if (value.startsWith('#') || value.startsWith('?') || value.startsWith('/')) return true
  return !/^[a-z][a-z\d+.-]*:/i.test(value)
}

const safeLinkTarget = (value: string): { safe: boolean; external: boolean } => {
  if (!value || /[\u0000-\u001f\u007f]/.test(value)) return { safe: false, external: false }
  if (isRelativeUrl(value)) return { safe: true, external: false }

  try {
    const parsed = new URL(value)
    return {
      safe: SAFE_LINK_PROTOCOLS.has(parsed.protocol),
      external: parsed.protocol === 'http:' || parsed.protocol === 'https:'
    }
  } catch {
    return { safe: false, external: false }
  }
}

const isSafeImageSource = (value: string): boolean =>
  Boolean(value)
  && !/[\u0000-\u001f\u007f]/.test(value)
  && (isRelativeUrl(value) || SAFE_DATA_IMAGE.test(value))

const removeEventProperties = (properties: MarkdownProperties): void => {
  for (const key of Object.keys(properties)) {
    if (/^on/i.test(key)) delete properties[key]
  }
}

const sanitizeNode = (node: MarkdownNode): void => {
  const properties = node.type === 'element' ? (node.properties ?? {}) : undefined
  if (properties) {
    node.properties = properties
    removeEventProperties(properties)
  }

  if (properties && node.tagName === 'a') {
    const href = stringProperty(properties.href)
    const target = safeLinkTarget(href)
    if (!target.safe) {
      delete properties.href
      delete properties.target
      properties.ariaDisabled = 'true'
    } else if (target.external) {
      properties.target = '_blank'
      properties.rel = ['noopener', 'noreferrer', 'nofollow']
      properties.referrerPolicy = 'no-referrer'
    }
  }

  if (properties && node.tagName === 'img') {
    const src = stringProperty(properties.src)
    if (!isSafeImageSource(src)) {
      const alt = stringProperty(properties.alt)
      node.tagName = 'span'
      node.properties = { className: ['markdown-image-alt'] }
      node.children = alt ? [{ type: 'text', value: alt }] : []
    } else {
      properties.loading = 'lazy'
      properties.decoding = 'async'
      properties.referrerPolicy = 'no-referrer'
    }
  }

  node.children?.forEach(sanitizeNode)
}

export const sanitizeMarkdownTree = (tree: MarkdownNode): void => sanitizeNode(tree)

export const safeMarkdownPlugin = () => (tree: MarkdownNode): void => sanitizeMarkdownTree(tree)

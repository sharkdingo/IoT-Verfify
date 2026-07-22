import { describe, expect, it } from 'vitest'

import { sanitizeMarkdownTree, type MarkdownNode } from '@/utils/safeMarkdown'

const element = (tagName: string, properties: Record<string, unknown> = {}): MarkdownNode => ({
  type: 'element',
  tagName,
  properties,
  children: []
})

describe('safeMarkdown', () => {
  it('removes executable link protocols and event properties', () => {
    const link = element('a', {
      href: 'javascript:alert(document.domain)',
      onClick: 'alert(1)'
    })

    sanitizeMarkdownTree(link)

    expect(link.properties).not.toHaveProperty('href')
    expect(link.properties).not.toHaveProperty('onClick')
    expect(link.properties).toMatchObject({ ariaDisabled: 'true' })
  })

  it('hardens external links while preserving relative links', () => {
    const external = element('a', { href: 'https://example.com/docs' })
    const relative = element('a', { href: '/docs/start' })
    const bareRelative = element('a', { href: 'guides/start.html' })

    sanitizeMarkdownTree(external)
    sanitizeMarkdownTree(relative)
    sanitizeMarkdownTree(bareRelative)

    expect(external.properties).toMatchObject({
      href: 'https://example.com/docs',
      target: '_blank',
      rel: ['noopener', 'noreferrer', 'nofollow'],
      referrerPolicy: 'no-referrer'
    })
    expect(relative.properties).toEqual({ href: '/docs/start' })
    expect(bareRelative.properties).toEqual({ href: 'guides/start.html' })
  })

  it('prevents automatic remote-image requests but keeps safe embedded images', () => {
    const remote = element('img', { src: 'https://tracker.example/pixel', alt: 'diagram' })
    const embedded = element('img', { src: 'data:image/png;base64,AA==', alt: 'preview' })

    sanitizeMarkdownTree(remote)
    sanitizeMarkdownTree(embedded)

    expect(remote.tagName).toBe('span')
    expect(remote.properties).toEqual({ className: ['markdown-image-alt'] })
    expect(remote.children).toEqual([{ type: 'text', value: 'diagram' }])
    expect(embedded.properties).toMatchObject({
      src: 'data:image/png;base64,AA==',
      loading: 'lazy',
      decoding: 'async',
      referrerPolicy: 'no-referrer'
    })
  })
})

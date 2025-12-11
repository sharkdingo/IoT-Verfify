// src/utils/ai/stream-renderer.ts
import md from './markdown-it';

/**
 * 核心算法：DOM 差量更新 (Deep Clone & Update)
 * 来源：掘金教程
 */
function deepCloneAndUpdate(oldNode: Node, newNode: Node) {
    // 1. 文本节点：内容不同才更新
    if (oldNode.nodeType === Node.TEXT_NODE && newNode.nodeType === Node.TEXT_NODE) {
        if (oldNode.nodeValue !== newNode.nodeValue) {
            oldNode.nodeValue = newNode.nodeValue;
        }
        return;
    }

    // 2. 元素节点：标签不同，直接替换
    if (oldNode.nodeType === Node.ELEMENT_NODE && newNode.nodeType === Node.ELEMENT_NODE) {
        const oldEl = oldNode as HTMLElement;
        const newEl = newNode as HTMLElement;

        if (oldEl.tagName !== newEl.tagName) {
            oldEl.parentNode?.replaceChild(newEl.cloneNode(true), oldEl);
            return;
        }

        // 3. 更新属性 (Class, Style 等)
        // 注意：教程里有 id 保护，这里我们通用处理
        if (oldEl.className !== newEl.className) {
            oldEl.className = newEl.className;
        }
        // 简单的属性全量比对 (生产环境可优化)
        const newAttrs = newEl.attributes;
        for (let i = 0; i < newAttrs.length; i++) {
            const attr = newAttrs[i];
            if (oldEl.getAttribute(attr.name) !== attr.value) {
                oldEl.setAttribute(attr.name, attr.value);
            }
        }
    }

    // 4. 递归对比子节点
    const oldChildren = Array.from(oldNode.childNodes);
    const newChildren = Array.from(newNode.childNodes);
    const maxLength = Math.max(oldChildren.length, newChildren.length);

    for (let i = 0; i < maxLength; i++) {
        const oldChild = oldChildren[i];
        const newChild = newChildren[i];

        if (!oldChild && newChild) {
            oldNode.appendChild(newChild.cloneNode(true)); // 新增
        } else if (oldChild && !newChild) {
            oldNode.removeChild(oldChild); // 删除
        } else if (oldChild && newChild) {
            deepCloneAndUpdate(oldChild, newChild); // 递归
        }
    }
}

/**
 * 正则预处理：解决流式输出中 Markdown 表格/列表不渲染的顽疾
 */
function preProcessMarkdown(content: string): string {
    if (!content) return '';
    let clean = content;

    // 1. 移除 "正在执行指令..."
    const loadingRegex = /^正在执行指令[.\s\n]*/;
    const match = clean.match(loadingRegex);
    if (match && clean.length > match[0].length) {
        clean = clean.substring(match[0].length);
    }

    // 2. 强制换行修复 (你的数据源最需要这个)
    // 匹配：非换行符 -> 换行 -> 表格竖线 |
    clean = clean.replace(/([^\n])\n(\|)/g, '$1\n\n$2');
    // 匹配：非换行符 -> 换行 -> 列表符 -
    clean = clean.replace(/([^\n])\n(\s*[-*]\s+)/g, '$1\n\n$2');

    return clean;
}

/**
 * 渲染控制器类
 * 负责管理异步队列和 DOM 更新
 */
export class StreamRenderer {
    private el: HTMLElement;
    private queue: string[] = [];
    private isRendering = false;

    constructor(element: HTMLElement) {
        this.el = element;
    }

    /**
     * 外部调用的入口：将新数据加入渲染队列
     */
    public push(fullContent: string) {
        this.queue.push(fullContent);
        if (!this.isRendering) {
            this.isRendering = true;
            this.processQueue();
        }
    }

    private processQueue() {
        if (this.queue.length === 0) {
            this.isRendering = false;
            return;
        }

        // 取出最新的数据 (为了性能，可以直接取最后一个，但这取决于是否增量)
        // 既然我们每次传的是 fullContent，我们可以跳过中间帧，直接渲染最新帧，进一步优化性能
        const content = this.queue.shift();

        if (content !== undefined) {
            this.renderFrame(content);
        }

        // 使用 requestAnimationFrame 或 setTimeout 让出主线程
        setTimeout(() => {
            this.processQueue();
        }, 16); // ~60fps
    }

    private renderFrame(content: string) {
        if (!this.el) return;

        // 1. 预处理 + Markdown 解析
        const fixedContent = preProcessMarkdown(content);
        const html = md.render(fixedContent);

        // 2. 创建 Virtual DOM (Temp Div)
        const tempDiv = document.createElement('div');
        tempDiv.innerHTML = html;

        // 你可以在这里调用 buildCodeBlock(tempDiv) 来添加复制按钮等

        // 3. 差量更新
        deepCloneAndUpdate(this.el, tempDiv);
    }
}
/**
 * 核心函数：对比新旧 DOM 树，只更新变化的部分
 * 避免 innerHTML 导致的重绘闪烁
 */
export function deepCloneAndUpdate(oldNode: Node, newNode: Node) {
    // 1. 文本节点：直接更新内容
    if (oldNode.nodeType === Node.TEXT_NODE && newNode.nodeType === Node.TEXT_NODE) {
        if (oldNode.nodeValue !== newNode.nodeValue) {
            oldNode.nodeValue = newNode.nodeValue;
        }
        return;
    }

    // 2. 元素节点标签不同：直接替换整个节点
    if (oldNode.nodeType === Node.ELEMENT_NODE && newNode.nodeType === Node.ELEMENT_NODE) {
        const oldEl = oldNode as HTMLElement;
        const newEl = newNode as HTMLElement;

        if (oldEl.tagName !== newEl.tagName) {
            oldEl.parentNode?.replaceChild(newEl.cloneNode(true), oldEl);
            return;
        }

        // 3. 更新属性 (Class, Style, etc.)
        // 忽略特定的容器 ID 保护
        if (oldEl.className !== newEl.className) {
            oldEl.className = newEl.className;
        }

        // 对比并更新 Attribute
        // 简单起见，这里假设新节点包含所有需要的属性。
        // 如果需要更严谨，可以遍历 setAttribute
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
            // 新增节点
            oldNode.appendChild(newChild.cloneNode(true));
        } else if (oldChild && !newChild) {
            // 删除多余节点
            oldNode.removeChild(oldChild);
        } else if (oldChild && newChild) {
            // 递归更新
            deepCloneAndUpdate(oldChild, newChild);
        }
    }
}
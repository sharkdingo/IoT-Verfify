// src/utils/ai/markdown-it.ts
import MarkdownIt from 'markdown-it';
import hljs from 'highlight.js';
import 'highlight.js/styles/atom-one-dark.css';

// 教程中的配置项
const md = new MarkdownIt({
    html: true,          // 允许 HTML 标签
    xhtmlOut: true,      // 使用 / 关闭标签
    breaks: true,        // 转换 \n 为 <br> (注意：表格需要双换行)
    linkify: true,       // 自动识别链接
    typographer: true,   // 排版优化
    quotes: '“”‘’',
});

// 配置高亮 (保留你之前的高亮逻辑，融合教程的 highlight.js)
md.set({
    highlight: function (str, lang) {
        if (lang && hljs.getLanguage(lang)) {
            try {
                return '<pre class="hljs"><code>' +
                    hljs.highlight(str, { language: lang, ignoreIllegals: true }).value +
                    '</code></pre>';
            } catch (__) {}
        }
        return '<pre class="hljs"><code>' + md.utils.escapeHtml(str) + '</code></pre>';
    }
});

export default md;
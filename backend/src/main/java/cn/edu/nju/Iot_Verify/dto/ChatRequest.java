package cn.edu.nju.Iot_Verify.dto;

import java.util.List;

/**
 * 与前端 ai-suspended-ball-chat 约定的请求体结构：
 *
 * {
 *   "appName": "xxx",
 *   "userId": "xxx",
 *   "query": "用户当前的问题",
 *   "isStream": true,
 *   "history": [
 *     { "role": "user", "content": "之前的问题" },
 *     { "role": "assistant", "content": "之前的回答" }
 *   ]
 * }
 */
public class ChatRequest {

    // 组件 <SuspendedBallChat :app-name="appName" ... />
    private String appName;

    // 你可以用 domainName 或者用户唯一 ID
    private String userId;

    // 当前这次用户输入的问题
    private String query;

    // 是否流式（enable-streaming=true 时一般为 true）
    private Boolean isStream;

    // 历史对话
    private List<ChatHistoryItem> history;

    // ---------- getter / setter ----------

    public String getAppName() {
        return appName;
    }

    public void setAppName(String appName) {
        this.appName = appName;
    }

    public String getUserId() {
        return userId;
    }

    public void setUserId(String userId) {
        this.userId = userId;
    }

    public String getQuery() {
        return query;
    }

    public void setQuery(String query) {
        this.query = query;
    }

    public Boolean getIsStream() {
        return isStream;
    }

    public void setIsStream(Boolean isStream) {
        this.isStream = isStream;
    }

    public List<ChatHistoryItem> getHistory() {
        return history;
    }

    public void setHistory(List<ChatHistoryItem> history) {
        this.history = history;
    }

    // ---------- 内部类：历史记录项 ----------

    public static class ChatHistoryItem {
        /**
         * "user" 或 "assistant"
         */
        private String role;

        /**
         * 文本内容
         */
        private String content;

        public String getRole() {
            return role;
        }

        public void setRole(String role) {
            this.role = role;
        }

        public String getContent() {
            return content;
        }

        public void setContent(String content) {
            this.content = content;
        }
    }
}

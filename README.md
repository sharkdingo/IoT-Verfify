# IoT-Verify 项目配置与运行指南

## 📋 目录

- [项目简介](#项目简介)
- [技术栈](#技术栈)
- [环境要求](#环境要求)
- [前置条件](#前置条件)
- [项目结构](#项目结构)
- [配置说明](#配置说明)
  - [后端配置](#后端配置)
  - [前端配置](#前端配置)
- [安装步骤](#安装步骤)
- [运行项目](#运行项目)
- [API 接口](#api-接口)
- [常见问题](#常见问题)

---

## 项目简介

IoT-Verify 是一个物联网设备验证平台，支持用户注册登录、设备模板管理、规格管理、实时聊天等功能。

**核心功能：**
1. **设备管理**：创建设备模板、设备实例，拖拽式布局
2. **规则引擎**：配置设备间数据流向规则（sources → target）
3. **规格管理**：定义 IF-THEN 规则进行形式化验证
4. **AI 助手**：基于火山引擎的智能对话，支持设备操作、NuSMV 验证问答

**AI 助手特点：**
- 自然语言交互：创建设备、查询状态、修改配置
- 流式响应：SSE 实时显示 AI 生成内容
- 工具调用：自动执行设备操作、刷新数据
- 上下文感知：了解当前系统状态，提供智能建议

**特点：**
- 前后端分离架构
- JWT Token 认证
- 火山引擎 AI 模型集成（智能家居问答、设备操作、形式化验证）
- Redis Token 黑名单
- SSE 流式聊天
- 设备规则与边的可视化编辑

---

## 技术栈

### 后端
- **框架**：Spring Boot 3.5.7
- **语言**：Java 17
- **数据库**：MySQL 8.0
- **缓存**：Redis
- **安全**：Spring Security + JWT
- **ORM**：Spring Data JPA
- **AI**：火山引擎 Ark Runtime SDK（流式 SSE 输出）

### 前端
- **框架**：Vue 3 + TypeScript
- **构建工具**：Vite 6
- **UI 组件库**：Ant Design Vue 4 + Element Plus
- **路由**：Vue Router 4
- **HTTP 客户端**：Axios（REST API）+ 原生 fetch（SSE 流式）
- **国际化**：Vue I18n
- **实时通信**：Server-Sent Events (SSE)

---

## 环境要求

| 依赖 | 版本要求 | 说明 |
|------|----------|------|
| JDK | 17+ | 后端运行环境 |
| Node.js | 18+ | 前端运行环境 |
| Maven | 3.6+ | 后端构建工具 |
| MySQL | 8.0+ | 主数据库 |
| Redis | 6.0+ | 缓存与 Token 黑名单 |
| npm / pnpm | 最新版 | 前端包管理 |

---

## 前置条件

### 1. 安装 MySQL 8.0

**Windows (使用 MySQL Installer)：**
1. 下载 MySQL Installer from [mysql.com](https://dev.mysql.com/downloads/installer/)
2. 选择 "Developer Default" 或 "Full" 安装
3. 设置 root 密码（建议：`sharkdingo123` 或自定义）
4. 创建数据库：
   ```sql
   CREATE DATABASE iot_verify CHARACTER SET utf8mb4 COLLATE utf8mb4_unicode_ci;
   ```

**Linux (Ubuntu)：**
```bash
sudo apt update
sudo apt install mysql-server-8.0
sudo mysql
# 在 MySQL 终端中：
CREATE DATABASE iot_verify CHARACTER SET utf8mb4 COLLATE utf8mb4_unicode_ci;
ALTER USER 'root'@'localhost' IDENTIFIED WITH mysql_native_password BY 'your_password';
FLUSH PRIVILEGES;
EXIT;
```

**macOS (使用 Homebrew)：**
```bash
brew install mysql@8.0
brew services start mysql@8.0
mysql -u root -p
# 创建数据库（同上）
```

**验证 MySQL：**
```bash
mysql -u root -p -e "SHOW DATABASES;"
```

### 2. 安装 Redis

**Windows：**
- 下载 [Redis for Windows](https://github.com/microsoftarchive/redis/releases) 或使用 WSL2
- 推荐使用 Docker：
  ```bash
  docker run -d -p 6379:6379 --name redis-server redis:alpine
  ```

**Linux (Ubuntu)：**
```bash
sudo apt install redis-server
sudo systemctl start redis
sudo systemctl enable redis
```

**macOS：**
```bash
brew install redis
brew services start redis
```

**验证 Redis：**
```bash
redis-cli ping
# 应该返回 PONG
```

### 3. 安装 JDK 17

**Windows：**
1. 下载 [OpenJDK 17](https://adoptium.net/temurin/releases/?version=17) 或 [Oracle JDK 17](https://www.oracle.com/java/technologies/downloads/#java17)
2. 安装后配置环境变量：
   ```
   JAVA_HOME = C:\Program Files\Eclipse Adoptium\jdk-17.0.x.x-hotspot
   PATH = %JAVA_HOME%\bin
   ```

**Linux (Ubuntu)：**
```bash
sudo apt install openjdk-17-jdk
java -version
```

**macOS：**
```bash
brew install openjdk@17
echo 'export PATH="/opt/homebrew/opt/openjdk@17/bin:$PATH"' >> ~/.zshrc
```

### 4. 安装 Node.js

**Windows/macOS/Linux：**
1. 下载 [Node.js LTS](https://nodejs.org/) (推荐 20.x)
2. 或使用 nvm：
   ```bash
   # 安装 nvm (Linux/macOS)
   curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.0/install.sh | bash
   source ~/.bashrc  # 或 ~/.zshrc
   nvm install 20
   nvm use 20
   ```

**验证 Node.js：**
```bash
node -v  # 应该显示 v20.x.x
npm -v   # 应该显示 10.x.x
```

### 5. 安装 Maven

**Windows：**
1. 下载 [Maven](https://maven.apache.org/download.cgi)
2. 解压到 `C:\Program Files\Apache\Maven`
3. 配置环境变量：
   ```
   MAVEN_HOME = C:\Program Files\Apache\Maven
   PATH = %MAVEN_HOME%\bin
   ```

**Linux/macOS：**
```bash
# Ubuntu
sudo apt install maven
# macOS
brew install maven
```

**验证 Maven：**
```bash
mvn -version
```

---

## 项目结构

```
IoT-Verify/
├── README.md                    # 本文档
├── backend/                     # 后端 Spring Boot 项目
│   ├── pom.xml                 # Maven 配置
│   └── src/main/
│       ├── java/cn/edu/nju/Iot_Verify/
│       │   ├── api/            # REST API 控制器
│       │   ├── model/          # 数据模型
│       │   ├── service/        # 业务逻辑
│       │   ├── repository/     # 数据访问
│       │   ├── security/       # 安全配置 (JWT, Spring Security)
│       │   └── configure/      # 配置类
│       └── resources/
│           ├── application.yaml # 主配置文件
│           └── application-dev.yaml # 开发环境配置（可选）
├── frontend/                   # 前端 Vue 3 项目
│   ├── package.json           # npm 配置
│   ├── vite.config.ts         # Vite 配置
│   ├── .env                   # 环境变量（敏感配置）
│   └── src/
│       ├── api/               # API 调用层
│       ├── views/             # 页面组件
│       ├── stores/            # 状态管理
│       ├── components/        # 公共组件
│       ├── router/            # 路由配置
│       └── types/             # TypeScript 类型定义
```

---

## 配置说明

### 后端配置

**文件位置：** `backend/src/main/resources/application.yaml`

```yaml
spring:
  application:
    name: iot-verify

  datasource:
    url: jdbc:mysql://localhost:3306/iot_verify?useSSL=false&serverTimezone=Asia/Shanghai&characterEncoding=utf-8&allowPublicKeyRetrieval=true
    username: root
    password: sharkdingo123  # ⚠️ 修改为你的 MySQL 密码
    driver-class-name: com.mysql.cj.jdbc.Driver

  jpa:
    hibernate:
      ddl-auto: update  # 第一次运行用 update，后续可用 validate
    show-sql: false
    properties:
      hibernate:
        dialect: org.hibernate.dialect.MySQL8Dialect
        format_sql: true

server:
  port: 8080
  error:
    include-message: never
    include-binding-errors: never

volcengine:
  ark:
    api-key: your_api_key_here  # ⚠️ 替换为你的火山引擎 API Key
    model-id: ep-20251125202752-bhwbw  # 模型 ID
    base-url: https://ark.cn-beijing.volces.com/api/v3

jwt:
  secret: iot-verify-secret-key-must-be-at-least-256-bits-long-for-hs256  # ⚠️ 修改为更复杂的密钥
  expiration: 86400000  # Token 有效期 (毫秒)，86400000 = 24 小时

spring.data.redis:
    host: localhost
    port: 6379
    password:  # ⚠️ 如果 Redis 有密码，填入此处
    database: 0
```

#### 使用环境变量覆盖配置

后端支持通过环境变量覆盖配置，示例：

```bash
# Linux/macOS
export DB_URL="jdbc:mysql://localhost:3306/iot_verify?useSSL=false&serverTimezone=Asia/Shanghai&characterEncoding=utf-8&allowPublicKeyRetrieval=true"
export DB_USERNAME="root"
export DB_PASSWORD="your_password"
export JWT_SECRET="your-256-bit-secret-key-here"
export JWT_EXPIRATION="86400000"
export REDIS_HOST="localhost"
export REDIS_PORT="6379"
export REDIS_PASSWORD="your_redis_password"
export VOLCENGINE_API_KEY="your_volcengine_api_key"
export VOLCENGINE_MODEL_ID="your_model_id"
export SERVER_PORT="8080"

# Windows (PowerShell)
$env:DB_PASSWORD = "your_password"
$env:JWT_SECRET = "your-256-bit-secret-key-here"
$env:VOLCENGINE_API_KEY = "your_volcengine_api_key"
# ... 其他变量
```

#### 创建生产配置文件（可选）

创建 `backend/src/main/resources/application-prod.yaml`：

```yaml
spring:
  datasource:
    url: jdbc:mysql://your_prod_db_host:3306/iot_verify?useSSL=true&serverTimezone=Asia/Shanghai
    username: ${PROD_DB_USERNAME}
    password: ${PROD_DB_PASSWORD}

spring.data.redis:
    host: ${PROD_REDIS_HOST}
    port: ${PROD_REDIS_PORT}
    password: ${PROD_REDIS_PASSWORD}

jwt:
  secret: ${PROD_JWT_SECRET}
  expiration: ${PROD_JWT_EXPIRATION}

volcengine:
  ark:
    api-key: ${PROD_VOLCENGINE_API_KEY}
```

### 前端配置

**文件位置：** `frontend/.env`

```bash
# API 基础地址（后端服务地址）
VITE_API_BASE_URL=http://localhost:8080
```

#### 使用环境变量

Vite 支持多种环境文件：

| 文件名 | 用途 |
|--------|------|
| `.env` | 所有环境共享的默认值 |
| `.env.local` | 本地覆盖，不提交到版本控制 |
| `.env.development` | 开发环境（`npm run dev` 时加载） |
| `.env.production` | 生产环境（`npm run build` 时加载） |

**示例：创建 `.env.development`**
```bash
# frontend/.env.development
VITE_API_BASE_URL=http://localhost:8080
```

**示例：创建 `.env.production`**
```bash
# frontend/.env.production
VITE_API_BASE_URL=https://your-api-domain.com
```

---

## 安装步骤

### 1. 克隆项目（如果尚未克隆）

```bash
git clone https://your-repo-url/IoT-Verify.git
cd IoT-Verify
```

### 2. 后端安装

```bash
cd backend

# 方式一：使用 Maven Wrapper（推荐，无需安装 Maven）
# Windows
mvnw.cmd install -DskipTests

# Linux/macOS
./mvnw install -DskipTests

# 方式二：使用本地 Maven
mvn install -DskipTests
```

**首次运行会自动：**
- 创建 MySQL 表（JPA `ddl-auto: update`）
- 下载所有依赖

### 3. 前端安装

```bash
cd frontend

# 使用 npm
npm install

# 或使用 pnpm（推荐，更快）
pnpm install

# 或使用 yarn
yarn install
```

---

## 运行项目

### 1. 启动 MySQL 和 Redis

**方式一：手动启动**

```bash
# 启动 MySQL（根据你的安装方式）
# Windows 服务
net start mysql

# 启动 Redis
redis-server
```

**方式二：使用 Docker（推荐）**

```bash
# 启动 MySQL
docker run -d \
  --name mysql-iot-verify \
  -p 3306:3306 \
  -e MYSQL_ROOT_PASSWORD=sharkdingo123 \
  -e MYSQL_DATABASE=iot_verify \
  mysql:8.0 \
  --character-set-server=utf8mb4 \
  --collation-server=utf8mb4_unicode_ci

# 启动 Redis
docker run -d \
  --name redis-iot-verify \
  -p 6379:6379 \
  redis:alpine
```

**停止 Docker 容器：**
```bash
docker stop mysql-iot-verify redis-iot-verify
```

### 2. 启动后端

```bash
cd backend

# 方式一：使用 Maven（推荐）
mvn spring-boot:run

# 方式二：运行打包后的 JAR
java -jar target/Iot-Verify-0.0.1-SNAPSHOT.jar

# 方式三：使用 Maven Wrapper
./mvnw spring-boot:run  # Linux/macOS
mvnw.cmd spring-boot:run  # Windows
```

后端启动成功后会看到：
```
Started Application in X.XXX seconds
```

后端默认运行在：`http://localhost:8080`

### 3. 启动前端

```bash
cd frontend

# 开发模式（热重载）
npm run dev

# 或使用 pnpm
pnpm dev
```

前端开发服务器默认运行在：
- `http://localhost:3000`（或下一个可用端口）
- 打开浏览器访问显示的地址

### 4. 完整启动流程（脚本）

**创建启动脚本 `start.sh` (Linux/macOS)：**

```bash
#!/bin/bash

echo "🚀 启动 IoT-Verify..."

# 检查 MySQL 和 Redis
echo "📦 检查依赖服务..."
if ! command -v mysql &> /dev/null; then
    echo "⚠️  MySQL 未安装，请先安装 MySQL 8.0"
    exit 1
fi

# 启动后端
echo "🔧 启动后端服务..."
cd backend
./mvnw spring-boot:run &
BACKEND_PID=$!

# 等待后端启动
echo "⏳ 等待后端启动..."
sleep 30

# 启动前端
echo "🎨 启动前端服务..."
cd ../frontend
npm run dev &
FRONTEND_PID=$!

echo ""
echo "✅ 服务启动完成！"
echo "   后端: http://localhost:8080"
echo "   前端: http://localhost:3000"
echo ""
echo "按 Ctrl+C 停止所有服务"

# 等待用户中断
trap "kill $BACKEND_PID $FRONTEND_PID; exit" SIGINT SIGTERM
wait
```

**Windows 批处理脚本 `start.bat`：**

```bat
@echo off
echo 🚀 启动 IoT-Verify...

echo 🔧 启动后端服务...
cd /d %~dp0backend
start /B mvn spring-boot:run > backend.log 2>&1

echo ⏳ 等待后端启动...
timeout /t 30 /nobreak >nul

echo 🎨 启动前端服务...
cd /d %~dp0frontend
start /B npm run dev > frontend.log 2>&1

echo.
echo ✅ 服务启动完成！
echo    后端: http://localhost:8080
echo    前端: http://localhost:3000
echo.
echo 按任意键停止服务
pause >nul

taskkill /F /IM java.exe >nul 2>&1
taskkill /F /IM node.exe >nul 2>&1
```

---

## API 接口

### 认证接口

| 方法 | 路径 | 说明 | 需要认证 |
|------|------|------|----------|
| POST | `/api/auth/register` | 用户注册 | 否 |
| POST | `/api/auth/login` | 用户登录 | 否 |
| POST | `/api/auth/logout` | 退出登录 | 是 |

### 设备模板接口

| 方法 | 路径 | 说明 | 需要认证 |
|------|------|------|----------|
| GET | `/api/board/templates` | 获取设备模板列表 | 是 |
| POST | `/api/board/templates` | 创建设备模板 | 是 |
| DELETE | `/api/board/templates/{id}` | 删除设备模板 | 是 |
| POST | `/api/board/templates/reload` | 重载默认模板 | 是 |
| GET | `/api/board/active` | 获取活跃设备 | 是 |
| POST | `/api/board/active` | 保存活跃设备 | 是 |
| GET | `/api/board/edges` | 获取连线列表 | 是 |
| POST | `/api/board/edges` | 保存连线列表 | 是 |

### 规格接口

| 方法 | 路径 | 说明 | 需要认证 |
|------|------|------|----------|
| GET | `/api/board/specs` | 获取规格列表 | 是 |
| POST | `/api/board/specs` | 保存规格（全量替换） | 是 |

### 聊天接口

| 方法 | 路径 | 说明 | 需要认证 |
|------|------|------|----------|
| GET | `/api/chat/sessions` | 获取会话列表 | 是 |
| POST | `/api/chat/sessions` | 创建新会话 | 是 |
| GET | `/api/chat/sessions/{id}/messages` | 获取会话消息历史 | 是 |
| POST | `/api/chat/completions` | 发送消息（SSE 流式） | 是 |
| DELETE | `/api/chat/sessions/{id}` | 删除会话 | 是 |

#### SSE 流式响应格式

`POST /api/chat/completions` 使用 Server-Sent Events (SSE) 进行流式响应：

```json
// 数据块
data: {"content":"AI 响应文本片段"}

data: {"command":{"type":"REFRESH_DATA","payload":{"target":"device_list"}}}

// 结束标记
data: [DONE]
```

**Command 类型：**

| type | payload | 说明 |
|------|---------|------|
| REFRESH_DATA | {"target": "device_list"} | 通知前端刷新数据 |

#### 聊天请求示例

```bash
# 1. 先创建会话
SESSION_ID=$(curl -X POST http://localhost:8080/api/chat/sessions \
  -H "Authorization: Bearer $TOKEN" \
  -s | jq -r '.data.id')

# 2. 发送消息并接收 SSE 流
curl -X POST http://localhost:8080/api/chat/completions \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -H "Accept: text/event-stream" \
  -d "{\"sessionId\":\"$SESSION_ID\",\"content\":\"你好\"}" \
  --stream
```

### 规则与边接口

| 方法 | 路径 | 说明 | 需要认证 |
|------|------|------|----------|
| GET | `/api/board/rules` | 获取规则列表 | 是 |
| POST | `/api/board/rules` | 保存规则（增量更新） | 是 |
| GET | `/api/board/edges` | 获取边列表 | 是 |
| POST | `/api/board/edges` | 保存边列表 | 是 |

**说明：**
- Rule 表示 IFTTT 规则：`conditions[] → command`（条件满足时执行命令）
- Edge 是 Rule 的可视化表示，包含连线端点坐标
- 前端维护 Rule 和 Edge 的同步关系，后端只负责存储

### 验证接口

| 方法 | 路径 | 说明 | 需要认证 |
|------|------|------|----------|
| POST | `/api/verify` | 执行 IoT 系统形式化验证（同步） | 是 |
| POST | `/api/verify/async` | 异步验证，返回 taskId | 是 |
| GET | `/api/verify/tasks/{id}` | 获取验证任务状态 | 是 |
| GET | `/api/verify/tasks/{id}/progress` | 获取验证任务进度 (0-100) | 是 |
| POST | `/api/verify/tasks/{id}/cancel` | 取消验证任务 | 是 |
| GET | `/api/verify/traces` | 获取用户所有验证轨迹 | 是 |
| GET | `/api/verify/traces/{id}` | 获取单个验证轨迹 | 是 |
| DELETE | `/api/verify/traces/{id}` | 删除验证轨迹 | 是 |

### 模拟接口

| 方法 | 路径 | 说明 | 需要认证 |
|------|------|------|----------|
| POST | `/api/simulate` | 随机模拟 N 步（不落库） | 是 |
| POST | `/api/simulate/async` | 异步模拟，返回 taskId | 是 |
| GET | `/api/simulate/tasks/{id}` | 获取模拟任务状态 | 是 |
| GET | `/api/simulate/tasks/{id}/progress` | 获取模拟任务进度 (0-100) | 是 |
| POST | `/api/simulate/tasks/{id}/cancel` | 取消模拟任务 | 是 |
| POST | `/api/simulate/traces` | 执行模拟并持久化 | 是 |
| GET | `/api/simulate/traces` | 获取用户所有模拟记录（摘要） | 是 |
| GET | `/api/simulate/traces/{id}` | 获取单条模拟记录（详情） | 是 |
| DELETE | `/api/simulate/traces/{id}` | 删除模拟记录 | 是 |

#### 验证请求示例

```bash
curl -X POST http://localhost:8080/api/verify \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "devices": [
      {
        "varName": "ac_1",
        "templateName": "AirConditioner",
        "state": "Off",
        "variables": [{"name": "temperature", "value": "24", "trust": "trusted"}],
        "privacies": [{"name": "temperature", "privacy": "private"}]
      }
    ],
    "rules": [
      {
        "conditions": [{"deviceName": "ac_1", "attribute": "temperature", "relation": ">", "value": "28"}],
        "command": {"deviceName": "ac_1", "action": "turnOn"}
      }
    ],
    "specs": [
      {
        "id": "spec_1",
        "templateId": "1",
        "templateLabel": "AG(A)",
        "aConditions": [{"deviceId": "ac_1", "targetType": "state", "key": "state", "relation": "=", "value": "Cooling"}],
        "ifConditions": [],
        "thenConditions": []
      }
    ],
    "isAttack": false,
    "intensity": 3,
    "enablePrivacy": false
  }'
```

#### 验证结果示例

```json
{
  "safe": false,
  "traces": [...],
  "specResults": [false],
  "checkLogs": ["Generating NuSMV model...", "Specification violation detected!"],
  "nusmvOutput": "..."
}
```

**说明：**
- `safe: true` 表示所有规格都满足
- `safe: false` 表示发现违反规格的轨迹
- `traces` 包含违反规格的 counterexample（反例轨迹）
- `checkLogs` 包含验证过程的日志
- `nusmvOutput` 包含原始的 NuSMV 输出

#### NuSMV 规格语法

| 规格类型 | 约束 | NuSMV 语法 |
|---------|------|-----------|
| A | 始终成立 | `CTLSPEC AG(condition)` |
| A | 终将发生 | `CTLSPEC AF(condition)` |
| A | 永不发生 | `CTLSPEC AG !(condition)` |
| B | 同时发生 | `CTLSPEC AG((A) -> AX(B))` |
| B | 随后发生 | `CTLSPEC AG((A) -> AF(B))` |

### 响应格式

所有 API 响应使用统一包装格式：

```json
{
  "code": 200,
  "message": "success",
  "data": { ... }
}
```

**错误码：**
| code | 说明 |
|------|------|
| 200 | 成功 |
| 400 | 请求参数错误 |
| 401 | 未认证或 Token 过期 |
| 403 | 无权限 |
| 404 | 资源不存在 |
| 500 | 服务器内部错误 |

### 请求示例

**登录：**
```bash
curl -X POST http://localhost:8080/api/auth/login \
  -H "Content-Type: application/json" \
  -d '{"phone": "13800138000", "password": "password123"}'
```

---

## 常见问题

### Q1: 后端启动报错 "Connection to MySQL failed"

**错误信息：**
```
Connection to MySQL failed: java.sql.SQLException: Access denied for user 'root'@'localhost'
```

**解决方案：**
1. 确认 MySQL 服务已启动
2. 检查 `application.yaml` 中的用户名和密码
3. 验证 MySQL 用户权限：
   ```sql
   ALTER USER 'root'@'localhost' IDENTIFIED WITH mysql_native_password BY 'your_password';
   FLUSH PRIVILEGES;
   ```

### Q2: 后端启动报错 "Connection to Redis failed"

**错误信息：**
```
Unable to connect to Redis
```

**解决方案：**
1. 确认 Redis 服务已启动：`redis-cli ping`
2. 检查 `application.yaml` 中的 Redis 配置
3. 如果有密码，确保 `redis.password` 配置正确

### Q3: 前端请求报 CORS 错误

**错误信息：**
```
Access to XMLHttpRequest at 'http://localhost:8080/api/auth/login' from origin 'http://localhost:3000' has been blocked by CORS policy
```

**解决方案：**
1. 确认后端 `SecurityConfig.java` 中已配置 CORS
2. 重启后端服务
3. 检查浏览器地址栏端口是否与 CORS 配置一致（3000 或 3001）

### Q4: 登录后 API 请求返回 401

**错误信息：**
```
{"code":401,"message":"Unauthorized"}
```

**解决方案：**
1. 检查请求头是否包含 `Authorization: Bearer token`
2. 确认 Token 未过期
3. 确认 Token 未在 Redis 黑名单中
4. 检查 JWT Secret 是否正确

### Q5: 前端构建失败

**错误信息：**
```
Error: @vitejs/plugin-vue not found
```

**解决方案：**
```bash
# 删除 node_modules 重新安装
cd frontend
rm -rf node_modules package-lock.json
npm install
```

### Q6: 后端构建失败

**错误信息：**
```
Could not resolve dependency
```

**解决方案：**
```bash
# 清除 Maven 本地仓库缓存
cd backend
rm -rf ~/.m2/repository/cn/edu/nju/Iot-Verify
mvn clean install
```

### Q7: 如何修改默认端口

**后端端口：**
修改 `application.yaml`：
```yaml
server:
  port: 8080  # 改为其他端口
```

**前端端口：**
在 `frontend/vite.config.ts` 中配置：
```typescript
import { defineConfig } from 'vite'
import vue from '@vitejs/plugin-vue'

export default defineConfig({
  plugins: [vue()],
  server: {
    port: 3000  // 改为其他端口
  }
})
```

### Q8: 如何在生产环境部署

**后端：**
```bash
cd backend
mvn clean package -DskipTests
java -jar target/Iot-Verify-0.0.1-SNAPSHOT.jar --spring.profiles.active=prod
```

**前端：**
```bash
cd frontend
npm run build
# 将 dist 目录部署到 Nginx 或其他 Web 服务器
```

**Nginx 配置示例：**
```nginx
server {
    listen 80;
    server_name your-domain.com;
    
    # 前端
    location / {
        root /var/www/iot-verify/dist;
        try_files $uri $uri/ /index.html;
    }
    
    # 后端 API
    location /api {
        proxy_pass http://localhost:8080;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
    }
}
```

### Q9: Token 过期时间设置

**临时 Token（开发环境）：**
```yaml
jwt:
  expiration: 86400000  # 24 小时
```

**短时 Token（生产环境，更安全）：**
```yaml
jwt:
  expiration: 3600000  # 1 小时
```

**刷新 Token 机制：**
如果需要更长的会话，可以实现刷新 Token 机制，用户在 Token 即将过期时可以用刷新 Token 换取新的访问 Token。

### Q10: 如何查看后端日志

**实时查看日志：**
```bash
# 开发模式
cd backend
mvn spring-boot:run

# 查看日志文件（如果配置了日志文件）
tail -f logs/application.log
```

**修改日志级别：**
在 `application.yaml` 中：
```yaml
logging:
  level:
    root: INFO
    cn.edu.nju.Iot_Verify: DEBUG
    org.springframework.security: DEBUG
```

### Q11: AI 聊天无响应

**错误信息：**
```
发送消息失败: network error
```

**解决方案：**
1. 确认后端服务正常运行
2. 检查火山引擎 API Key 是否正确配置
3. 确认 Redis 服务正常运行（用于 Token 黑名单）
4. 查看后端日志确认 AI 调用是否成功
5. 检查 SSE 连接是否被 CORS 拦截

### Q12: SSE 流式响应中断

**可能原因：**
1. 网络不稳定导致连接断开
2. 后端 SSE 超时（默认 5 分钟）
3. AI 响应时间过长

**解决方案：**
1. 前端已实现断点续传机制，部分内容仍可显示
2. 优化 AI 提示，缩短响应时间
3. 检查网络连接稳定性

### Q13: AI 助手无法操作设备

**可能原因：**
1. 设备模板不存在
2. 设备实例未创建
3. API 名称不匹配

**解决方案：**
1. 确认设备模板已创建
2. 确认设备实例已放置在画布上
3. 使用准确的 API 名称（可从设备模板中查看）

---

## AI 助手使用指南

- **项目负责人：** [你的名字]
- **问题反馈：** [Issue 链接]
- **文档更新：** 提交 PR 修改 README.md

---

## 更新日志

- **v0.0.1** (2025-01-21)
  - 初始版本
  - 用户认证（注册/登录/登出）
  - JWT Token 认证与 Redis Token 黑名单
  - 设备模板管理（增删改查）
  - 设备实例管理（拖拽创建、拖拽移动）
  - 规则引擎（sources → target 数据流向）
  - 边可视化（自动计算端点坐标）
  - 规格管理（IF-THEN 规则）
  - 形式化验证准备
  - AI 助手（火山引擎集成，SSE 流式聊天）
  - 设备操作工具（自然语言创建设备）
  - 面板布局持久化

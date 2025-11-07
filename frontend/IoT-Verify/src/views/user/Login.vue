<script setup lang="ts">
import {ElForm, ElFormItem, ElMessage} from "element-plus";
import {ref, computed} from 'vue';
import {router} from '../../router';
import {userInfo, userLogin} from "../../api/user.ts";
// 输入框值（需要在前端拦截不合法输入：是否为空+额外规则）
const username = ref('');
const password = ref('');

// 电话号码是否为空
const hasUsernameInput = computed(() => username.value != '');
// 密码是否为空
const hasPasswordInput = computed(() => password.value != '');
// 密码不设置特殊规则
// 登录按钮可用性
const loginDisabled = computed(() => {
  return !(hasUsernameInput.value && hasPasswordInput.value);
});

//登录按钮触发
function handleLogin() {
  // userLogin({
  //   username: username.value,
  //   password: password.value
  // }).then(res => {
  //   if (res.data.code === '200') {
  //     console.log(res);
  //     ElMessage({
  //       message: "登录成功",
  //       type: 'success',
  //     });
  //     const token = res.data.data;
  //     sessionStorage.setItem('token', token);
  //     userInfo(username.value).then(res => {
  //       console.log(res.data);
  //       sessionStorage.setItem('username', res.data.data.username);
  //       sessionStorage.setItem('name', res.data.data.name);
  //       sessionStorage.setItem('role', res.data.data.role);
  //       sessionStorage.setItem('avatar', res.data.data.avatar);
  //       sessionStorage.setItem('telephone', res.data.data.telephone);
  //       sessionStorage.setItem('email', res.data.data.email);
  //       sessionStorage.setItem('location', res.data.data.location);
  //       sessionStorage.setItem('userId', res.data.data.id);
  //     });
  //     router.push({path: "/home"});
  //   } else  {
  //     ElMessage({
  //       message: res.data.code + res.data.msg,
  //       type: 'error',
  //     });
  //     password.value = '';
  //   }
  // });
  router.push({path: "/home"});
}
</script>

<template>
  <el-main class="main-frame bg-image">
    <el-card class="login-card">
      <div>
        <h1>登入您的<span class="tomato-logo">IoT-Verify</span>账户</h1>
        <el-form>
          <el-form-item>
            <label v-if="!hasUsernameInput" for="username">用户名</label>
            <label v-else for="username">用户名/手机号</label>
            <el-input id="username" type="text" v-model="username"
                      required :class="{'error-warn-input' :(!hasUsernameInput)}"
                      placeholder="请输入用户名"/>
          </el-form-item>

          <el-form-item>
            <label for="password">账户密码</label>
            <el-input id="password" type="password" v-model="password"
                      required
                      placeholder="••••••••"
                      show-password/>
          </el-form-item>

          <span class="button-group">
              <el-button @click.prevent="handleLogin" :disabled="loginDisabled"
                         type="primary">登入</el-button>
              <router-link to="/register" v-slot="{navigate}">
                <el-button @click="navigate">去注册</el-button>
              </router-link>
          </span>
        </el-form>
      </div>
    </el-card>
  </el-main>
</template>


<style scoped>
.main-frame {
  width: 100%;
  height: 100%;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
}

.bg-image {
  background-image: url("../../assets/login.jpg");
  background-repeat: no-repeat;
  background-position: center center;
  background-size: cover;
}
.login-card {
  width: 40%;
  padding: 20px;
  border-radius: 10px;
  background-color: rgba(255, 255, 255, 0.5); /* 半透明白色 */
  backdrop-filter: blur(10px);                /* 毛玻璃模糊效果 */
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.2);   /* 柔和阴影 */
  border: 1px solid rgba(255, 255, 255, 0.3);  /* 淡淡的边框 */
}

.tomato-logo {
  color: #91265b; /* 番茄红 */
  font-weight: bold;
}

.error-warn-input {
  --el-input-focus-border-color: red;
}

.button-group {
  padding-top: 10px;
  display: flex;
  flex-direction: row;
  gap: 30px;
  align-items: center;
  justify-content: right;
}

:deep(.el-input__wrapper) {
  background-color: rgba(255, 255, 255, 0.25);
  border: 1px solid rgba(255, 255, 255, 0.3);
  border-radius: 8px;
  backdrop-filter: blur(4px);
}

</style>

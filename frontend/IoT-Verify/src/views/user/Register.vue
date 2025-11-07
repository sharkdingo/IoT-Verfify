<script setup lang="ts">
import { ref, computed } from 'vue'
import { router } from '../../router'
import { uploadImage } from '../../api/tools';
import { userRegister } from "../../api/user.ts"
import { runWithTimeout } from "../../utils";
import { UploadFilled } from "@element-plus/icons-vue";
import "../../styles/base.css";

const username = ref('')
const password = ref('')
const confirmPassword = ref('')
const name = ref('')
const role = ref('')
const telephone = ref('')
const email = ref('')
const location = ref('')

const hasUsernameInput = computed(() => username.value != '')
const hasPasswordInput = computed(() => password.value != '')
const hasNameInput = computed(() => name.value != '')
const hasRoleInput = computed(() => role.value != '')
const hasTelephoneInput = computed(() => telephone.value != '')
const hasEmailInput = computed(() => email.value != '')
const hasConfirmPasswordInput = computed(() => confirmPassword.value != '')

const chinaMobileRegex = /^1(3[0-9]|4[579]|5[0-35-9]|6[2567]|7[0-8]|8[0-9]|9[189])\d{8}$/
const telLegal = computed(() => chinaMobileRegex.test(telephone.value))
const emailRegex = /^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/;
const emailLegal = computed(() => emailRegex.test(email.value))

const isPasswordIdentical = computed(() => password.value == confirmPassword.value)

const registerDisabled = computed(() => {
  const mustFields = hasUsernameInput.value && hasPasswordInput.value && hasNameInput.value && hasRoleInput.value && isPasswordIdentical.value
  // 如果电话输入了，那就必须合法才行；如果没输入就无所谓
  const phoneOk = !hasTelephoneInput.value || telLegal.value
  const emailOk = !hasEmailInput.value || emailLegal.value
  return !(mustFields && phoneOk && emailOk)
})

async function handleRegister() {
  return userRegister({
    username: username.value,
    password: password.value,
    avatar: imgURLs.value[0],
    name: name.value,
    role: role.value,
    telephone: telephone.value,
    email: email.value,
    location: location.value,
  }).then(res => {
    if (res.data.code === '200') {
      clearCache();
      ElMessage({
        message: "注册成功！请登录账号",
        type: 'success',
      });
      router.push({ path: "/login" });
    } else {
      resetImgCache();
      ElMessage({
        message: res.data.code + res.data.msg,
        type: 'error',
      });
    }
  });
}

//file
const imageFileList = ref([] as any);
const imgURLs = ref([] as any);
const loading = ref(false);
async function handleChangeUltimate() {
  loading.value = true;
  try {
    await runWithTimeout(async () => {
      await loopUpload();
      await handleRegister(); // 注意：handleRegister 也要改成 async 返回 Promise
    }, 10000); // 设置超时 10 秒
  } catch (err) {
    resetImgCache();
    ElMessage({
      message: "创建账户失败：请求超时，请重试",
      type: 'error',
    });
  } finally {
    loading.value = false;
  }
}
async function loopUpload() {
  for (let image of imageFileList.value) {
    let formData = new FormData();
    formData.append('file', image.raw);
    const res = await uploadImage(formData);
    imgURLs.value.push(res.data.data as string);
  }
}
// 在上传失败时，因为上传图片并保存url先于上传执行，将已经保存的url作废
function resetImgCache() {
  imgURLs.value = [];
}
function handleExceed() {
  ElMessage.warning(`当前限制选择 1 个文件`);
}
// 成功时调用
function clearCache() {
  imgURLs.value = [];
  imageFileList.value = [];
  username.value = '';
  password.value = '';
  confirmPassword.value = '';
  name.value = '';
  role.value = '';
  location.value = '';
  email.value = '';
}
const beforeUpload = (file: File) => {
  const isLt5M = file.size / 1024 / 1024 < 10;
  if (!isLt5M) {
    ElMessage.error('上传的文件不能超过 10MB 哦~');
  }
  return isLt5M;
};

</script>


<template>
  <el-main class="main-frame bg-image">
    <el-card class="login-card">
      <div>
        <h1>创建新的账户</h1>

        <el-form>

          <el-form-item label="头像（可选）" label-position="top">
            <el-upload
                v-model:file-list="imageFileList"
                :limit="1"
                :on-exceed="handleExceed"
                class="upload-demo input"
                list-type="picture"
                :auto-upload="false"
                drag
                :before-upload="beforeUpload"
            >
              <el-icon class="el-icon--upload">
                <upload-filled/>
              </el-icon>
              <div class="el-upload__text">
                将头像文件拖到此处或单击此处上传。仅允许上传一份文件。
              </div>
            </el-upload>
          </el-form-item>

          <el-row>
            <el-col :span="12">
              <el-form-item>
                <label for="username">昵称</label>
                <el-input id="username"
                          v-model="username"
                          placeholder="请输入昵称"/>
              </el-form-item>
            </el-col>

            <el-col :span="1"></el-col>

            <el-col :span="11">
              <el-form-item>
                <label for="role">身份</label>
                <el-select id="role"
                           v-model="role"
                           placeholder="请选择"
                           style="width: 100%;"
                >
                  <el-option value="ADMIN" label="管理员"/>
                  <el-option value="USER" label="用户"/>
                </el-select>
              </el-form-item>
            </el-col>
          </el-row>

          <el-row>
            <el-col :span="12">
              <el-form-item>

                <label v-if="!hasEmailInput" for="email">
                  邮箱（可选）
                </label>
                <label v-else-if="!emailLegal" for="email" class="error-warn">
                  邮箱不合法
                </label>
                <label v-else for="email">
                  邮箱（可选）
                </label>

                <el-input id="email"
                          v-model="email"
                          placeholder="请输入邮箱"/>
              </el-form-item>
            </el-col>

            <el-col :span="1"></el-col>

            <el-col :span="11">
              <el-form-item>
                <label for="name">姓名</label>
                <el-input id="name"
                          v-model="name"
                          placeholder="请输入姓名"/>
              </el-form-item>
            </el-col>
          </el-row>

          <el-row>
            <el-col :span="12">
              <el-form-item>

                <label v-if="!hasTelephoneInput" for="telephone">
                  注册手机号（可选）
                </label>
                <label v-else-if="!telLegal" for="telephone" class="error-warn">
                  手机号不合法
                </label>
                <label v-else for="telephone">
                  注册手机号（可选）
                </label>

                <el-input id="telephone"
                          v-model="telephone" :class="{'error-warn-input' :(hasTelephoneInput && !telLegal)}"
                          placeholder="请输入手机号"/>
              </el-form-item>
            </el-col>

            <el-col :span="1"></el-col>

            <el-col :span="11">
              <el-form-item>
                <label for="location">
                  地址（可选）
                </label>
                <el-input id="location"
                          v-model="location"
                          placeholder="请输入地址"/>
              </el-form-item>
            </el-col>
          </el-row>

          <el-form-item>
            <label for="password">密码</label>
            <el-input type="password" id="password"
                      v-model="password"
                      placeholder="••••••••"/>
          </el-form-item>

          <el-form-item>
            <label v-if="!hasConfirmPasswordInput">确认密码</label>
            <label v-else-if="!isPasswordIdentical" class="error-warn">密码不一致</label>
            <label v-else>确认密码</label>

            <el-input type="password" id="confirm-password"
                      v-model="confirmPassword"
                      :class="{'error-warn-input' :(hasConfirmPasswordInput && !isPasswordIdentical)}"
                      placeholder="••••••••"/>
          </el-form-item>

          <span class="button-group">
            <el-button @click.prevent="handleChangeUltimate"
                       :disabled="registerDisabled"
                       :loading="loading"
                       type="primary">
              创建账户
            </el-button>

            <router-link to="/login" v-slot="{navigate}">
              <el-button @click="navigate">
                去登录
              </el-button>
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
  width: 55%;
  padding: 20px;
  border-radius: 10px;
  background-color: rgba(255, 255, 255, 0.5); /* 半透明白色 */
  backdrop-filter: blur(10px);                /* 毛玻璃模糊效果 */
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.2);   /* 柔和阴影 */
  border: 1px solid rgba(255, 255, 255, 0.3);  /* 淡淡的边框 */
}

.error-warn {
  color: red;
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
</style>

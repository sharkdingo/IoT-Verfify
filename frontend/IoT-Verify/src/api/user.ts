import {axios} from '../utils/request.ts';
import {USER_MODULE} from './_prefix';

type LoginInfo = {
    username: string,
    password: string
}

type RegisterInfo = {
    username: string,
    password: string,
    avatar?: string,
    name: string,
    role: string,
    telephone?: string,
    email?: string,
    location?: string
}

type UpdateInfo = {
    username: string,
    password?: string,
    name?: string,
    avatar?: string,
    role?: string,
    telephone?: string,
    email?: string,
    location?: string,
}

// 如果有“Vue: This may be converted to an async function”警告，可以不管
// 用户登录
export const userLogin = async (loginInfo: LoginInfo) => {
    console.log(loginInfo);
    const res = await axios.post(`${USER_MODULE}/login`, loginInfo);

    // 保存登录返回的 token（res.data.data 是你说的 JWT）
    const token = res.data.data;
    sessionStorage.setItem('token', token);

    return res;
};

// 用户注册
export const userRegister = async (registerInfo: RegisterInfo) => {
    try {
        return await axios.post(`${USER_MODULE}`, registerInfo);
    } catch (err) {
        console.error('注册失败', err);
        throw err;
    }
};


// 获取用户信息
export const userInfo = async (username: string) => {
    return axios.get(`${USER_MODULE}/${username}`);
};

// 更新用户信息
export const userInfoUpdate = async (updateInfo: UpdateInfo) => {
    console.log(updateInfo);
    return axios.put(`${USER_MODULE}`, updateInfo); // headers自动加上 token
};

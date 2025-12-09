// src/utils/http.ts
import axios from 'axios'

const api = axios.create({
    baseURL: 'http://localhost:8080/api', // 后端地址
    timeout: 10000
})

export default api
package cn.edu.nju.Iot_Verify.security;

import jakarta.servlet.FilterChain;
import jakarta.servlet.ReadListener;
import jakarta.servlet.ServletInputStream;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletRequestWrapper;
import jakarta.servlet.http.HttpServletResponse;
import org.springframework.boot.autoconfigure.security.SecurityProperties;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.core.annotation.Order;
import org.springframework.stereotype.Component;
import org.springframework.web.filter.OncePerRequestFilter;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.util.Locale;

/** Rejects oversized JSON requests before Jackson allocates the request graph. */
@Component
@Order(SecurityProperties.DEFAULT_FILTER_ORDER + 1)
public class RequestBodySizeFilter extends OncePerRequestFilter {

    private final long maxRequestBytes;
    private final long maxSceneRequestBytes;

    @Autowired
    public RequestBodySizeFilter(
            @Value("${iot-verify.http.max-request-bytes:4194304}") long maxRequestBytes,
            @Value("${iot-verify.http.max-scene-request-bytes:67108864}") long maxSceneRequestBytes) {
        this.maxRequestBytes = normalize(maxRequestBytes);
        this.maxSceneRequestBytes = Math.max(this.maxRequestBytes, normalize(maxSceneRequestBytes));
    }

    RequestBodySizeFilter(long maxRequestBytes) {
        this(maxRequestBytes, 64L * 1024L * 1024L);
    }

    @Override
    protected void doFilterInternal(HttpServletRequest request,
                                    HttpServletResponse response,
                                    FilterChain filterChain) throws ServletException, IOException {
        long requestLimit = requestLimit(request);
        long contentLength = request.getContentLengthLong();
        if (contentLength > requestLimit) {
            reject(response);
            return;
        }
        if (!isJson(request) || contentLength == 0) {
            filterChain.doFilter(request, response);
            return;
        }

        byte[] body = request.getInputStream().readNBytes((int) requestLimit + 1);
        if (body.length > requestLimit) {
            reject(response);
            return;
        }
        filterChain.doFilter(new CachedBodyRequest(request, body), response);
    }

    private long requestLimit(HttpServletRequest request) {
        String path = request.getRequestURI();
        return path != null && path.endsWith("/api/board/batch")
                ? maxSceneRequestBytes : maxRequestBytes;
    }

    private static long normalize(long value) {
        return Math.min(Integer.MAX_VALUE - 1L, Math.max(1024L, value));
    }

    private boolean isJson(HttpServletRequest request) {
        String contentType = request.getContentType();
        if (contentType == null) return false;
        String mediaType = contentType.split(";", 2)[0].trim().toLowerCase(Locale.ROOT);
        return "application/json".equals(mediaType) || mediaType.endsWith("+json");
    }

    private void reject(HttpServletResponse response) throws IOException {
        response.setStatus(HttpServletResponse.SC_REQUEST_ENTITY_TOO_LARGE);
        response.setContentType("application/json;charset=UTF-8");
        response.getWriter().write(
                "{\"code\":413,\"message\":\"Request body is too large\",\"data\":null}");
    }

    private static final class CachedBodyRequest extends HttpServletRequestWrapper {
        private final byte[] body;

        private CachedBodyRequest(HttpServletRequest request, byte[] body) {
            super(request);
            this.body = body;
        }

        @Override
        public int getContentLength() {
            return body.length;
        }

        @Override
        public long getContentLengthLong() {
            return body.length;
        }

        @Override
        public ServletInputStream getInputStream() {
            return new ByteArrayServletInputStream(body);
        }

        @Override
        public BufferedReader getReader() {
            String encoding = getCharacterEncoding();
            Charset charset = encoding == null ? StandardCharsets.UTF_8 : Charset.forName(encoding);
            return new BufferedReader(new InputStreamReader(getInputStream(), charset));
        }
    }

    private static final class ByteArrayServletInputStream extends ServletInputStream {
        private final ByteArrayInputStream input;

        private ByteArrayServletInputStream(byte[] body) {
            this.input = new ByteArrayInputStream(body);
        }

        @Override
        public int read() {
            return input.read();
        }

        @Override
        public int read(byte[] bytes, int offset, int length) {
            return input.read(bytes, offset, length);
        }

        @Override
        public boolean isFinished() {
            return input.available() == 0;
        }

        @Override
        public boolean isReady() {
            return true;
        }

        @Override
        public void setReadListener(ReadListener readListener) {
            throw new UnsupportedOperationException("Asynchronous request-body reads are not supported");
        }
    }
}

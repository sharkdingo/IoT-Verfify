package cn.edu.nju.Iot_Verify.security;

import jakarta.servlet.FilterChain;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletRequestWrapper;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import org.springframework.boot.autoconfigure.security.SecurityProperties;
import org.springframework.core.annotation.Order;
import org.springframework.mock.web.MockHttpServletRequest;
import org.springframework.mock.web.MockHttpServletResponse;

import java.nio.charset.StandardCharsets;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class RequestBodySizeFilterTest {

    private final RequestBodySizeFilter filter = new RequestBodySizeFilter(1024);

    @Test
    void bodyBufferingRunsAfterTheSpringSecurityFilterChain() {
        Order order = RequestBodySizeFilter.class.getAnnotation(Order.class);
        assertTrue(order.value() > SecurityProperties.DEFAULT_FILTER_ORDER);
    }

    @Test
    void chunkedJsonOverLimitIsRejectedBeforeControllerBinding() throws Exception {
        MockHttpServletRequest base = jsonRequest(new byte[1025]);
        HttpServletRequest chunked = new HttpServletRequestWrapper(base) {
            @Override
            public int getContentLength() {
                return -1;
            }

            @Override
            public long getContentLengthLong() {
                return -1;
            }
        };
        MockHttpServletResponse response = new MockHttpServletResponse();
        AtomicBoolean chainCalled = new AtomicBoolean();

        filter.doFilter(chunked, response, (request, servletResponse) -> chainCalled.set(true));

        assertEquals(413, response.getStatus());
        assertFalse(chainCalled.get());
        assertTrue(response.getContentAsString().contains("Request body is too large"));
    }

    @Test
    void boundedJsonBodyIsReplayableToDownstreamConsumers() throws Exception {
        byte[] body = "{\"message\":\"hello\"}".getBytes(StandardCharsets.UTF_8);
        MockHttpServletRequest request = jsonRequest(body);
        MockHttpServletResponse response = new MockHttpServletResponse();
        AtomicReference<byte[]> observed = new AtomicReference<>();
        FilterChain chain = (wrapped, servletResponse) ->
                observed.set(wrapped.getInputStream().readAllBytes());

        filter.doFilter(request, response, chain);

        assertEquals(200, response.getStatus());
        assertArrayEquals(body, observed.get());
    }

    /**
     * Both full-scene commands, not just the older one. A scene carries its self-contained template
     * snapshots and embedded icons, so leaving the import endpoint on the ordinary limit would reject
     * a file the exporter considers valid.
     */
    @ParameterizedTest
    @ValueSource(strings = {"/api/board/batch", "/api/board/scene"})
    void sceneCommandsUseTheirDedicatedLargerLimit(String path) throws Exception {
        byte[] body = new byte[2048];
        MockHttpServletRequest request = jsonRequest(body);
        request.setRequestURI(path);
        MockHttpServletResponse response = new MockHttpServletResponse();
        AtomicBoolean chainCalled = new AtomicBoolean();

        filter.doFilter(request, response, (wrapped, servletResponse) -> chainCalled.set(true));

        assertTrue(chainCalled.get());
        assertEquals(200, response.getStatus());
    }

    private MockHttpServletRequest jsonRequest(byte[] body) {
        MockHttpServletRequest request = new MockHttpServletRequest("POST", "/api/test");
        request.setContentType("application/json");
        request.setContent(body);
        return request;
    }
}

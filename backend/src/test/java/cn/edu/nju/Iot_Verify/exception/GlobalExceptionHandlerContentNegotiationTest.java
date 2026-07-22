package cn.edu.nju.Iot_Verify.exception;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.springframework.http.MediaType;
import org.springframework.test.web.servlet.MockMvc;
import org.springframework.test.web.servlet.setup.MockMvcBuilders;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RestController;

import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.get;
import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.post;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.header;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.content;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.jsonPath;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.status;

class GlobalExceptionHandlerContentNegotiationTest {

    private MockMvc mockMvc;

    @BeforeEach
    void setUp() {
        mockMvc = MockMvcBuilders.standaloneSetup(new ErrorProbeController())
                .setControllerAdvice(new GlobalExceptionHandler())
                .build();
    }

    @Test
    void resourceNotFound_retainsJsonEnvelopeForEventStreamAcceptHeader() throws Exception {
        mockMvc.perform(get("/error-probe/not-found").accept(MediaType.TEXT_EVENT_STREAM))
                .andExpect(status().isNotFound())
                .andExpect(content().contentTypeCompatibleWith(MediaType.APPLICATION_JSON))
                .andExpect(jsonPath("$.code").value(404))
                .andExpect(jsonPath("$.message").value("Chat session not found: missing"));
    }

    @Test
    void chatBusy_retainsConflictDetailsForEventStreamAcceptHeader() throws Exception {
        mockMvc.perform(get("/error-probe/busy").accept(MediaType.TEXT_EVENT_STREAM))
                .andExpect(status().isConflict())
                .andExpect(content().contentTypeCompatibleWith(MediaType.APPLICATION_JSON))
                .andExpect(jsonPath("$.code").value(409))
                .andExpect(jsonPath("$.data.reasonCode").value("CHAT_SESSION_BUSY"))
                .andExpect(jsonPath("$.data.sessionId").value("busy-session"));
    }

    @Test
    void wrongMethod_retainsThe405ProtocolStatus() throws Exception {
        mockMvc.perform(get("/error-probe/json-only"))
                .andExpect(status().isMethodNotAllowed())
                .andExpect(header().string("Allow", org.hamcrest.Matchers.containsString("POST")))
                .andExpect(jsonPath("$.code").value(405));
    }

    @Test
    void unsupportedRequestMediaType_retainsThe415ProtocolStatus() throws Exception {
        mockMvc.perform(post("/error-probe/json-only")
                        .contentType(MediaType.TEXT_PLAIN)
                        .content("text"))
                .andExpect(status().isUnsupportedMediaType())
                .andExpect(jsonPath("$.code").value(415));
    }

    @Test
    void unacceptableResponseMediaType_retainsThe406ProtocolStatus() throws Exception {
        mockMvc.perform(post("/error-probe/json-only")
                        .contentType(MediaType.APPLICATION_JSON)
                        .accept(MediaType.APPLICATION_XML)
                        .content("{}"))
                .andExpect(status().isNotAcceptable());
    }

    @RestController
    static class ErrorProbeController {

        @GetMapping("/error-probe/not-found")
        Object notFound() {
            throw ResourceNotFoundException.session("missing");
        }

        @GetMapping("/error-probe/busy")
        Object busy() {
            throw new ChatSessionBusyException("busy-session");
        }

        @PostMapping(value = "/error-probe/json-only",
                consumes = MediaType.APPLICATION_JSON_VALUE,
                produces = MediaType.APPLICATION_JSON_VALUE)
        Object jsonOnly() {
            return java.util.Map.of("ok", true);
        }
    }
}

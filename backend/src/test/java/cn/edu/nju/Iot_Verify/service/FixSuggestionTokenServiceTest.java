package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.configure.JwtConfig;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class FixSuggestionTokenServiceTest {

    private FixSuggestionTokenService service;

    @BeforeEach
    void setUp() {
        JwtConfig config = new JwtConfig();
        config.setSecret("test-secret-that-is-long-enough-for-hmac-signatures");
        service = new FixSuggestionTokenService(new ObjectMapper(), config);
    }

    @Test
    void verify_restoresSignedInternalRuleIndices() {
        FixSuggestionDto suggestion = FixSuggestionDto.builder()
                .strategy("remove")
                .description("Remove conflicting automation")
                .removedRuleIndices(List.of(2, 4))
                .removedRuleDescriptions(List.of("Rule 3", "Rule 5"))
                .verified(true)
                .build();
        Map<String, PreferredRange> ranges = Map.of();

        String token = service.issue(7L, 11L, suggestion, ranges);
        suggestion.setSuggestionToken(token);

        FixSuggestionDto trusted = service.verify(
                7L, 11L, "remove", suggestion, token, ranges);

        assertEquals(List.of(2, 4), trusted.getRemovedRuleIndices());
        assertEquals(List.of("Rule 3", "Rule 5"), trusted.getRemovedRuleDescriptions());
    }

    @Test
    void verify_rejectsVisibleSuggestionOrRangeTampering() {
        FixSuggestionDto suggestion = FixSuggestionDto.builder()
                .strategy("parameter")
                .description("Adjust threshold")
                .verified(true)
                .build();
        Map<String, PreferredRange> ranges = Map.of(
                "rule:1:condition:0", new PreferredRange(10, 20));
        String token = service.issue(7L, 11L, suggestion, ranges);

        suggestion.setDescription("Apply a different change");
        assertThrows(BadRequestException.class, () -> service.verify(
                7L, 11L, "parameter", suggestion, token, ranges));

        suggestion.setDescription("Adjust threshold");
        Map<String, PreferredRange> changedRanges = Map.of(
                "rule:1:condition:0", new PreferredRange(0, 100));
        assertThrows(BadRequestException.class, () -> service.verify(
                7L, 11L, "parameter", suggestion, token, changedRanges));
    }
}

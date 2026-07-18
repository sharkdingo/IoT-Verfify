package cn.edu.nju.Iot_Verify.component.ai;

import cn.edu.nju.Iot_Verify.component.ai.ChatConfirmationDetector.ConfirmationDecision;
import cn.edu.nju.Iot_Verify.component.ai.ChatConfirmationDetector.ConfirmationKind;
import cn.edu.nju.Iot_Verify.component.ai.ChatConfirmationDetector.DecisionType;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.EnumSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.ArgumentMatchers.anyDouble;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.argThat;
import static org.mockito.ArgumentMatchers.contains;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ChatConfirmationDetectorTest {

    @Mock
    private PromptCompletionService promptCompletionService;

    private ChatConfirmationDetector detector;

    @BeforeEach
    void setUp() {
        detector = new ChatConfirmationDetector(promptCompletionService, new ObjectMapper());
    }

    @Test
    void detect_usesModelMeaningAndAcceptsOnlyAPendingKind() {
        when(promptCompletionService.complete(
                argThat(prompt -> prompt.contains("meaning, context, and the user's language")),
                contains("latestUserMessage"), anyDouble(), anyInt()))
                .thenReturn("{\"decision\":\"CONFIRMED\",\"kind\":\"DESTRUCTIVE\"}")
                .thenReturn("{\"decision\":\"CONFIRMED\",\"kind\":\"SCENE_REPLACEMENT\"}");

        ConfirmationDecision confirmed = detector.detect(
                "Express this however the user naturally prefers.",
                EnumSet.of(ConfirmationKind.DESTRUCTIVE));
        ConfirmationDecision impossibleKind = detector.detect(
                "Another natural-language reply.",
                EnumSet.of(ConfirmationKind.DESTRUCTIVE));

        assertEquals(DecisionType.CONFIRMED, confirmed.type());
        assertEquals(ConfirmationKind.DESTRUCTIVE, confirmed.kind());
        assertEquals(DecisionType.NONE, impossibleKind.type());
    }

    @Test
    void detect_preservesAmbiguityAndCancelAllSemantics() {
        when(promptCompletionService.complete(
                org.mockito.ArgumentMatchers.anyString(), org.mockito.ArgumentMatchers.anyString(),
                anyDouble(), anyInt()))
                .thenReturn("```json\n{\"decision\":\"AMBIGUOUS\",\"kind\":null}\n```")
                .thenReturn("{\"decision\":\"CANCELLED\",\"kind\":\"ALL\"}");
        EnumSet<ConfirmationKind> pending = EnumSet.of(
                ConfirmationKind.DESTRUCTIVE, ConfirmationKind.SCENE_REPLACEMENT);

        assertEquals(DecisionType.AMBIGUOUS, detector.detect("Proceed.", pending).type());
        ConfirmationDecision cancelled = detector.detect("Cancel the pending work.", pending);
        assertEquals(DecisionType.CANCELLED, cancelled.type());
        assertEquals(null, cancelled.kind());
    }

    @Test
    void detect_failsClosedForMissingPendingContextOrInvalidModelOutput() {
        assertEquals(DecisionType.NONE,
                detector.detect("yes", EnumSet.noneOf(ConfirmationKind.class)).type());

        when(promptCompletionService.complete(
                org.mockito.ArgumentMatchers.anyString(), org.mockito.ArgumentMatchers.anyString(),
                anyDouble(), anyInt())).thenReturn("not-json");

        assertEquals(DecisionType.NONE,
                detector.detect("Any reply", EnumSet.of(ConfirmationKind.CHOICE)).type());
    }
}

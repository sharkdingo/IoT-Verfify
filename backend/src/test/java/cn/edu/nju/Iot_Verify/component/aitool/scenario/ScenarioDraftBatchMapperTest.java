package cn.edu.nju.Iot_Verify.component.aitool.scenario;

import cn.edu.nju.Iot_Verify.component.board.BoardBatchRequestParser;
import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ScenarioDraftBatchMapperTest {

    @Mock
    private BoardBatchRequestParser parser;

    private final ObjectMapper objectMapper = new ObjectMapper();

    @Test
    void toBatch_convertsPortableRulesAndSpecificationsToBoardWriteContract() throws Exception {
        BoardBatchDto expected = new BoardBatchDto();
        when(parser.parse(any())).thenReturn(expected);
        ScenarioDraftBatchMapper mapper = new ScenarioDraftBatchMapper(objectMapper, parser);
        JsonNode scene = objectMapper.readTree("""
                {
                  "templates": [],
                  "devices": [{
                    "id":"device_1","templateName":"Light","label":"Hall Light",
                    "position":{"x":0,"y":0},"state":"off","width":176,"height":128
                  }],
                  "environmentVariables": [],
                  "rules": [{
                    "name":"Turn on the light",
                    "sources":[{
                      "fromId":"device_1","itemType":"state","fromApi":"state",
                      "relation":"=","value":"off"
                    }],
                    "toId":"device_1","toApi":"on"
                  }],
                  "specs": [{
                    "templateId":"1",
                    "aConditions":[{
                      "deviceId":"device_1","targetType":"api","key":"on",
                      "relation":"=","value":"TRUE"
                    }],
                    "ifConditions":[],"thenConditions":[]
                  }]
                }
                """);

        BoardBatchDto actual = mapper.toBatch(scene, "board-impact");

        assertEquals(expected, actual);
        ArgumentCaptor<JsonNode> bodyCaptor = ArgumentCaptor.forClass(JsonNode.class);
        verify(parser).parse(bodyCaptor.capture());
        JsonNode body = bodyCaptor.getValue();
        assertEquals("board-impact", body.path("impactToken").asText());
        assertEquals("device_1", body.path("nodes").get(0).path("id").asText());
        JsonNode condition = body.path("rules").get(0).path("conditions").get(0);
        assertEquals("device_1", condition.path("deviceName").asText());
        assertEquals("state", condition.path("attribute").asText());
        assertEquals("Turn on the light", body.path("rules").get(0).path("ruleString").asText());
        JsonNode spec = body.path("specs").get(0);
        assertEquals("chat_scene_spec_1", spec.path("id").asText());
        assertFalse(spec.path("aConditions").get(0).has("side"));
        assertEquals("api", spec.path("aConditions").get(0).path("targetType").asText());
        assertEquals("=", spec.path("aConditions").get(0).path("relation").asText());
        assertEquals("TRUE", spec.path("aConditions").get(0).path("value").asText());
    }
}

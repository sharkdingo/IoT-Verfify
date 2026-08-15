package cn.edu.nju.Iot_Verify.component.board;

import cn.edu.nju.Iot_Verify.component.template.DeviceTemplateSchemaValidator;
import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import jakarta.validation.Validation;

import java.util.List;
import java.util.Map;

/**
 * Imports a shipped scene file the way the product does, for tests that verify what a scene models.
 *
 * <p>Both scene NuSMV tests previously hand-built {@link RuleDto} and {@link SpecificationDto} from the
 * scene JSON. That verified "this file, parsed the way the test author understood it, generates correct
 * SMV" rather than "this file, imported, generates correct SMV" — so a scene could pass the suite and
 * be refused by the real endpoint, with the failure reading as a product bug. Routing both through
 * {@link PortableSceneBatchMapper} and the real {@link BoardBatchRequestParser} means the shipped
 * scenes also regression-test admission, and there is one reader instead of three.</p>
 */
public final class PortableSceneTestImport {

    private PortableSceneTestImport() {
    }

    /**
     * @param specIdPrefix provenance prefix for the minted specification ids, matching what the
     *                     production import path supplies
     */
    public static BoardBatchDto importScene(JsonNode scene, String specIdPrefix) {
        ObjectMapper mapper = new ObjectMapper();
        BoardBatchRequestParser batchParser = new BoardBatchRequestParser(
                mapper,
                Validation.buildDefaultValidatorFactory().getValidator(),
                new DeviceTemplateSchemaValidator(mapper));
        // The token is compared against a live board preview inside the service, which these
        // generator-level tests do not reach; any non-blank value satisfies the request boundary.
        return new PortableSceneBatchMapper(mapper, batchParser)
                .toBatch(scene, "test-impact-token", specIdPrefix);
    }

    /**
     * Rules as imported, with ids assigned.
     *
     * <p>The generator resolves rule references by id and storage assigns them on persist. These tests
     * stop short of the database, so the ids are minted here rather than left null.</p>
     */
    public static List<RuleDto> importRules(JsonNode scene) {
        List<RuleDto> rules = importScene(scene, "scene_spec_").getRules();
        for (int index = 0; index < rules.size(); index++) {
            rules.get(index).setId((long) (index + 1));
        }
        return rules;
    }

    /**
     * Specifications as imported, with the display caches the storage layer would rebuild.
     *
     * <p>Labels and device summaries are deliberately excluded from the portable format, so they are
     * not import semantics and are supplied here instead.</p>
     */
    public static List<SpecificationDto> importSpecs(JsonNode scene,
                                                     String idPrefix,
                                                     Map<String, String> labelsByDeviceId) {
        List<SpecificationDto> specs = importScene(scene, idPrefix + "-spec-").getSpecs();
        for (int index = 0; index < specs.size(); index++) {
            SpecificationDto spec = specs.get(index);
            spec.setTemplateLabel("Scene specification " + (index + 1));
            spec.setDevices(List.of());
            labelConditions(spec.getAConditions(), "a", labelsByDeviceId);
            labelConditions(spec.getIfConditions(), "if", labelsByDeviceId);
            labelConditions(spec.getThenConditions(), "then", labelsByDeviceId);
        }
        return specs;
    }

    private static void labelConditions(List<SpecConditionDto> conditions,
                                        String side,
                                        Map<String, String> labelsByDeviceId) {
        int index = 0;
        for (SpecConditionDto condition : conditions) {
            condition.setId(side + "-" + ++index);
            condition.setSide(side);
            condition.setDeviceLabel(labelsByDeviceId.get(condition.getDeviceId()));
        }
    }
}

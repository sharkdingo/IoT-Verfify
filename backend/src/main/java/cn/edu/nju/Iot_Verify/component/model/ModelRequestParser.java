package cn.edu.nju.Iot_Verify.component.model;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.DeserializationFeature;
import com.fasterxml.jackson.databind.JsonMappingException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.exc.UnrecognizedPropertyException;
import jakarta.validation.ConstraintViolationException;
import jakarta.validation.Validator;
import lombok.RequiredArgsConstructor;
import org.springframework.stereotype.Component;

import java.io.IOException;
/** Strict JSON boundary for requests whose fields define the checked model. */
@Component
@RequiredArgsConstructor
public class ModelRequestParser {

    private final ObjectMapper objectMapper;
    private final Validator validator;

    public VerificationRequestDto parseVerification(JsonNode body) {
        return parse(body, VerificationRequestDto.class, "Verification");
    }

    public SimulationRequestDto parseSimulation(JsonNode body) {
        return parse(body, SimulationRequestDto.class, "Simulation");
    }

    private <T> T parse(JsonNode body, Class<T> type, String requestKind) {
        if (body == null || !body.isObject()) {
            throw new BadRequestException(requestKind + " request must be a JSON object.");
        }

        final T request;
        try {
            request = objectMapper.readerFor(type)
                    .with(DeserializationFeature.FAIL_ON_UNKNOWN_PROPERTIES)
                    .readValue(objectMapper.treeAsTokens(body));
        } catch (UnrecognizedPropertyException exception) {
            throw new BadRequestException("Unknown field '" + exception.getPropertyName() + "' at '"
                    + formatPath(exception) + "'. The request was rejected because ignoring it could change "
                    + "what the model checks.");
        } catch (JsonProcessingException exception) {
            String path = exception instanceof JsonMappingException mappingException
                    ? formatPath(mappingException)
                    : "request";
            throw new BadRequestException("Invalid " + requestKind.toLowerCase() + " value at '" + path
                    + "': " + exception.getOriginalMessage() + ".");
        } catch (IOException exception) {
            throw new BadRequestException(requestKind + " request JSON could not be read.");
        }

        var violations = validator.validate(request);
        if (!violations.isEmpty()) {
            // Preserve the REST contract: DTO/shape violations are HTTP 400, while
            // model-semantic validation performed by the services remains HTTP 422.
            throw new ConstraintViolationException(violations);
        }
        return request;
    }

    private String formatPath(JsonMappingException exception) {
        StringBuilder path = new StringBuilder();
        for (JsonMappingException.Reference reference : exception.getPath()) {
            if (reference.getFieldName() != null) {
                if (!path.isEmpty()) {
                    path.append('.');
                }
                path.append(reference.getFieldName());
            } else if (reference.getIndex() >= 0) {
                path.append('[').append(reference.getIndex()).append(']');
            }
        }
        return path.isEmpty() ? "request" : path.toString();
    }
}

package cn.edu.nju.Iot_Verify.exception;

import cn.edu.nju.Iot_Verify.dto.Result;
import com.fasterxml.jackson.databind.JsonMappingException;
import com.fasterxml.jackson.databind.exc.UnrecognizedPropertyException;
import lombok.extern.slf4j.Slf4j;
import org.springframework.dao.DataIntegrityViolationException;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.http.converter.HttpMessageNotReadableException;
import org.springframework.security.access.AccessDeniedException;
import org.springframework.security.core.AuthenticationException;
import org.springframework.web.bind.MethodArgumentNotValidException;
import org.springframework.web.bind.MissingServletRequestParameterException;
import org.springframework.web.bind.annotation.ExceptionHandler;
import org.springframework.web.bind.annotation.RestControllerAdvice;
import org.springframework.web.method.annotation.MethodArgumentTypeMismatchException;
import org.springframework.web.servlet.NoHandlerFoundException;
import org.springframework.web.servlet.resource.NoResourceFoundException;

import jakarta.persistence.EntityNotFoundException;
import jakarta.validation.ConstraintViolationException;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

@Slf4j
@RestControllerAdvice
public class GlobalExceptionHandler {

    @ExceptionHandler(BaseException.class)
    public ResponseEntity<Result<Void>> handleBaseException(BaseException e) {
        log.warn("Business exception [{}]: {}", e.getCode(), e.getMessage());
        return ResponseEntity
                .status(e.getCode())
                .body(Result.error(e.getCode(), e.getMessage()));
    }

    @ExceptionHandler(BadRequestException.class)
    public ResponseEntity<Result<Void>> handleBadRequestException(BadRequestException e) {
        log.warn("Bad request: {}", e.getMessage());
        return ResponseEntity
                .status(HttpStatus.BAD_REQUEST)
                .body(Result.badRequest(e.getMessage()));
    }

    @ExceptionHandler(UnauthorizedException.class)
    public ResponseEntity<Result<Void>> handleUnauthorizedException(UnauthorizedException e) {
        log.warn("Unauthorized: {}", e.getMessage());
        return ResponseEntity
                .status(HttpStatus.UNAUTHORIZED)
                .body(Result.unauthorized(e.getMessage()));
    }

    @ExceptionHandler(ForbiddenException.class)
    public ResponseEntity<Result<Void>> handleForbiddenException(ForbiddenException e) {
        log.warn("Forbidden: {}", e.getMessage());
        return ResponseEntity
                .status(HttpStatus.FORBIDDEN)
                .body(Result.forbidden(e.getMessage()));
    }

    @ExceptionHandler(ResourceNotFoundException.class)
    public ResponseEntity<Result<Void>> handleResourceNotFoundException(ResourceNotFoundException e) {
        log.warn("Resource not found: {}", e.getMessage());
        return ResponseEntity
                .status(HttpStatus.NOT_FOUND)
                .body(Result.notFound(e.getMessage()));
    }

    @ExceptionHandler(BoardReplacementStaleException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleBoardReplacementStaleException(
            BoardReplacementStaleException e) {
        log.warn("Board replacement confirmation became stale");
        Result<Map<String, Object>> result = Result.error(HttpStatus.CONFLICT.value(), e.getMessage());
        result.setData(Map.of(
                "reasonCode", "BOARD_REPLACEMENT_STALE",
                "currentPreview", e.getCurrentPreview()));
        return ResponseEntity.status(HttpStatus.CONFLICT).body(result);
    }

    @ExceptionHandler(ConflictException.class)
    public ResponseEntity<Result<Void>> handleConflictException(ConflictException e) {
        log.warn("Conflict: {}", e.getMessage());
        return ResponseEntity
                .status(HttpStatus.CONFLICT)
                .body(Result.conflict(e.getMessage()));
    }

    @ExceptionHandler(FuzzTaskQuotaExceededException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleFuzzTaskQuotaExceededException(
            FuzzTaskQuotaExceededException e) {
        log.warn("Counterexample-search active-task limit reached: active={}, limit={}",
                e.getActiveTaskCount(), e.getMaxActiveTasksPerUser());
        Result<Map<String, Object>> result = Result.error(
                HttpStatus.TOO_MANY_REQUESTS.value(), e.getMessage());
        result.setData(Map.of(
                "reasonCode", FuzzTaskQuotaExceededException.REASON_CODE,
                "activeTaskCount", e.getActiveTaskCount(),
                "maxActiveTasksPerUser", e.getMaxActiveTasksPerUser()));
        return ResponseEntity.status(HttpStatus.TOO_MANY_REQUESTS).body(result);
    }

    @ExceptionHandler(FuzzTaskStorageQuotaExceededException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleFuzzTaskStorageQuotaExceededException(
            FuzzTaskStorageQuotaExceededException e) {
        log.warn("Counterexample-search stored-task limit reached: stored={}, limit={}",
                e.getStoredTaskCount(), e.getMaxStoredTasksPerUser());
        Result<Map<String, Object>> result = Result.error(
                HttpStatus.TOO_MANY_REQUESTS.value(), e.getMessage());
        result.setData(Map.of(
                "reasonCode", FuzzTaskStorageQuotaExceededException.REASON_CODE,
                "storedTaskCount", e.getStoredTaskCount(),
                "maxStoredTasksPerUser", e.getMaxStoredTasksPerUser()));
        return ResponseEntity.status(HttpStatus.TOO_MANY_REQUESTS).body(result);
    }

    @ExceptionHandler(AsyncTaskQuotaExceededException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleAsyncTaskQuotaExceededException(
            AsyncTaskQuotaExceededException e) {
        log.warn("{} {}-task limit reached: count={}, limit={}",
                e.getTaskKind(), e.getQuotaType(), e.getTaskCount(), e.getMaxTasksPerUser());
        Result<Map<String, Object>> result = Result.error(
                HttpStatus.TOO_MANY_REQUESTS.value(), e.getMessage());
        result.setData(Map.of(
                "reasonCode", e.getReasonCode(),
                "taskKind", e.getTaskKind(),
                "quotaType", e.getQuotaType().name(),
                "taskCount", e.getTaskCount(),
                "maxTasksPerUser", e.getMaxTasksPerUser()));
        return ResponseEntity.status(HttpStatus.TOO_MANY_REQUESTS).body(result);
    }

    @ExceptionHandler(ChatSessionBusyException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleChatSessionBusyException(
            ChatSessionBusyException e) {
        log.warn("Chat session is busy: {}", e.getSessionId());
        Result<Map<String, Object>> result = Result.error(HttpStatus.CONFLICT.value(), e.getMessage());
        result.setData(Map.of(
                "reasonCode", e.getReasonCode(),
                "sessionId", e.getSessionId()));
        return ResponseEntity.status(HttpStatus.CONFLICT).body(result);
    }

    @ExceptionHandler(TemplateDeletionConflictException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleTemplateDeletionConflictException(
            TemplateDeletionConflictException e) {
        log.warn("Template deletion conflict [{}]", e.getReasonCode());
        Result<Map<String, Object>> result = Result.error(HttpStatus.CONFLICT.value(), e.getMessage());
        result.setData(Map.of(
                "reasonCode", e.getReasonCode(),
                "currentPreview", e.getCurrentPreview()));
        return ResponseEntity.status(HttpStatus.CONFLICT).body(result);
    }

    @ExceptionHandler(ValidationException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleValidationException(ValidationException e) {
        log.warn("Validation error: {}", e.getMessage());
        Result<Map<String, Object>> result = Result.error(422, e.getMessage());
        result.setData(Map.of("errors", e.getErrors()));
        return ResponseEntity
                .status(HttpStatus.UNPROCESSABLE_ENTITY)  // 422
                .body(result);
    }

    @ExceptionHandler(SmvGenerationException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleSmvGenerationException(SmvGenerationException e) {
        log.error("SMV generation error [{}]: {}", e.getErrorCategory(), e.getMessage(), e);
        Result<Map<String, Object>> result = Result.error(
                HttpStatus.INTERNAL_SERVER_ERROR.value(),
                "[" + e.getErrorCategory() + "] " + e.getMessage()
        );
        result.setData(Map.of("errorCategory", e.getErrorCategory()));
        return ResponseEntity
                .status(HttpStatus.INTERNAL_SERVER_ERROR)
                .body(result);
    }

    @ExceptionHandler(PersistedDataIntegrityException.class)
    public ResponseEntity<Result<Map<String, Object>>> handlePersistedDataIntegrityException(
            PersistedDataIntegrityException e) {
        log.error("Persisted semantic data is invalid: type={}, id={}, field={}",
                e.getRecordType(), e.getRecordId(), e.getField(), e);
        Result<Map<String, Object>> result = Result.error(
                HttpStatus.INTERNAL_SERVER_ERROR.value(),
                "Stored model data is invalid; the operation was stopped before using an incomplete model.");
        Map<String, Object> details = new LinkedHashMap<>();
        details.put("reasonCode", e.getReasonCode());
        details.put("recordType", e.getRecordType());
        if (e.getRecordId() != null) details.put("recordId", e.getRecordId());
        details.put("field", e.getField());
        result.setData(details);
        return ResponseEntity.status(HttpStatus.INTERNAL_SERVER_ERROR).body(result);
    }

    @ExceptionHandler(InternalServerException.class)
    public ResponseEntity<Result<Void>> handleInternalServerException(InternalServerException e) {
        log.error("Internal server error: {}", e.getMessage(), e);
        return ResponseEntity
                .status(HttpStatus.INTERNAL_SERVER_ERROR)
                .body(Result.error("Internal server error"));
    }

    @ExceptionHandler(ServiceUnavailableException.class)
    public ResponseEntity<Result<Void>> handleServiceUnavailableException(ServiceUnavailableException e) {
        log.error("Service unavailable: {}", e.getMessage());
        return ResponseEntity
                .status(HttpStatus.SERVICE_UNAVAILABLE)
                .body(Result.serviceUnavailable(e.getMessage()));
    }

    @ExceptionHandler(FixApplyPreflightUnavailableException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleFixApplyPreflightUnavailableException(
            FixApplyPreflightUnavailableException e) {
        log.warn("Automatic-fix apply preflight unavailable");
        Result<Map<String, Object>> result = Result.error(
                HttpStatus.SERVICE_UNAVAILABLE.value(), e.getMessage());
        result.setData(Map.of("reasonCode", FixApplyPreflightUnavailableException.REASON_CODE));
        return ResponseEntity.status(HttpStatus.SERVICE_UNAVAILABLE).body(result);
    }

    @ExceptionHandler(SimulationExecutionException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleSimulationExecutionException(
            SimulationExecutionException e) {
        log.warn("Simulation did not produce a trace [{}]: {}", e.getReasonCode(), e.getMessage());
        Result<Map<String, Object>> result = Result.error(e.getCode(), e.getMessage());
        result.setData(Map.of(
                "reasonCode", e.getReasonCode(),
                "logs", e.getLogs()
        ));
        return ResponseEntity.status(e.getCode()).body(result);
    }

    @ExceptionHandler(MethodArgumentTypeMismatchException.class)
    public ResponseEntity<Result<Void>> handleMethodArgumentTypeMismatch(MethodArgumentTypeMismatchException e) {
        log.warn("Argument type mismatch: {} for parameter '{}'", e.getValue(), e.getName());
        return ResponseEntity
                .status(HttpStatus.BAD_REQUEST)
                .body(Result.badRequest("Invalid parameter '" + e.getName() + "': expected a valid number"));
    }

    @ExceptionHandler(MissingServletRequestParameterException.class)
    public ResponseEntity<Result<Void>> handleMissingServletRequestParameter(
            MissingServletRequestParameterException e) {
        log.warn("Missing required request parameter: {}", e.getParameterName());
        return ResponseEntity
                .status(HttpStatus.BAD_REQUEST)
                .body(Result.badRequest("Missing required parameter '" + e.getParameterName() + "'"));
    }

    @ExceptionHandler(HttpMessageNotReadableException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleHttpMessageNotReadableException(
            HttpMessageNotReadableException e) {
        log.warn("Malformed request body: {}", e.getMessage());
        RequestBodyError error = describeRequestBodyError(e);
        Result<Map<String, Object>> result = Result.error(HttpStatus.BAD_REQUEST.value(), error.message());
        result.setData(Map.of("errors", Map.of(error.path(), error.reason())));
        return ResponseEntity
                .status(HttpStatus.BAD_REQUEST)
                .body(result);
    }

    @ExceptionHandler(IllegalArgumentException.class)
    public ResponseEntity<Result<Void>> handleIllegalArgumentException(IllegalArgumentException e) {
        log.warn("IllegalArgumentException: {}", e.getMessage());
        return ResponseEntity
                .status(HttpStatus.BAD_REQUEST)
                .body(Result.badRequest("Invalid request parameter"));
    }

    @ExceptionHandler(MethodArgumentNotValidException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleMethodArgumentNotValidException(MethodArgumentNotValidException e) {
        Map<String, String> errors = new LinkedHashMap<>();
        e.getBindingResult().getFieldErrors().forEach(error -> mergeValidationError(
                errors, error.getField(), Objects.toString(error.getDefaultMessage(), "Validation failed")));
        String message = validationMessage(errors);
        log.warn("Validation failed: {}", message);
        Result<Map<String, Object>> result = Result.error(400, message);
        result.setData(Map.of("errors", errors));
        return ResponseEntity
                .status(HttpStatus.BAD_REQUEST)
                .body(result);
    }

    @ExceptionHandler(org.springframework.web.method.annotation.HandlerMethodValidationException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleHandlerMethodValidationException(
            org.springframework.web.method.annotation.HandlerMethodValidationException e) {
        Map<String, String> errors = new LinkedHashMap<>();
        int[] index = {0};
        e.getAllErrors().forEach(error -> {
            String reason = error.getDefaultMessage();
            if (reason != null) errors.put("request[" + index[0]++ + "]", reason);
        });
        String message = validationMessage(errors);
        log.warn("Handler method validation failed: {}", message);
        Result<Map<String, Object>> result = Result.error(400, message);
        result.setData(Map.of("errors", errors));
        return ResponseEntity
                .status(HttpStatus.BAD_REQUEST)
                .body(result);
    }

    @ExceptionHandler(ConstraintViolationException.class)
    public ResponseEntity<Result<Map<String, Object>>> handleConstraintViolationException(ConstraintViolationException e) {
        Map<String, String> errors = new LinkedHashMap<>();
        e.getConstraintViolations().forEach(violation -> mergeValidationError(
                errors, violation.getPropertyPath().toString(), violation.getMessage()));
        String message = validationMessage(errors);
        log.warn("Constraint violation: {}", message);
        Result<Map<String, Object>> result = Result.error(400, message);
        result.setData(Map.of("errors", errors));
        return ResponseEntity
                .status(HttpStatus.BAD_REQUEST)
                .body(result);
    }

    private void mergeValidationError(Map<String, String> errors, String field, String reason) {
        errors.merge(field, reason, (first, next) -> first.equals(next) ? first : first + "; " + next);
    }

    private String validationMessage(Map<String, String> errors) {
        return errors.entrySet().stream()
                .map(entry -> entry.getKey() + ": " + entry.getValue())
                .findFirst()
                .orElse("Validation failed");
    }

    private RequestBodyError describeRequestBodyError(HttpMessageNotReadableException exception) {
        Throwable cause = exception.getCause();
        while (cause != null) {
            if (cause instanceof UnrecognizedPropertyException unknown) {
                String path = jsonPath(unknown.getPath());
                if (path.isBlank()) path = unknown.getPropertyName();
                String message = "Unknown field '" + unknown.getPropertyName() + "'";
                if (!path.equals(unknown.getPropertyName())) message += " at '" + path + "'";
                return new RequestBodyError(path, "Unknown field", message);
            }
            if (cause instanceof JsonMappingException mapping && !mapping.getPath().isEmpty()) {
                String path = jsonPath(mapping.getPath());
                String reason = "Value does not match the declared field type";
                return new RequestBodyError(path, reason, "Invalid JSON value at '" + path + "': " + reason);
            }
            cause = cause.getCause();
        }
        return new RequestBodyError("request", "Malformed JSON syntax", "Malformed request body");
    }

    private String jsonPath(List<JsonMappingException.Reference> references) {
        StringBuilder path = new StringBuilder();
        for (JsonMappingException.Reference reference : references) {
            if (reference.getFieldName() != null) {
                if (!path.isEmpty()) path.append('.');
                path.append(reference.getFieldName());
            } else if (reference.getIndex() >= 0) {
                path.append('[').append(reference.getIndex()).append(']');
            }
        }
        return path.toString();
    }

    private record RequestBodyError(String path, String reason, String message) {}

    @ExceptionHandler(AuthenticationException.class)
    public ResponseEntity<Result<Void>> handleAuthenticationException(AuthenticationException e) {
        log.warn("Authentication failed: {}", e.getMessage());
        return ResponseEntity
                .status(HttpStatus.UNAUTHORIZED)
                .body(Result.unauthorized(e.getMessage()));
    }

    @ExceptionHandler(AccessDeniedException.class)
    public ResponseEntity<Result<Void>> handleAccessDeniedException(AccessDeniedException e) {
        log.warn("Access denied: {}", e.getMessage());
        return ResponseEntity
                .status(HttpStatus.FORBIDDEN)
                .body(Result.forbidden(e.getMessage()));
    }

    @ExceptionHandler(EntityNotFoundException.class)
    public ResponseEntity<Result<Void>> handleEntityNotFoundException(EntityNotFoundException e) {
        log.warn("Entity not found: {}", e.getMessage());
        return ResponseEntity
                .status(HttpStatus.NOT_FOUND)
                .body(Result.notFound(e.getMessage()));
    }

    @ExceptionHandler(NoHandlerFoundException.class)
    public ResponseEntity<Result<Void>> handleNoHandlerFoundException(NoHandlerFoundException e) {
        log.warn("Endpoint not found: {}", e.getRequestURL());
        return ResponseEntity
                .status(HttpStatus.NOT_FOUND)
                .body(Result.notFound("Endpoint not found: " + e.getRequestURL()));
    }

    @ExceptionHandler(NoResourceFoundException.class)
    public ResponseEntity<Result<Void>> handleNoResourceFoundException(NoResourceFoundException e) {
        log.warn("Resource not found: {}", e.getResourcePath());
        return ResponseEntity
                .status(HttpStatus.NOT_FOUND)
                .body(Result.notFound("Endpoint not found: " + e.getResourcePath()));
    }

    @ExceptionHandler(IllegalStateException.class)
    public ResponseEntity<Result<Void>> handleIllegalStateException(IllegalStateException e) {
        log.error("IllegalStateException: {}", e.getMessage(), e);
        return ResponseEntity
                .status(HttpStatus.INTERNAL_SERVER_ERROR)
                .body(Result.error(500, "Internal server error"));
    }

    @ExceptionHandler(DataIntegrityViolationException.class)
    public ResponseEntity<Result<Void>> handleDataIntegrityViolation(DataIntegrityViolationException e) {
        log.warn("Data integrity violation: {}", e.getMessage());
        return ResponseEntity
                .status(HttpStatus.CONFLICT)
                .body(Result.conflict("Data conflict, the resource may already exist"));
    }

    @ExceptionHandler(RuntimeException.class)
    public ResponseEntity<Result<Void>> handleRuntimeException(RuntimeException e) {
        log.error("Internal server error", e);
        return ResponseEntity
                .status(HttpStatus.INTERNAL_SERVER_ERROR)
                .body(Result.error("Internal server error"));
    }

    @ExceptionHandler(Exception.class)
    public ResponseEntity<Result<Void>> handleException(Exception e) {
        log.error("Unexpected error: {} - {}", e.getClass().getName(), e.getMessage(), e);
        return ResponseEntity
                .status(HttpStatus.INTERNAL_SERVER_ERROR)
                .body(Result.error("Internal server error"));
    }

    @ExceptionHandler(Throwable.class)
    public ResponseEntity<Result<Void>> handleThrowable(Throwable e) {
        log.error("Unhandled Throwable: {} - {}", e.getClass().getName(), e.getMessage(), e);
        return ResponseEntity
                .status(HttpStatus.INTERNAL_SERVER_ERROR)
                .body(Result.error("Internal server error"));
    }
}

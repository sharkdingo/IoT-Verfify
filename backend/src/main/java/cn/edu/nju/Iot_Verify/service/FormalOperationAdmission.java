package cn.edu.nju.Iot_Verify.service;

import lombok.RequiredArgsConstructor;
import org.springframework.stereotype.Component;

import java.util.Objects;
import java.util.function.Supplier;

/** Single admission boundary for synchronous verification, simulation, and fix work. */
@Component
@RequiredArgsConstructor
public class FormalOperationAdmission {

    private final UserOperationGuard userOperationGuard;

    public <T> T execute(Long userId, Supplier<T> operation) {
        Objects.requireNonNull(operation, "operation must not be null");
        try (var lease = userOperationGuard.acquire(
                userId, UserOperationGuard.Kind.FORMAL, 1, userOperationGuard.renewableLeaseTtl())) {
            lease.requireActive();
            T result = operation.get();
            lease.requireActive();
            return result;
        }
    }
}

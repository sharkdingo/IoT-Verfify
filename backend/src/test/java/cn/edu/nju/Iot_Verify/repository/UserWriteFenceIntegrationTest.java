package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.dto.board.EnvironmentVariableUpdateRequestDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.exception.EnvironmentVariableConflictException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.po.BoardEnvironmentVariableId;
import cn.edu.nju.Iot_Verify.po.BoardEnvironmentVariablePo;
import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.service.FormalOperationAdmission;
import cn.edu.nju.Iot_Verify.service.FormalOperationFence;
import cn.edu.nju.Iot_Verify.service.UserOperationGuard;
import cn.edu.nju.Iot_Verify.service.impl.BoardStorageServiceImpl;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceNodeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceTemplateMapper;
import cn.edu.nju.Iot_Verify.util.mapper.RuleMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.jdbc.AutoConfigureTestDatabase;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;
import org.springframework.transaction.PlatformTransactionManager;
import org.springframework.transaction.annotation.Propagation;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.transaction.support.TransactionTemplate;

import java.time.Duration;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicLong;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.AdditionalAnswers.delegatesTo;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.ArgumentMatchers.nullable;
import static org.mockito.Mockito.doAnswer;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@DataJpaTest(properties = {
        "spring.jpa.database-platform=org.hibernate.dialect.H2Dialect",
        "spring.jpa.properties.hibernate.dialect=org.hibernate.dialect.H2Dialect",
        "spring.jpa.hibernate.ddl-auto=create-drop"
})
@AutoConfigureTestDatabase(replace = AutoConfigureTestDatabase.Replace.ANY)
@Transactional(propagation = Propagation.NOT_SUPPORTED)
class UserWriteFenceIntegrationTest {

    private static final long COORDINATION_TIMEOUT_SECONDS = 10;
    private static final long LOCK_OBSERVATION_MILLIS = 500;

    @Autowired
    private UserRepository users;

    @Autowired
    private DeviceNodeRepository nodes;

    @Autowired
    private DeviceTemplateRepository templates;

    @Autowired
    private BoardEnvironmentVariableRepository environment;

    @Autowired
    private PlatformTransactionManager transactionManager;

    // This class runs with Propagation.NOT_SUPPORTED so its saveAndFlush calls COMMIT rather than
    // roll back. All @DataJpaTest classes share one cached H2 context, so leftover committed rows
    // would leak into sibling repository tests (order-dependent, CI-only). Delete what we commit.
    @AfterEach
    void clearCommittedRows() {
        new TransactionTemplate(transactionManager).executeWithoutResult(status -> {
            environment.deleteAllInBatch();
            nodes.deleteAllInBatch();
            templates.deleteAllInBatch();
            users.deleteAllInBatch();
        });
    }

    @Test
    void independentBoardServicesSerializeThenRejectTheStaleCas() throws Exception {
        Long userId = saveUser("board-cas-user", "13800000001");
        saveFiniteEnvironmentBoard(userId, "old");

        CountDownLatch winnerLocked = new CountDownLatch(1);
        CountDownLatch releaseWinner = new CountDownLatch(1);
        CountDownLatch loserCallingDatabaseLock = new CountDownLatch(1);
        UserRepository winnerUsers = mock(UserRepository.class, delegatesTo(users));
        UserRepository loserUsers = mock(UserRepository.class, delegatesTo(users));
        doAnswer(invocation -> {
            var locked = users.findByIdForUpdate(invocation.getArgument(0));
            winnerLocked.countDown();
            await(releaseWinner);
            return locked;
        }).when(winnerUsers).findByIdForUpdate(userId);
        doAnswer(invocation -> {
            loserCallingDatabaseLock.countDown();
            return users.findByIdForUpdate(invocation.getArgument(0));
        }).when(loserUsers).findByIdForUpdate(userId);

        BoardStorageServiceImpl winnerService = boardServiceInstance(winnerUsers);
        BoardStorageServiceImpl loserService = boardServiceInstance(loserUsers);
        ExecutorService executor = Executors.newFixedThreadPool(2);
        Future<?> winner = executor.submit(() -> winnerService.saveEnvironmentVariables(
                userId, List.of(environmentUpdate("old", "winner"))));

        try {
            await(winnerLocked);
            Future<?> loser = executor.submit(() -> loserService.saveEnvironmentVariables(
                    userId, List.of(environmentUpdate("old", "loser"))));
            await(loserCallingDatabaseLock);

            assertThrows(TimeoutException.class,
                    () -> loser.get(LOCK_OBSERVATION_MILLIS, TimeUnit.MILLISECONDS),
                    "The second service must remain blocked while the first transaction owns the user row");

            releaseWinner.countDown();
            winner.get(COORDINATION_TIMEOUT_SECONDS, TimeUnit.SECONDS);
            ExecutionException failure = assertThrows(
                    ExecutionException.class,
                    () -> loser.get(COORDINATION_TIMEOUT_SECONDS, TimeUnit.SECONDS));
            EnvironmentVariableConflictException conflict = findCause(
                    failure, EnvironmentVariableConflictException.class);

            assertEquals("winner", conflict.getCurrentVariable().getValue());
            assertEquals("winner", inTransaction(() -> environment.findById(
                    new BoardEnvironmentVariableId("signal", userId)).orElseThrow().getValue()));
            verify(winnerUsers, times(1)).findByIdForUpdate(userId);
            verify(loserUsers, times(1)).findByIdForUpdate(userId);
        } finally {
            releaseWinner.countDown();
            executor.shutdownNow();
            assertTrue(executor.awaitTermination(COORDINATION_TIMEOUT_SECONDS, TimeUnit.SECONDS));
        }
    }

    @Test
    void staleFormalEpochInBeforeCommitRollsBackAFlushedBusinessWrite() {
        Long userId = saveUser("fence-user", "13800000002");
        FormalOperationFence fence = new FormalOperationFence(users, transactionManager);
        UserOperationGuard guard = mock(UserOperationGuard.class);
        UserOperationGuard.Lease lease = mock(UserOperationGuard.Lease.class);
        when(guard.acquire(
                eq(userId), eq(UserOperationGuard.Kind.FORMAL), eq(1), nullable(Duration.class)))
                .thenReturn(lease);
        FormalOperationAdmission admission = new FormalOperationAdmission(guard, fence);
        AtomicLong supersedingEpoch = new AtomicLong();
        String businessName = "fenced_signal";
        BoardEnvironmentVariableId businessId = new BoardEnvironmentVariableId(businessName, userId);

        ServiceUnavailableException failure = assertThrows(
                ServiceUnavailableException.class,
                () -> admission.execute(userId, () -> inTransaction(() -> {
                    admission.registerCurrentLeaseCommitFence();
                    environment.saveAndFlush(BoardEnvironmentVariablePo.builder()
                            .name(businessName)
                            .userId(userId)
                            .value("pending")
                            .trust("trusted")
                            .privacy("public")
                            .build());
                    supersedingEpoch.set(fence.claim(userId));
                    return null;
                })));

        assertTrue(failure.getMessage().contains("ownership changed"));
        assertFalse(inTransaction(() -> environment.findById(businessId).isPresent()));
        assertEquals(supersedingEpoch.get(), inTransaction(() -> users.findById(userId).orElseThrow()
                .getFormalOperationFence()));
        verify(lease, times(2)).requireActive();
        verify(lease).close();
    }

    private EnvironmentVariableUpdateRequestDto environmentUpdate(String expectedValue, String desiredValue) {
        return new EnvironmentVariableUpdateRequestDto(
                "signal",
                new EnvironmentVariableUpdateRequestDto.ExpectedValue(
                        expectedValue, "untrusted", "public"),
                new EnvironmentVariableUpdateRequestDto.DesiredPatch(
                        desiredValue, null, null));
    }

    private Long saveUser(String username, String phone) {
        return inTransaction(() -> users.saveAndFlush(UserPo.builder()
                .username(username)
                .phone(phone)
                .password("encoded-password")
                .build()).getId());
    }

    private void saveFiniteEnvironmentBoard(Long userId, String value) {
        inTransaction(() -> {
            DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                    .name("Signal source")
                    .internalVariables(List.of(
                            DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                                    .name("signal")
                                    .isInside(false)
                                    .falsifiableWhenCompromised(false)
                                    .trust("untrusted")
                                    .privacy("public")
                                    .values(List.of("old", "winner", "loser"))
                                    .build()))
                    .build();
            templates.saveAndFlush(DeviceTemplatePo.builder()
                    .userId(userId)
                    .name("Signal source")
                    .manifestJson(JsonUtils.toJson(manifest))
                    .defaultTemplate(false)
                    .build());
            nodes.saveAndFlush(DeviceNodePo.builder()
                    .id("signal_1")
                    .userId(userId)
                    .templateName("Signal source")
                    .label("Signal source")
                    .posX(0.0)
                    .posY(0.0)
                    .state("Working")
                    .width(176)
                    .height(128)
                    .build());
            environment.saveAndFlush(BoardEnvironmentVariablePo.builder()
                    .name("signal")
                    .userId(userId)
                    .value(value)
                    .trust("untrusted")
                    .privacy("public")
                    .build());
            return null;
        });
    }

    private BoardStorageServiceImpl boardServiceInstance(UserRepository userRepository) {
        return new BoardStorageServiceImpl(
                nodes, environment, null, null, null, templates, null,
                new TransactionTemplate(transactionManager), null, null,
                new SpecificationMapper(), new RuleMapper(), new DeviceNodeMapper(), null,
                new DeviceTemplateMapper(), null, userRepository, null);
    }

    private <T> T inTransaction(java.util.function.Supplier<T> action) {
        return new TransactionTemplate(transactionManager).execute(status -> action.get());
    }

    private void await(CountDownLatch latch) {
        try {
            if (!latch.await(COORDINATION_TIMEOUT_SECONDS, TimeUnit.SECONDS)) {
                throw new IllegalStateException("Timed out waiting for test coordination");
            }
        } catch (InterruptedException exception) {
            Thread.currentThread().interrupt();
            throw new IllegalStateException("Interrupted while coordinating test", exception);
        }
    }

    private <T extends Throwable> T findCause(Throwable failure, Class<T> expectedType) {
        Throwable current = failure;
        while (current != null) {
            if (expectedType.isInstance(current)) {
                return expectedType.cast(current);
            }
            current = current.getCause();
        }
        throw new AssertionError("Expected cause " + expectedType.getSimpleName(), failure);
    }
}

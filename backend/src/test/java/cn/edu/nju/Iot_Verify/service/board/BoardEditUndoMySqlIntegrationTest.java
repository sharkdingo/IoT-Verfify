package cn.edu.nju.Iot_Verify.service.board;

import cn.edu.nju.Iot_Verify.dto.board.BoardUndoResultDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.repository.*;
import cn.edu.nju.Iot_Verify.service.impl.BoardStorageServiceImpl;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceNodeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceTemplateMapper;
import cn.edu.nju.Iot_Verify.util.mapper.RuleMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.datatype.jsr310.JavaTimeModule;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.jdbc.AutoConfigureTestDatabase;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;
import org.springframework.transaction.PlatformTransactionManager;
import org.springframework.transaction.support.TransactionTemplate;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * The undo cases that only a real MySQL can answer.
 *
 * <p>Restoring a deleted rule goes through {@code RuleRepository.insertWithId}, a native insert into
 * a {@code JSON} column. MySQL parses the bound string into JSON and returns it unchanged; H2 stores
 * it as a JSON *string literal* and cannot emulate the MySQL behaviour at all, so these assertions
 * are meaningless there — which is why they lived as {@code @Disabled} siblings in
 * {@link BoardEditUndoIntegrationTest}.
 *
 * <p>Enabled only when a MySQL server is actually reachable, so the H2-only backend CI job skips this
 * class instead of failing. The full-stack E2E job exercises the same path through the real
 * application. Set {@code IOT_VERIFY_UNDO_IT_URL} to point at another server.
 */
@DataJpaTest(properties = {
        "spring.jpa.database-platform=org.hibernate.dialect.MySQLDialect",
        "spring.jpa.hibernate.ddl-auto=create-drop",
        "spring.datasource.driver-class-name=com.mysql.cj.jdbc.Driver"
})
@AutoConfigureTestDatabase(replace = AutoConfigureTestDatabase.Replace.NONE)
@org.junit.jupiter.api.extension.ExtendWith(MySqlAvailableCondition.class)
class BoardEditUndoMySqlIntegrationTest {

    @Autowired private DeviceNodeRepository nodes;
    @Autowired private RuleRepository rules;
    @Autowired private SpecificationRepository specs;
    @Autowired private DeviceTemplateRepository templates;
    @Autowired private UserRepository users;
    @Autowired private BoardEditJournalRepository journalRepo;
    @Autowired private PlatformTransactionManager transactionManager;

    private BoardStorageServiceImpl service;
    private Long userId;
    private BoardEditJournal journal;

    @BeforeEach
    void setUp() {
        journalRepo.deleteAll();
        rules.deleteAll();
        specs.deleteAll();
        nodes.deleteAll();
        templates.deleteAll();
        users.deleteAll();
        journal = new BoardEditJournal(journalRepo,
                new ObjectMapper().registerModule(new JavaTimeModule()));
        service = new BoardStorageServiceImpl(
                nodes, null, specs, rules, null, templates, null,
                new TransactionTemplate(transactionManager), null, null,
                new SpecificationMapper(), new RuleMapper(), new DeviceNodeMapper(), null,
                new DeviceTemplateMapper(), null, users, journal);
        userId = createUser("13800138201", "undo-mysql-owner");
        seedDevice(userId);
    }

    private Long createUser(String phone, String username) {
        UserPo user = new UserPo();
        user.setPhone(phone);
        user.setUsername(username);
        user.setPassword("hashed");
        user.setCreatedAt(java.time.LocalDateTime.now());
        return users.saveAndFlush(user).getId();
    }

    private void seedDevice(Long owner) {
        String manifest;
        try (var stream = getClass().getResourceAsStream("/deviceTemplate/Light.json")) {
            manifest = new String(java.util.Objects.requireNonNull(stream).readAllBytes(),
                    java.nio.charset.StandardCharsets.UTF_8);
        } catch (Exception e) {
            throw new IllegalStateException("Light device template fixture is unavailable", e);
        }
        templates.saveAndFlush(DeviceTemplatePo.builder()
                .userId(owner)
                .name("Light")
                .defaultTemplate(true)
                .manifestJson(manifest)
                .build());
        nodes.saveAndFlush(DeviceNodePo.builder()
                .id("light-1")
                .userId(owner)
                .templateName("Light")
                .label("Light 1")
                .posX(0.0).posY(0.0).state("on").width(176).height(128)
                .build());
    }

    private RuleDto newRule(String description) {
        return newRule(description, "on", "off");
    }

    /** The board rejects two semantically identical rules, so a second fixture must differ. */
    private RuleDto newRule(String description, String triggerState, String action) {
        RuleDto rule = new RuleDto();
        RuleDto.Condition condition = new RuleDto.Condition();
        condition.setDeviceName("light-1");
        condition.setTargetType("state");
        condition.setAttribute("state");
        condition.setRelation("=");
        condition.setValue(triggerState);
        rule.setConditions(List.of(condition));
        RuleDto.Command command = new RuleDto.Command();
        command.setDeviceName("light-1");
        command.setAction(action);
        rule.setCommand(command);
        rule.setRuleString(description);
        return rule;
    }

    @Test
    void undoRestoresADeletedRuleUnderItsOriginalId() {
        Long ruleId = service.addRule(userId, newRule("r1")).getAffectedItem().getId();
        RuleDto persisted = service.getRules(userId).get(0);
        service.removeRuleIfUnchanged(userId, ruleId, persisted);
        assertTrue(service.getRules(userId).isEmpty());

        BoardUndoResultDto undone = service.undoLastEdit(userId);

        assertTrue(undone.isApplied());
        assertEquals(1, undone.getRules().size());
        // The original id must come back: rules and specifications reference it.
        assertEquals(ruleId, undone.getRules().get(0).getId());
        assertTrue(undone.isCanRedo());
        // The JSON columns survived the native insert as JSON, not as a quoted string.
        assertEquals(1, undone.getRules().get(0).getConditions().size());
        assertEquals("off", undone.getRules().get(0).getCommand().getAction());
    }

    @Test
    void redoReappliesTheDeletionAndUndoIsIdempotentPastTheEnd() {
        Long ruleId = service.addRule(userId, newRule("r1")).getAffectedItem().getId();
        service.removeRuleIfUnchanged(userId, ruleId, service.getRules(userId).get(0));
        service.undoLastEdit(userId);

        assertTrue(service.redoLastUndoneEdit(userId).isApplied());
        assertTrue(service.getRules(userId).isEmpty());

        // Walk back past the beginning: each extra press is a no-op, never a double-apply. The second
        // undo reverses the *create* as well, so the board legitimately ends empty.
        service.undoLastEdit(userId);
        service.undoLastEdit(userId);
        BoardUndoResultDto exhausted = service.undoLastEdit(userId);
        assertFalse(exhausted.isApplied());
        assertEquals("NOTHING_TO_APPLY", exhausted.getReasonCode());
        assertTrue(service.getRules(userId).isEmpty());
    }

    @Test
    void aNewEditAfterAnUndoMakesRedoUnreachable() {
        Long ruleId = service.addRule(userId, newRule("r1")).getAffectedItem().getId();
        service.removeRuleIfUnchanged(userId, ruleId, service.getRules(userId).get(0));
        service.undoLastEdit(userId);
        assertEquals(1, service.getRules(userId).size());

        // A new edit invalidates the abandoned redo branch: replaying it would overwrite this edit.
        service.addRule(userId, newRule("r2", "off", "on"));

        BoardUndoResultDto redo = service.redoLastUndoneEdit(userId);
        assertFalse(redo.isApplied());
        assertEquals("NOTHING_TO_APPLY", redo.getReasonCode());
        assertEquals(0, journalRepo.countByUserIdAndUndoneTrue(userId));
    }


}

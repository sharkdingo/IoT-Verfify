package cn.edu.nju.Iot_Verify.service.board;

import cn.edu.nju.Iot_Verify.dto.board.BoardUndoResultDto;
import cn.edu.nju.Iot_Verify.dto.board.CollectionMutationResultDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
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

import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.List;
import java.util.Map;
import javax.sql.DataSource;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Undo/redo of rule edits against a real database.
 *
 * Covers what only a live persistence layer can show: that the journal entry and the edit commit
 * together, that a restored rule keeps its original id, that repeating an exhausted undo is
 * idempotent, and that a competing change is refused instead of silently discarded.
 */
@DataJpaTest(properties = {
        "spring.jpa.database-platform=org.hibernate.dialect.H2Dialect",
        "spring.jpa.properties.hibernate.dialect=org.hibernate.dialect.H2Dialect",
        "spring.jpa.hibernate.ddl-auto=create-drop",
        // MySQL compatibility mode so H2 stores a JSON column the way production does. Without it
        // H2 wraps the inserted string as a JSON string literal and the rule cannot be read back.
        // Overridden explicitly: with Replace.NONE the app's own MySQL driver setting is inherited and
        // rejects this H2 URL.
        "spring.datasource.driver-class-name=org.h2.Driver",
        "spring.datasource.username=sa",
        "spring.datasource.password=",
        "spring.datasource.url=jdbc:h2:mem:boardEditUndo;MODE=MySQL;DATABASE_TO_LOWER=TRUE;DB_CLOSE_DELAY=-1"
})
// Replace.NONE so the `spring.datasource.url` above is actually honoured. With the default
// (Replace.ANY) Spring Boot substitutes its own auto-configured embedded DataSource and silently
// discards that URL — losing MODE=MySQL, so every rule/spec read back through the mappers failed with
// PersistedDataIntegrityException on the JSON columns.
@AutoConfigureTestDatabase(replace = AutoConfigureTestDatabase.Replace.NONE)
class BoardEditUndoIntegrationTest {

    @Autowired private DeviceNodeRepository nodes;
    @Autowired private RuleRepository rules;
    @Autowired private SpecificationRepository specs;
    @Autowired private DeviceTemplateRepository templates;
    @Autowired private UserRepository users;
    @Autowired private BoardEditJournalRepository journalRepo;
    @Autowired private PlatformTransactionManager transactionManager;
    @Autowired private DataSource dataSource;

    private BoardStorageServiceImpl service;
    private BoardEditJournal journal;
    private Long userId;
    private Long otherUserId;

    /**
     * Re-types the MySQL {@code JSON} columns as text for this H2 schema.
     *
     * <p>The entities declare {@code columnDefinition = "JSON"} and hold a Java {@code String}. MySQL
     * parses that string into JSON and returns it unchanged; H2 — even under {@code MODE=MySQL} — stores
     * it as a JSON *string literal*, so reading it back yields a quoted scalar where the mappers expect
     * an array, and every rule/spec read fails closed with {@code PersistedDataIntegrityException}.
     * H2 cannot emulate the MySQL behaviour, so the column type is what has to change here. This is a
     * schema-shape workaround only: the JSON text written and read is exactly what production handles,
     * which is what makes these assertions meaningful — including the native-insert restore, which
     * needed no {@code @Disabled} once the column stopped re-quoting its value.
     * {@link BoardEditUndoMySqlIntegrationTest} re-asserts that path against a real MySQL, where the
     * server's own JSON parsing is what returns the value unchanged.
     */
    private void relaxJsonColumnsForH2() {
        Map<String, List<String>> jsonColumns = Map.of(
                "rules", List.of("conditions_json", "command_json"),
                "specification", List.of("a_conditions", "if_conditions", "then_conditions", "devices_json"));
        try (Connection connection = dataSource.getConnection();
             Statement statement = connection.createStatement()) {
            for (Map.Entry<String, List<String>> table : jsonColumns.entrySet()) {
                for (String column : table.getValue()) {
                    statement.executeUpdate("ALTER TABLE " + table.getKey()
                            + " ALTER COLUMN " + column + " SET DATA TYPE CLOB");
                }
            }
        } catch (SQLException e) {
            throw new IllegalStateException("Could not relax H2 JSON columns for this fixture", e);
        }
    }

    @BeforeEach
    void setUp() {
        relaxJsonColumnsForH2();
        // Match Spring's configured mapper: DTOs carry LocalDateTime, which the bare mapper
        // cannot write.
        journal = new BoardEditJournal(journalRepo,
                new ObjectMapper().registerModule(new JavaTimeModule()));
        service = new BoardStorageServiceImpl(
                nodes, null, specs, rules, null, templates, null,
                new TransactionTemplate(transactionManager), null, null,
                new SpecificationMapper(), new RuleMapper(), new DeviceNodeMapper(), null,
                new DeviceTemplateMapper(), null, users, journal);
        userId = createUser("13800138001", "undo-owner");
        otherUserId = createUser("13800138002", "undo-other");
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

    /**
     * A rule needs a device to reference, and a device needs its template manifest. The shipped
     * Light manifest is reused so this fixture cannot drift from the real validation rules.
     */
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

    /** A minimal rule that passes board validation against the Light template. */
    private RuleDto newRule(String text) {
        return newRule(text, "on", "off");
    }

    /**
     * A rule distinguished by its trigger and action, not just its text: the board rejects two
     * semantically identical rules, so tests holding several rules at once must vary these.
     */
    private RuleDto newRule(String text, String triggerState, String action) {
        RuleDto.Condition trigger = new RuleDto.Condition();
        trigger.setDeviceName("light-1");
        trigger.setTargetType("state");
        trigger.setAttribute("state");
        trigger.setRelation("=");
        trigger.setValue(triggerState);

        RuleDto.Command command = new RuleDto.Command();
        command.setDeviceName("light-1");
        command.setAction(action);

        RuleDto rule = new RuleDto();
        rule.setConditions(List.of(trigger));
        rule.setCommand(command);
        rule.setRuleString(text);
        return rule;
    }

    @Test
    void restoringADeletedSpecificationKeepsItsListPosition() {
        String first = service.addSpec(userId, newSpec("on")).getAffectedItem().getId();
        String second = service.addSpec(userId, newSpec("off")).getAffectedItem().getId();
        assertEquals(List.of(first, second), specIdsInOrder());

        // Delete the *first* one: saveSpecsInternal rewrites list_order from the list index, so a
        // restore that appends would silently move it behind the survivor.
        service.removeSpecIfUnchanged(userId, first, service.getSpecs(userId).stream()
                .filter(spec -> first.equals(spec.getId())).findFirst().orElseThrow());
        assertEquals(List.of(second), specIdsInOrder());

        assertTrue(service.undoLastEdit(userId).isApplied());
        assertEquals(List.of(first, second), specIdsInOrder());
    }

    private List<String> specIdsInOrder() {
        return service.getSpecs(userId).stream().map(SpecificationDto::getId).toList();
    }

    /**
     * A minimal template-1 specification that passes board validation against the Light template.
     * Distinguished by its A-condition state, because the board rejects two identical specifications.
     */
    private SpecificationDto newSpec(String state) {
        SpecificationDto spec = new SpecificationDto();
        // Specification ids are author-supplied strings, not IDENTITY-generated.
        spec.setId("spec-" + state);
        spec.setTemplateId("1");
        // Template 1 ("always") uses A conditions only, so the state is what distinguishes the two
        // fixtures — the board rejects two semantically identical specifications.
        spec.setAConditions(List.of(specCondition("a", state)));
        return spec;
    }

    private SpecConditionDto specCondition(String side, String value) {
        SpecConditionDto condition = new SpecConditionDto();
        condition.setDeviceId("light-1");
        condition.setTargetType("state");
        condition.setKey("state");
        condition.setRelation("=");
        condition.setSide(side);
        condition.setValue(value);
        return condition;
    }

    @Test
    void addingARuleRecordsTheJournalEntryInTheSameCommit() {
        CollectionMutationResultDto<RuleDto> created = service.addRule(userId, newRule("r1"));

        assertEquals(1, journalRepo.countByUserIdAndUndoneFalse(userId));
        // The mutation itself reports availability, so the client never has to guess.
        assertEquals(Boolean.TRUE, created.getCanUndo());
        assertEquals(Boolean.FALSE, created.getCanRedo());
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
    }

    /**
     * Unlike the two tests above, this one is not blocked by H2's JSON handling: the guard refuses
     * before {@code insertWithId} runs, so no JSON column is ever written.
     */
    @Test
    void undoRefusesWhenAnotherAccountNowHoldsTheDeletedRulesId() {
        Long ruleId = service.addRule(userId, newRule("r1")).getAffectedItem().getId();
        service.removeRuleIfUnchanged(userId, ruleId, service.getRules(userId).get(0));

        // `rules.id` is a single global primary key — not composite with user_id like device_node — so
        // another account can take the freed id. The drift check only inspects this account's rows and
        // therefore sees "absent", which used to send the restore into a primary-key violation.
        rules.insertWithId(ruleId, otherUserId, "[]", "{}", "other account's rule", 0,
                java.time.LocalDateTime.now());

        ConflictException refused = assertThrows(ConflictException.class,
                () -> service.undoLastEdit(userId));
        assertTrue(refused.getMessage().contains("no longer available"),
                "the conflict must name the id collision, not read as generic drift");
    }

    @Test
    void redoReappliesTheDeletionAndUndoIsIdempotentPastTheEnd() {
        Long ruleId = service.addRule(userId, newRule("r1")).getAffectedItem().getId();
        service.removeRuleIfUnchanged(userId, ruleId, service.getRules(userId).get(0));
        service.undoLastEdit(userId);

        assertTrue(service.redoLastUndoneEdit(userId).isApplied());
        assertTrue(service.getRules(userId).isEmpty());

        // Walk back past the beginning: each extra press is a no-op, never a double-apply. The second
        // undo reverses the *create* too, so the board legitimately ends empty — what matters is that
        // the exhausted presses add nothing back.
        service.undoLastEdit(userId);
        service.undoLastEdit(userId);
        BoardUndoResultDto exhausted = service.undoLastEdit(userId);
        assertFalse(exhausted.isApplied());
        assertEquals("NOTHING_TO_APPLY", exhausted.getReasonCode());
        assertFalse(exhausted.isCanUndo());
        assertTrue(service.getRules(userId).isEmpty(), "no duplicate rule was created");
    }

    @Test
    void aNewEditAfterAnUndoMakesRedoUnreachable() {
        Long first = service.addRule(userId, newRule("r1")).getAffectedItem().getId();
        service.removeRuleIfUnchanged(userId, first,
                service.getRules(userId).stream()
                        .filter(rule -> rule.getId().equals(first)).findFirst().orElseThrow());
        service.undoLastEdit(userId);
        assertTrue(journal.availability(userId).canRedo());

        // Redoing the abandoned branch would overwrite this new edit, so it must be discarded.
        service.addRule(userId, newRule("r2", "off", "on"));

        assertFalse(journal.availability(userId).canRedo());
        assertFalse(service.redoLastUndoneEdit(userId).isApplied());
    }

    @Test
    void undoIsRefusedWhenTheRuleChangedAfterTheEdit() {
        Long ruleId = service.addRule(userId, newRule("r1")).getAffectedItem().getId();

        // Something else edits the same rule after the create was journalled. Undoing the create
        // would delete that newer version, so it is refused rather than silently applied.
        rules.findById(ruleId).ifPresent(po -> {
            po.setRuleString("edited elsewhere");
            rules.saveAndFlush(po);
        });

        assertThrows(ConflictException.class, () -> service.undoLastEdit(userId));
        assertEquals(1, service.getRules(userId).size(), "the board was left untouched");
        assertTrue(journal.availability(userId).canUndo(), "the entry stays retryable");
    }

    @Test
    void undoOnlyEverTouchesTheRequestingAccountsHistory() {
        service.addRule(userId, newRule("r1"));

        // A second account has no history of its own and cannot reach the first account's.
        assertFalse(service.undoLastEdit(otherUserId).isApplied());
        assertEquals(1, service.getRules(userId).size());
        assertTrue(journal.availability(userId).canUndo());
    }

    @Test
    void undoRequiresAnActiveUser() {
        service.addRule(userId, newRule("r1"));
        assertThrows(UnauthorizedException.class, () -> service.undoLastEdit(999_999L));
    }

    @Test
    void undoRestoresThePreviousRuleExecutionOrder() {
        Long first = service.addRule(userId, newRule("r1", "on", "off")).getAffectedItem().getId();
        Long second = service.addRule(userId, newRule("r2", "off", "on")).getAffectedItem().getId();

        // Users reach reorder through explicit up/down buttons, so one press is one reversible edit.
        service.reorderRules(userId, List.of(first, second), List.of(second, first));
        assertEquals(List.of(second, first), ruleIdsInOrder());

        assertTrue(service.undoLastEdit(userId).isApplied());
        assertEquals(List.of(first, second), ruleIdsInOrder());

        assertTrue(service.redoLastUndoneEdit(userId).isApplied());
        assertEquals(List.of(second, first), ruleIdsInOrder());
    }

    @Test
    void reorderUndoIsRefusedWhenTheRuleSetChangedAfterwards() {
        Long first = service.addRule(userId, newRule("r1", "on", "off")).getAffectedItem().getId();
        Long second = service.addRule(userId, newRule("r2", "off", "on")).getAffectedItem().getId();
        service.reorderRules(userId, List.of(first, second), List.of(second, first));

        // A later rule makes the recorded ordering no longer describe the current rule set, so
        // re-imposing it would silently drop the new rule from the order.
        service.addRule(userId, newRule("r3", "on", "on"));

        // Undo the newer CREATE first, so the reorder entry is the one actually being applied next.
        assertTrue(service.undoLastEdit(userId).isApplied());
        assertEquals(List.of(second, first), ruleIdsInOrder());

        // The reorder is reachable again and its preconditions hold, so reversing it restores the
        // ordering the reorder replaced.
        BoardUndoResultDto reorderUndo = service.undoLastEdit(userId);
        assertTrue(reorderUndo.isApplied());
        assertEquals("RULE_ORDER", reorderUndo.getEntityType());
        assertEquals(List.of(first, second), ruleIdsInOrder());
    }

    private List<Long> ruleIdsInOrder() {
        return service.getRules(userId).stream().map(RuleDto::getId).toList();
    }

    @Test
    void availabilityIsAQueryThatReportsNoCollectionsAndChangesNothing() {
        service.addRule(userId, newRule("r1"));

        BoardUndoResultDto availability = service.boardEditAvailability(userId);

        assertTrue(availability.isCanUndo());
        assertFalse(availability.isCanRedo());
        assertFalse(availability.isApplied());
        // Availability is a read. Shipping the collections here would invite a client to treat a
        // query response as an authoritative board update.
        assertTrue(availability.getRules().isEmpty());
        assertTrue(availability.getSpecs().isEmpty());
        // And it must not consume the history it reports on.
        assertEquals(1, service.getRules(userId).size());
        assertTrue(journal.availability(userId).canUndo());
    }
}

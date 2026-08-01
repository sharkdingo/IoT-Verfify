import assert from 'node:assert/strict';
import { test } from 'node:test';
import { route } from './ci-risk-router.mjs';

/**
 * Routing decides whether a change is allowed to reach main without full validation, so a wrong
 * answer here is not a slow pipeline — it is an unverified release. These tests pin the two
 * directions that matter: cheap changes must stay cheap, and risky changes must escalate no matter
 * how small they are.
 */

test('documentation-only changes run nothing', () => {
  for (const paths of [
    ['README.md'],
    ['docs/architecture/shared-value-semantics.md'],
    ['CHANGELOG.md', 'docs/README.md', 'backend/README.md'],
    ['docs/examples/screenshot.png'],
    ['.gitignore'],
  ]) {
    const decision = route(paths, { ref: 'refs/heads/feature/x' });
    assert.equal(decision.inertOnly, true, `expected inert: ${paths}`);
    assert.equal(decision.fast, false);
    assert.equal(decision.full, false);
  }
});

test('an ordinary source change runs fast CI only', () => {
  const decision = route(
    ['frontend/src/components/DeviceDialog.vue', 'frontend/src/assets/i18n.ts'],
    { ref: 'refs/heads/feature/x' },
  );
  assert.equal(decision.fast, true);
  assert.equal(decision.full, false, 'a UI component tweak should not need the full E2E suite');
  assert.equal(decision.frontend, true);
  assert.equal(decision.backend, false, 'no backend tree touched');
});

test('a single high-risk line escalates to full CI regardless of diff size', () => {
  const cases = [
    ['backend/src/main/java/cn/edu/nju/Iot_Verify/component/nusmv/generator/module/SmvMainModuleBuilder.java', 'NuSMV model generation'],
    ['backend/src/main/java/cn/edu/nju/Iot_Verify/component/fuzz/FuzzModel.java', 'bounded exploration engine'],
    ['backend/device-template-schema.json', 'template schema is the authoring contract'],
    ['backend/src/main/resources/deviceTemplate/Light.json', 'bundled template semantics'],
    ['backend/src/main/java/cn/edu/nju/Iot_Verify/security/JwtAuthFilter.java', 'security filters'],
    ['backend/src/main/resources/db/migration/V9__add_column.sql', 'database migrations'],
    ['backend/src/main/java/cn/edu/nju/Iot_Verify/po/UserPo.java', 'persistence mapping'],
    ['backend/src/main/java/cn/edu/nju/Iot_Verify/dto/verification/VerificationRequestDto.java', 'REST/DTO contract'],
    ['backend/src/main/java/cn/edu/nju/Iot_Verify/controller/VerificationController.java', 'REST surface'],
    ['frontend/src/stores/board.ts', 'cross-cutting frontend state/routing'],
    ['frontend/src/api/verify.ts', 'frontend API client contract'],
    ['frontend/src/utils/modelRequest.ts', 'shared model contract'],
    ['.github/workflows/fast-ci.yml', 'CI infrastructure'],
    ['frontend/playwright.config.ts', 'test infrastructure'],
    ['frontend/e2e/board-full-flow.spec.ts', 'E2E harness'],
    ['backend/pom.xml', 'backend dependency graph'],
    ['frontend/package-lock.json', 'frontend dependency graph'],
  ];

  for (const [path, why] of cases) {
    const decision = route([path], { ref: 'refs/heads/feature/x' });
    assert.equal(decision.full, true, `expected full CI for ${path}`);
    assert.ok(decision.reasons.includes(why), `expected reason "${why}" for ${path}, got ${decision.reasons}`);
    assert.equal(decision.backend, true, 'escalation runs both suites');
    assert.equal(decision.frontend, true, 'escalation runs both suites');
  }
});

test('a high-risk path mixed with docs still escalates', () => {
  const decision = route(
    ['README.md', 'backend/src/main/java/cn/edu/nju/Iot_Verify/po/UserPo.java'],
    { ref: 'refs/heads/feature/x' },
  );
  assert.equal(decision.inertOnly, false);
  assert.equal(decision.full, true);
});

test('main, schedule, and manual dispatch always run everything', () => {
  for (const context of [
    { ref: 'refs/heads/main', eventName: 'push' },
    { ref: 'refs/heads/feature/x', eventName: 'schedule' },
    { ref: 'refs/heads/feature/x', eventName: 'workflow_dispatch' },
    { ref: 'refs/heads/feature/x', eventName: 'push', forceFull: true },
  ]) {
    const decision = route(['README.md'], context);
    assert.equal(decision.full, true, `expected full CI for ${JSON.stringify(context)}`);
    assert.equal(decision.fast, true);
    assert.equal(decision.inertOnly, false, 'main must not be short-circuited by a docs-only diff');
  }
});

test('an unrecognised path escalates rather than being silently skipped', () => {
  // A new top-level directory has unknown blast radius. Failing safe costs a slow pipeline; failing
  // open ships something nothing validated.
  const decision = route(['services/new-thing/main.go'], { ref: 'refs/heads/feature/x' });
  assert.equal(decision.full, true);
  assert.ok(decision.reasons.some((r) => r.startsWith('unclassified path')), decision.reasons.join('; '));
});

test('an empty change list still runs fast CI', () => {
  const decision = route([], { ref: 'refs/heads/feature/x' });
  assert.equal(decision.fast, true);
  assert.equal(decision.full, false);
  assert.equal(decision.inertOnly, false);
});

test('backend-only and frontend-only changes scope their suites', () => {
  const backendOnly = route(
    ['backend/src/main/java/cn/edu/nju/Iot_Verify/service/impl/ChatServiceImpl.java'],
    { ref: 'refs/heads/feature/x' },
  );
  assert.equal(backendOnly.backend, true);
  assert.equal(backendOnly.frontend, false);
  assert.equal(backendOnly.full, false);

  const frontendOnly = route(['frontend/src/views/Landing.vue'], { ref: 'refs/heads/feature/x' });
  assert.equal(frontendOnly.frontend, true);
  assert.equal(frontendOnly.backend, false);
  assert.equal(frontendOnly.full, false);
});

test('every high-risk rule states why it is high risk', () => {
  // Without a stated standard the list becomes folklore and nobody can judge an addition.
  const decision = route(['backend/pom.xml'], { ref: 'refs/heads/feature/x' });
  for (const reason of decision.reasons) {
    assert.ok(reason.length > 3, `reason too vague: ${reason}`);
  }
});

package cn.edu.nju.Iot_Verify.component.fuzz;

import cn.edu.nju.Iot_Verify.component.fuzz.paper.PaperEventDomainSnapshot;
import cn.edu.nju.Iot_Verify.component.fuzz.paper.PaperSeed;
import cn.edu.nju.Iot_Verify.component.fuzz.paper.PaperSeedKernel;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzExplorationMode;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.SplittableRandom;
import java.util.function.BooleanSupplier;

/**
 * Pure, bounded search kernel for the finite-trace fuzzing MVP.
 *
 * <p>The engine is stateless. A run consumes one immutable board snapshot and exactly one
 * {@link SplittableRandom}; path evaluation is deterministic and does not read randomness.</p>
 */
@Component
public final class FuzzEngine {

    public static final long MAX_SAFE_SEED = 9_007_199_254_740_991L;
    private static final long SAFE_SEED_MODULUS = MAX_SAFE_SEED + 1L;
    static final int RANDOM_RESTART_INTERVAL = 20;
    static final int PAPER_SOLVER_LEVELS = 3;

    public FuzzEngineResult run(
            FuzzEngineInput input,
            FuzzProgressListener progress,
            BooleanSupplier cancelled) {
        long startedAt = System.nanoTime();
        validateInput(input);
        FuzzEngineConfig config = input.config();
        long effectiveSeed = effectiveSeed(config.seed());
        SplittableRandom random = new SplittableRandom(effectiveSeed);
        BooleanSupplier cancellation = cancelled == null ? () -> false : cancelled;
        ProgressReporter progressReporter = new ProgressReporter(progress);
        List<String> limitations = new ArrayList<>(
                FuzzLimitationContract.requiredCodes(config.explorationMode()));

        Selection selection = selectSpecifications(input.snapshot(), config.targetSpecIds(), limitations);
        UnsupportedReason globalUnsupported = globalUnsupportedReason(input.snapshot());
        FuzzModel model = null;
        PaperEventDomainSnapshot paperEventDomain = null;
        UnsupportedReason modelError = null;
        if (globalUnsupported == null) {
            try {
                model = FuzzModel.from(input.snapshot());
                if (config.explorationMode() == FuzzExplorationMode.PAPER_COMPATIBLE) {
                    paperEventDomain = model.paperEventDomain(config.pathLength());
                }
            } catch (FuzzModel.ModelException exception) {
                modelError = new UnsupportedReason("MODEL_INVALID", exception.getMessage());
            }
        }

        List<FuzzSpecEligibility> eligibility = new ArrayList<>();
        List<SpecificationDto> eligible = new ArrayList<>();
        for (SpecificationDto specification : selection.specifications()) {
            UnsupportedReason reason = globalUnsupported != null
                    ? globalUnsupported
                    : modelError != null ? modelError : eligibilityReason(specification, model);
            boolean supported = reason == null;
            eligibility.add(new FuzzSpecEligibility(
                    specification,
                    supported,
                    supported ? null : reason.code(),
                    supported ? null : reason.message()));
            if (supported) {
                eligible.add(specification);
            }
        }

        if (eligible.isEmpty()) {
            progressReporter.report(100, "No eligible specifications");
            return result(
                    FuzzEngineOutcome.NO_ELIGIBLE_SPECIFICATIONS,
                    effectiveSeed,
                    0,
                    0,
                    startedAt,
                    List.of(),
                    eligibility,
                    limitations);
        }

        if (config.explorationMode() == FuzzExplorationMode.PAPER_COMPATIBLE) {
            return runPaperCompatible(
                    Objects.requireNonNull(model),
                    Objects.requireNonNull(paperEventDomain),
                    config,
                    effectiveSeed,
                    progressReporter,
                    cancellation,
                    eligible,
                    eligibility,
                    limitations,
                    startedAt);
        }

        progressReporter.report(0, "Preparing deterministic population");
        int geneCount = model.geneCount(config.pathLength());
        List<Genome> population = initialPopulation(random, config.populationSize(), geneCount);
        Map<String, FuzzFinding> findings = new LinkedHashMap<>();
        Map<String, CandidateScore> bestBySpecification = new LinkedHashMap<>();
        long generatedPaths = 0;
        int completedIterations = 0;
        boolean wasCancelled = false;

        for (int iteration = 0; iteration < config.maxIterations(); iteration++) {
            if (cancellation.getAsBoolean()) {
                wasCancelled = true;
                break;
            }

            boolean evaluatedAny = false;
            for (Genome genome : population) {
                if (cancellation.getAsBoolean()) {
                    wasCancelled = true;
                    break;
                }

                List<SpecificationDto> unresolvedSpecifications = eligible.stream()
                        .filter(specification -> !findings.containsKey(specification.getId()))
                        .toList();
                if (unresolvedSpecifications.isEmpty()) {
                    break;
                }
                FuzzModel.Simulation simulation = model.simulate(
                        genome.genes(),
                        config.pathLength(),
                        cancellation,
                        unresolvedSpecifications);
                if (simulation.cancelled()) {
                    wasCancelled = true;
                    break;
                }
                generatedPaths++;
                evaluatedAny = true;
                for (SpecificationDto specification : unresolvedSpecifications) {
                    FuzzModel.SpecEvaluation evaluation = model.evaluate(specification, simulation);
                    if (evaluation.violationStep() >= 0) {
                        int endExclusive = evaluation.violationStep() + 1;
                        findings.put(specification.getId(), new FuzzFinding(
                                specification,
                                evaluation.violationStep(),
                                simulation.traceStates().subList(0, endExclusive),
                                simulation.eventsThrough(evaluation.violationStep())));
                        bestBySpecification.remove(specification.getId());
                    } else {
                        CandidateScore previous = bestBySpecification.get(specification.getId());
                        if (previous == null || evaluation.distance() < previous.distance()) {
                            bestBySpecification.put(
                                    specification.getId(),
                                    new CandidateScore(
                                            genome.copy(),
                                            simulation.mutableChoiceBounds(),
                                            evaluation.distance()));
                        }
                    }
                }
                if (findings.size() == eligible.size()) {
                    break;
                }
            }

            if (evaluatedAny) {
                completedIterations = iteration + 1;
            }
            int percent = config.maxIterations() == 0
                    ? 100
                    : Math.min(100, (int) (((long) completedIterations * 100L) / config.maxIterations()));
            progressReporter.report(percent, "Completed fuzz iteration " + completedIterations);
            if (wasCancelled || findings.size() == eligible.size()) {
                break;
            }
            List<CandidateScore> parents = eligible.stream()
                    .filter(specification -> !findings.containsKey(specification.getId()))
                    .map(specification -> bestBySpecification.get(specification.getId()))
                    .filter(Objects::nonNull)
                    .toList();
            population = nextPopulation(
                    random,
                    parents,
                    config.populationSize(),
                    geneCount,
                    iteration + 1);
        }

        FuzzEngineOutcome outcome;
        if (wasCancelled) {
            outcome = FuzzEngineOutcome.CANCELLED;
        } else if (!findings.isEmpty()) {
            outcome = FuzzEngineOutcome.FINDINGS_FOUND;
        } else {
            outcome = FuzzEngineOutcome.BUDGET_EXHAUSTED;
        }
        if (!wasCancelled) {
            progressReporter.report(100, findings.isEmpty() ? "Search budget exhausted" : "Fuzz findings ready");
        }
        return result(
                outcome,
                effectiveSeed,
                completedIterations,
                generatedPaths,
                startedAt,
                new ArrayList<>(findings.values()),
                eligibility,
                limitations);
    }

    private static FuzzEngineResult runPaperCompatible(
            FuzzModel model,
            PaperEventDomainSnapshot eventDomain,
            FuzzEngineConfig config,
            long effectiveSeed,
            ProgressReporter progressReporter,
            BooleanSupplier cancellation,
            List<SpecificationDto> eligible,
            List<FuzzSpecEligibility> eligibility,
            List<String> limitations,
            long startedAt) {
        progressReporter.report(0, "Preparing paper-compatible Event population");
        PaperSeedKernel seedKernel = new PaperSeedKernel(eventDomain, effectiveSeed);
        List<PaperSeed> population = seedKernel.initialPopulation(config.populationSize());
        Map<String, FuzzFinding> findings = new LinkedHashMap<>();
        long generatedPaths = 0;
        int completedIterations = 0;
        boolean wasCancelled = false;

        for (int iteration = 0; iteration < config.maxIterations(); iteration++) {
            if (cancellation.getAsBoolean()) {
                wasCancelled = true;
                break;
            }
            Map<String, PaperCandidateScore> generationBest = new LinkedHashMap<>();
            boolean evaluatedAny = false;
            for (PaperSeed seed : population) {
                if (cancellation.getAsBoolean()) {
                    wasCancelled = true;
                    break;
                }
                List<SpecificationDto> unresolvedSpecifications = eligible.stream()
                        .filter(specification -> !findings.containsKey(specification.getId()))
                        .toList();
                if (unresolvedSpecifications.isEmpty()) {
                    break;
                }
                FuzzModel.Simulation simulation = model.simulatePaperSeed(
                        seed,
                        eventDomain,
                        config.pathLength(),
                        cancellation,
                        unresolvedSpecifications);
                if (simulation.cancelled()) {
                    wasCancelled = true;
                    break;
                }
                generatedPaths++;
                evaluatedAny = true;
                for (SpecificationDto specification : unresolvedSpecifications) {
                    FuzzModel.SpecEvaluation evaluation = model.evaluatePaper(
                            specification,
                            simulation,
                            PAPER_SOLVER_LEVELS);
                    if (evaluation.violationStep() >= 0) {
                        int endExclusive = evaluation.violationStep() + 1;
                        findings.put(specification.getId(), new FuzzFinding(
                                specification,
                                evaluation.violationStep(),
                                simulation.traceStates().subList(0, endExclusive),
                                simulation.eventsThrough(evaluation.violationStep())));
                    } else {
                        PaperCandidateScore previous = generationBest.get(specification.getId());
                        if (previous == null || evaluation.distance() < previous.distance()) {
                            generationBest.put(
                                    specification.getId(),
                                    new PaperCandidateScore(seed, evaluation.distance()));
                        }
                    }
                }
                if (findings.size() == eligible.size()) {
                    break;
                }
            }

            if (evaluatedAny) {
                completedIterations = iteration + 1;
            }
            int percent = Math.min(
                    100,
                    (int) (((long) completedIterations * 100L) / config.maxIterations()));
            progressReporter.report(percent, "Completed paper-compatible fuzz iteration " + completedIterations);
            if (wasCancelled || findings.size() == eligible.size()) {
                break;
            }

            List<PaperSeed> parents = eligible.stream()
                    .filter(specification -> !findings.containsKey(specification.getId()))
                    .map(specification -> generationBest.get(specification.getId()))
                    .filter(Objects::nonNull)
                    .map(PaperCandidateScore::seed)
                    .toList();
            if (parents.isEmpty()) {
                population = seedKernel.initialPopulation(config.populationSize());
            } else {
                List<PaperSeed> next = new ArrayList<>(config.populationSize());
                for (int slot = 0; slot < config.populationSize(); slot++) {
                    int parentIndex = paperParentIndexForSlot(
                            iteration + 1,
                            config.populationSize(),
                            slot,
                            parents.size());
                    PaperSeed parent = parents.get(parentIndex);
                    next.add(seedKernel.nextSeed(parent).seed());
                }
                population = List.copyOf(next);
            }
        }

        FuzzEngineOutcome outcome;
        if (wasCancelled) {
            outcome = FuzzEngineOutcome.CANCELLED;
        } else if (!findings.isEmpty()) {
            outcome = FuzzEngineOutcome.FINDINGS_FOUND;
        } else {
            outcome = FuzzEngineOutcome.BUDGET_EXHAUSTED;
        }
        if (!wasCancelled) {
            progressReporter.report(
                    100,
                    findings.isEmpty()
                            ? "Paper-compatible search budget exhausted"
                            : "Paper-compatible fuzz findings ready");
        }
        return result(
                outcome,
                effectiveSeed,
                completedIterations,
                generatedPaths,
                startedAt,
                new ArrayList<>(findings.values()),
                eligibility,
                limitations);
    }

    private static void validateInput(FuzzEngineInput input) {
        if (input == null || input.snapshot() == null || input.config() == null) {
            throw new IllegalArgumentException("snapshot and config are required");
        }
        FuzzEngineConfig config = input.config();
        if (config.maxIterations() < 0) {
            throw new IllegalArgumentException("maxIterations must be at least 0");
        }
        if (config.pathLength() < 1) {
            throw new IllegalArgumentException("pathLength must be at least 1");
        }
        if (config.populationSize() < 1) {
            throw new IllegalArgumentException("populationSize must be at least 1");
        }
    }

    private static long effectiveSeed(Long requestedSeed) {
        long raw = requestedSeed != null
                ? requestedSeed
                : System.nanoTime() ^ Long.rotateLeft(System.currentTimeMillis(), 21);
        return Math.floorMod(raw, SAFE_SEED_MODULUS);
    }

    private static Selection selectSpecifications(
            BoardDataConverter.ModelInputSnapshot snapshot,
            List<String> requestedIds,
            List<String> limitations) {
        List<SpecificationDto> all = snapshot.specifications();
        if (requestedIds == null || requestedIds.isEmpty()) {
            return new Selection(all);
        }
        Set<String> requested = new LinkedHashSet<>();
        for (String id : requestedIds) {
            if (id != null && !id.isBlank()) {
                requested.add(id.trim());
            }
        }
        List<SpecificationDto> selected = all.stream()
                .filter(specification -> specification != null && requested.contains(specification.getId()))
                .toList();
        Set<String> found = new LinkedHashSet<>();
        selected.forEach(specification -> found.add(specification.getId()));
        requested.removeAll(found);
        if (!requested.isEmpty()) {
            limitations.add("UNKNOWN_TARGET_SPEC_IDS_IGNORED");
        }
        return new Selection(selected);
    }

    private static UnsupportedReason globalUnsupportedReason(BoardDataConverter.ModelInputSnapshot snapshot) {
        for (RuleDto rule : snapshot.rules()) {
            if (rule == null) {
                continue;
            }
            RuleDto.Command command = rule.getCommand();
            if (command != null && (hasText(command.getContent()) || hasText(command.getContentDevice()))) {
                return new UnsupportedReason(
                        "CONTENT_COMMAND_UNSUPPORTED",
                        "Content-bearing automation commands are outside the fuzzing MVP.");
            }
        }
        return null;
    }

    private static UnsupportedReason eligibilityReason(SpecificationDto specification, FuzzModel model) {
        if (specification == null || !hasText(specification.getId())) {
            return new UnsupportedReason("INVALID_SPECIFICATION", "Specification ID is required.");
        }
        String templateId = specification.getTemplateId();
        if (!"1".equals(templateId) && !"3".equals(templateId) && !"4".equals(templateId)) {
            return new UnsupportedReason(
                    "UNSUPPORTED_TEMPLATE",
                    "Only specification templates 1, 3, and 4 are supported.");
        }
        for (SpecConditionDto condition : allConditions(specification)) {
            if (condition == null) {
                return new UnsupportedReason("INVALID_SPECIFICATION", "Specification conditions cannot contain null.");
            }
            String targetType = normalized(condition.getTargetType());
            if ("trust".equals(targetType) || "privacy".equals(targetType)) {
                return trustPrivacyUnsupported();
            }
        }
        try {
            model.validateSpecification(specification);
            return null;
        } catch (FuzzModel.ModelException exception) {
            return new UnsupportedReason("INVALID_SPECIFICATION", exception.getMessage());
        }
    }

    private static UnsupportedReason trustPrivacyUnsupported() {
        return new UnsupportedReason(
                "TRUST_PRIVACY_UNSUPPORTED",
                "Trust and privacy predicates are outside the fuzzing MVP.");
    }

    private static List<SpecConditionDto> allConditions(SpecificationDto specification) {
        List<SpecConditionDto> conditions = new ArrayList<>();
        conditions.addAll(safe(specification.getAConditions()));
        conditions.addAll(safe(specification.getIfConditions()));
        conditions.addAll(safe(specification.getThenConditions()));
        return conditions;
    }

    private static List<Genome> initialPopulation(SplittableRandom random, int size, int geneCount) {
        List<Genome> population = new ArrayList<>(size);
        for (int i = 0; i < size; i++) {
            population.add(randomGenome(random, geneCount));
        }
        return population;
    }

    private static List<Genome> nextPopulation(
            SplittableRandom random,
            List<CandidateScore> parents,
            int size,
            int geneCount,
            int nextGeneration) {
        List<Genome> next = new ArrayList<>(size);
        for (int slot = 0; slot < size; slot++) {
            if (parents.isEmpty() || isRandomRestartSlot(nextGeneration, size, slot)) {
                next.add(randomGenome(random, geneCount));
                continue;
            }
            long parentOrdinal = parentOrdinalForSlot(nextGeneration, size, slot);
            CandidateScore parent = parents.get((int) Math.floorMod(parentOrdinal, parents.size()));
            Genome mutated = mutatedCopy(random, parent);
            next.add(mutated == null ? randomGenome(random, geneCount) : mutated);
        }
        return next;
    }

    static boolean isRandomRestartSlot(int nextGeneration, int populationSize, int slot) {
        long offspringOrdinal = ((long) (nextGeneration - 1) * populationSize) + slot + 1L;
        return Math.floorMod(offspringOrdinal, RANDOM_RESTART_INTERVAL) == 0L;
    }

    static long parentOrdinalForSlot(int nextGeneration, int populationSize, int slot) {
        long zeroBasedOffspring = ((long) (nextGeneration - 1) * populationSize) + slot;
        long priorRestarts = Math.floorDiv(zeroBasedOffspring, RANDOM_RESTART_INTERVAL);
        return zeroBasedOffspring - priorRestarts;
    }

    static int paperParentIndexForSlot(
            int nextGeneration,
            int populationSize,
            int slot,
            int parentCount) {
        long parentOrdinal = ((long) (nextGeneration - 1) * populationSize) + slot;
        return (int) Math.floorMod(parentOrdinal, parentCount);
    }

    private static Genome randomGenome(SplittableRandom random, int geneCount) {
        long[] genes = new long[geneCount];
        for (int gene = 0; gene < geneCount; gene++) {
            genes[gene] = random.nextLong();
        }
        return new Genome(genes);
    }

    private static Genome mutatedCopy(SplittableRandom random, CandidateScore parent) {
        if (parent.mutableChoiceBounds().isEmpty()) {
            return null;
        }
        long[] genes = parent.genome().genes().clone();
        List<Integer> mutableIndexes = new ArrayList<>(parent.mutableChoiceBounds().keySet());
        int maxMutations = Math.max(1, mutableIndexes.size() / 8);
        int mutations = 1 + random.nextInt(maxMutations);
        for (int i = 0; i < mutations && !mutableIndexes.isEmpty(); i++) {
            int selected = random.nextInt(mutableIndexes.size());
            int geneIndex = mutableIndexes.remove(selected);
            int bound = parent.mutableChoiceBounds().get(geneIndex);
            int currentChoice = (int) Math.floorMod(genes[geneIndex], (long) bound);
            int offset = 1 + random.nextInt(bound - 1);
            genes[geneIndex] = (currentChoice + offset) % bound;
        }
        return new Genome(genes);
    }

    private static FuzzEngineResult result(
            FuzzEngineOutcome outcome,
            long effectiveSeed,
            int iterations,
            long generatedPaths,
            long startedAt,
            List<FuzzFinding> findings,
            List<FuzzSpecEligibility> eligibility,
            List<String> limitations) {
        long elapsedMs = Math.max(0L, (System.nanoTime() - startedAt) / 1_000_000L);
        return new FuzzEngineResult(
                outcome,
                effectiveSeed,
                iterations,
                generatedPaths,
                elapsedMs,
                findings,
                eligibility,
                limitations);
    }

    private static String normalized(String value) {
        return value == null ? "" : value.trim().toLowerCase(java.util.Locale.ROOT);
    }

    private static boolean hasText(String value) {
        return value != null && !value.isBlank();
    }

    private static <T> List<T> safe(List<T> values) {
        return values == null ? List.of() : values;
    }

    private record Genome(long[] genes) {
        private Genome copy() {
            return new Genome(genes.clone());
        }
    }

    private record CandidateScore(
            Genome genome,
            Map<Integer, Integer> mutableChoiceBounds,
            double distance) {
    }

    private record PaperCandidateScore(PaperSeed seed, double distance) {
    }

    private record Selection(List<SpecificationDto> specifications) {
    }

    private record UnsupportedReason(String code, String message) {
    }

    private static final class ProgressReporter {
        private final FuzzProgressListener listener;
        private int lastPercent = -1;

        private ProgressReporter(FuzzProgressListener listener) {
            this.listener = listener;
        }

        private void report(int percent, String message) {
            int bounded = Math.max(0, Math.min(100, percent));
            if (bounded == lastPercent) {
                return;
            }
            lastPercent = bounded;
            if (listener == null) {
                return;
            }
            try {
                listener.onProgress(bounded, message);
            } catch (RuntimeException ignored) {
                // Progress delivery must not change search results.
            }
        }
    }
}

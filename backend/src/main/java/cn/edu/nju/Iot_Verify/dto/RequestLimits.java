package cn.edu.nju.Iot_Verify.dto;

/** Central limits for user supplied model collections. */
public final class RequestLimits {
    public static final int MAX_DEVICES = 100;
    public static final int MAX_ENVIRONMENT_VARIABLES = 200;
    public static final int MAX_RULES = 100;
    public static final int MAX_SPECS = 100;
    public static final int MAX_RULE_CONDITIONS = 50;
    public static final int MAX_SPEC_CONDITIONS = 50;
    public static final int MAX_DEVICE_VARIABLES = 100;
    public static final int MAX_DEVICE_PRIVACIES = 100;
    /**
     * Must equal `DeviceNodePo.label`'s column length. The DTO's `@Size` only binds on the `@Valid` REST
     * path, so the service checks this itself — the AI tools call the service directly and an over-long
     * label otherwise reached the insert as a `DataIntegrityViolationException` / generic 500.
     */
    public static final int MAX_DEVICE_LABEL_LENGTH = 255;
    public static final int MAX_TEMPLATES = 100;
    public static final int MAX_CHAT_SESSIONS = 100;
    public static final int DEFAULT_CHAT_HISTORY_PAGE_SIZE = 50;
    public static final int MAX_CHAT_HISTORY_PAGE_SIZE = 100;
    public static final int MAX_CHAT_HISTORY_RAW_SCAN = 2000;
    public static final int MAX_CHAT_CONTENT_LENGTH = 10000;
    public static final int MAX_TEMPLATE_MODES = 20;
    public static final int MAX_TEMPLATE_WORKING_STATES = 100;
    public static final int MAX_TEMPLATE_DYNAMICS = 100;
    public static final int MAX_TEMPLATE_INTERNAL_VARIABLES = 100;
    public static final int MAX_TEMPLATE_VALUES = 100;
    /**
     * Widest {@code NaturalChangeRate} span the generator will model.
     *
     * <p>A declared interval is a constraint on {@code v' - v} (MEDIC §3.1, Fig. 2b), so every
     * integer in it must be an admissible next value — anything less proves properties the
     * declaration does not support. That makes the span a state-space cost, which is bounded here
     * and rejected at validation rather than silently narrowed to the endpoints.
     */
    public static final int MAX_NATURAL_CHANGE_RATE_SPAN = 100;
    /**
     * Largest number of distinct values a numeric variable domain may declare.
     *
     * <p>Bounded for the same reason as the span above — it is a state-space cost — but the immediate
     * cause is harsher than slowness. Measured on NuSMV 2.7.1: a variable declared `0..300000` makes the
     * engine print its banner and die with **no error and zero verdicts** (rc=127), deterministically,
     * in batch and interactive mode alike. `0..100000` still answers in 0.37 s, so the cliff sits
     * between them; this cap keeps a wide margin below it.
     *
     * <p>Nothing bounded it before: `device-template-schema.json` declares `LowerBound`/`UpperBound` as
     * plain `integer` with no `minimum`/`maximum`, and the Java validator checked only
     * `low > high` and `low == high`. So a template with a huge domain was admitted and persisted, and
     * every later verification of any board using it returned nothing at all —
     * `runTemplateNuSmvPrecheck` cannot catch it because it generates model text without ever starting
     * NuSMV, and it runs after `saveAndFlush` regardless.
     *
     * <p>Widest domain in the 45 bundled templates and 6 example scenes is **101** values (`0..100`,
     * across 30 numeric domains), so this rejects nothing that ships.
     */
    public static final int MAX_NUMERIC_DOMAIN_VALUES = 10_000;
    /*
     * The MAX_TEMPLATE_* constants below are mirrored by `maxItems` in `backend/device-template-schema.json`,
     * which is where they are actually enforced — the template endpoint accepts a raw `JsonNode` and runs
     * `validateRawManifest` before converting to this DTO, so Bean Validation never sees the manifest and a
     * `@Size` here would be decorative. That is stated in a `$comment` in the schema itself.
     *
     * They are therefore *not* unreferenced-by-accident: they document the Java-side value of a limit whose
     * mechanism lives in the schema. Verified live: a 21-mode template is rejected 400 with
     * "$.Modes: at most 20 items, found 21", naming the field and the limit.
     *
     * `MAX_TEMPLATE_ENVIRONMENT_DOMAINS` is kept for the same reason the others are, even though the
     * `EnvironmentDomains` array it named has since been removed from the schema — see that file's `$comment`
     * on read capability, which records what the array used to encode.
     */
    public static final int MAX_TEMPLATE_ENVIRONMENT_DOMAINS = 100;
    public static final int MAX_TEMPLATE_IMPACTED_VARIABLES = 100;
    public static final int MAX_TEMPLATE_TRANSITIONS = 100;
    public static final int MAX_TEMPLATE_APIS = 100;
    public static final int MAX_TEMPLATE_CONTENTS = 100;
    public static final int MAX_TASK_EXCLUSIONS = 100;
    public static final int MIN_REQUEST_ID_LENGTH = 8;
    public static final int MAX_REQUEST_ID_LENGTH = 80;
    /** Request IDs are opaque client correlation keys, never user-facing free text. */
    public static final String REQUEST_ID_PATTERN = "^[A-Za-z0-9][A-Za-z0-9._:-]*$";
    public static final int MAX_IDENTIFIER_LENGTH = 200;
    public static final int MAX_VALUE_LENGTH = 1000;
    public static final int MAX_DESCRIPTION_LENGTH = 4000;

    /*
     * Credential rules, brought into the mirrored limits.
     *
     * These were written out at each site instead: the character bounds appeared as literals in
     * `RegisterRequestDto`, again in `ValidationException`'s message, and again in `Landing.vue`'s client-side
     * check; the phone pattern appeared in the DTO annotation and again as a regex literal in `Landing.vue`.
     * Every other cross-layer limit in this product goes through this class and its mirror in
     * `frontend/src/constants/requestLimits.ts`, precisely so both sides reject identically — the credential
     * rules were the exception, and the convention was documented by comment with nothing checking it.
     *
     * They agree today. The risk is the next edit: changing a minimum here while a hardcoded client check keeps
     * the old one produces a form that accepts what the server refuses, and the user sees a rejection with no
     * explanation on the field they were told was fine.
     */

    /** BCrypt hashes at most 72 UTF-8 bytes, so a longer password would have its tail silently ignored. */
    public static final int MAX_PASSWORD_BCRYPT_BYTES = 72;
    public static final int MIN_PASSWORD_LENGTH = 10;
    public static final int MAX_PASSWORD_LENGTH = 64;
    /** Mainland China mobile numbers; the only format the product accepts as a sign-in identifier. */
    public static final String PHONE_PATTERN = "^1[3-9]\\d{9}$";
    /** Before normalization; the display rule shown to users is the narrower 3-20. */
    public static final int MAX_USERNAME_LENGTH = 100;
    public static final int MIN_USERNAME_DISPLAY_LENGTH = 3;
    public static final int MAX_USERNAME_DISPLAY_LENGTH = 20;

    private RequestLimits() {
    }
}

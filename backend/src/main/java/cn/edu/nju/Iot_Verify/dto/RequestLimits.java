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

    private RequestLimits() {
    }
}

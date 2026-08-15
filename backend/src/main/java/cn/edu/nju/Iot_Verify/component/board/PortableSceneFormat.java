package cn.edu.nju.Iot_Verify.component.board;

/**
 * The portable board-scene file contract.
 *
 * <p>Single home for the schema id and version. They were previously written out at four
 * independent sites — the scenario tool that emits drafts, the controller that admits them, the
 * frontend codec, and the frontend type declaration — with nothing tying them together. Bumping
 * the producer to 5 while the admitting validator still demanded 4 rejected every generated
 * scenario as "unsupported"; that is the failure this class exists to make impossible on the Java
 * side. The frontend counterpart is pinned by {@code PortableSceneContractTest}.</p>
 */
public final class PortableSceneFormat {

    /** Identifies an exported board scene and the shape its readers must expect. */
    public static final String SCHEMA = "iot-verify.board-scene";

    /**
     * 5: a {@code variable} specification condition must carry {@code variableSource}. A version-4
     * file cannot supply it, and guessing one would silently change what its specifications assert,
     * so those files are rejected by the version check rather than half-read.
     */
    public static final int VERSION = 5;

    private PortableSceneFormat() {
    }

    /** True when a scene declares exactly the schema and version this build reads. */
    public static boolean isSupported(String schema, Integer version) {
        return SCHEMA.equals(schema) && Integer.valueOf(VERSION).equals(version);
    }
}

package cn.edu.nju.Iot_Verify.service.impl;

import org.junit.jupiter.api.Test;

import java.nio.charset.StandardCharsets;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The stored SMV model must fit a MySQL {@code TEXT} column, which is bounded in bytes.
 *
 * <p>The model embeds user-authored rule text as comments (see {@code SmvRuleCommentWriter}), so a
 * real model is routinely non-ASCII. A cap counting characters lets such a model through at up to
 * three times the column bound; MySQL then rejects the insert and the run loses its whole result.
 */
class SmvModelContentTruncationTest {

    @Test
    void keepsAModelThatFitsUnchanged() {
        String model = "MODULE main\n-- 客厅温度规则\nVAR x : boolean;\n";

        assertSame(model, AbstractAsyncTaskService.truncateSmvModelContent(model));
    }

    @Test
    void boundsAMultiByteModelByBytesRatherThanCharacters() {
        // Under the byte bound as characters, ~3x over it as UTF-8 — the case a char-based cap misses.
        String model = "客".repeat(AbstractAsyncTaskService.MAX_SMV_MODEL_BYTES - 1);

        String stored = AbstractAsyncTaskService.truncateSmvModelContent(model);

        assertTrue(stored.getBytes(StandardCharsets.UTF_8).length
                        <= AbstractAsyncTaskService.MAX_SMV_MODEL_BYTES,
                "stored model must fit the TEXT column in bytes");
        assertTrue(stored.contains("-- [TRUNCATED: Original size "
                        + model.getBytes(StandardCharsets.UTF_8).length + " bytes]"),
                "the marker must name the original byte size, not a character count");
    }

    @Test
    void cutsOnACharacterBoundarySoTheFileStaysDecodable() {
        // One leading ASCII byte makes the byte budget land mid-character without a boundary-aware cut.
        String model = "M" + "客".repeat(AbstractAsyncTaskService.MAX_SMV_MODEL_BYTES);

        String stored = AbstractAsyncTaskService.truncateSmvModelContent(model);

        byte[] utf8 = stored.getBytes(StandardCharsets.UTF_8);
        assertEquals(stored, new String(utf8, StandardCharsets.UTF_8),
                "a mid-character cut would decode back with a replacement character");
        assertTrue(utf8.length <= AbstractAsyncTaskService.MAX_SMV_MODEL_BYTES);
    }

    @Test
    void boundsAnAsciiModelToo() {
        String model = "A".repeat(AbstractAsyncTaskService.MAX_SMV_MODEL_BYTES + 500);

        String stored = AbstractAsyncTaskService.truncateSmvModelContent(model);

        assertTrue(stored.getBytes(StandardCharsets.UTF_8).length
                <= AbstractAsyncTaskService.MAX_SMV_MODEL_BYTES);
        assertTrue(stored.endsWith(" bytes]"));
    }
}

package cn.edu.nju.Iot_Verify.util;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

class NaturalChangeRateParserTest {

    @Test
    void parsesTheSchemaGrammarAndSingleValueShorthand() {
        assertEquals(new NaturalChangeRateParser.RateRange(0, 0),
                NaturalChangeRateParser.parse(null));
        assertEquals(new NaturalChangeRateParser.RateRange(0, 1),
                NaturalChangeRateParser.parse("1"));
        assertEquals(new NaturalChangeRateParser.RateRange(-2, 0),
                NaturalChangeRateParser.parse("-2"));
        assertEquals(new NaturalChangeRateParser.RateRange(-1, 1),
                NaturalChangeRateParser.parse("[-1, 1]"));
        assertEquals(new NaturalChangeRateParser.RateRange(2, 3),
                NaturalChangeRateParser.parse("[2,3]"));
    }

    @Test
    void rejectsSyntaxThatTheFrontendAndJsonSchemaReject() {
        for (String raw : new String[]{"", " 1", "1,2", "[1,2,3]", "[[1,2]]", "[1,]", "+1"}) {
            assertThrows(NaturalChangeRateParser.ParseException.class,
                    () -> NaturalChangeRateParser.parse(raw), raw);
        }
    }

    @Test
    void rejectsOverflowAndDescendingIntervalsWithoutReinterpretingThem() {
        NaturalChangeRateParser.ParseException overflow = assertThrows(
                NaturalChangeRateParser.ParseException.class,
                () -> NaturalChangeRateParser.parse("2147483648"));
        assertFalse(overflow.isDescending());

        NaturalChangeRateParser.ParseException descending = assertThrows(
                NaturalChangeRateParser.ParseException.class,
                () -> NaturalChangeRateParser.parse("[3,2]"));
        assertTrue(descending.isDescending());
    }

    @Test
    void canonicalFormMatchesEquivalentDeclarationsAndPreservesMalformedText() {
        assertEquals("0..1", NaturalChangeRateParser.canonical("1"));
        assertEquals("0..1", NaturalChangeRateParser.canonical("[0, 1]"));
        assertEquals("1,2", NaturalChangeRateParser.canonical("1,2"));
    }
}

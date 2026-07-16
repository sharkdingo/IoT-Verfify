package cn.edu.nju.Iot_Verify.component.fuzz.paper;

import java.util.HashSet;
import java.util.List;

/** One device target, its initial mode/property, and legal values. */
public record PaperDeviceDomain(String targetId, String property, List<String> legalValues) {

    public PaperDeviceDomain {
        targetId = requireText(targetId, "targetId");
        property = requireText(property, "property");
        legalValues = immutableValues(legalValues);
    }

    private static List<String> immutableValues(List<String> input) {
        if (input == null || input.isEmpty()) {
            throw new IllegalArgumentException("device legalValues must not be empty");
        }
        if (input.size() > PaperEventDomain.MAX_VALUES_PER_TARGET) {
            throw new IllegalArgumentException(
                    "device legalValues exceeds " + PaperEventDomain.MAX_VALUES_PER_TARGET);
        }
        List<String> values = input.stream()
                .map(value -> requireText(value, "device legal value"))
                .toList();
        if (new HashSet<>(values).size() != values.size()) {
            throw new IllegalArgumentException("device legalValues must not contain duplicates");
        }
        return List.copyOf(values);
    }

    private static String requireText(String value, String field) {
        if (value == null || value.isBlank()) {
            throw new IllegalArgumentException(field + " must not be blank");
        }
        return value.trim();
    }
}

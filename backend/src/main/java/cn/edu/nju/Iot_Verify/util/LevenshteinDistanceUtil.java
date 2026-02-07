package cn.edu.nju.Iot_Verify.util;

/**
 * Levenshtein Distance Utility
 * Calculates the edit distance between two strings.
 */
public final class LevenshteinDistanceUtil {

    private LevenshteinDistanceUtil() {
        // Utility class - prevent instantiation
    }

    /**
     * Calculate the Levenshtein distance between two strings.
     * The distance is the minimum number of single-character edits
     * (insertions, deletions, or substitutions) required to change one string into the other.
     *
     * @param s1 First string
     * @param s2 Second string
     * @return The edit distance between the two strings
     */
    public static int calculate(String s1, String s2) {
        if (s1 == null || s2 == null) {
            throw new IllegalArgumentException("Input strings cannot be null");
        }

        int len1 = s1.length();
        int len2 = s2.length();

        // Use a single-dimensional array to save memory
        int[] previousRow = new int[len2 + 1];
        int[] currentRow = new int[len2 + 1];

        // Initialize the first row
        for (int j = 0; j <= len2; j++) {
            previousRow[j] = j;
        }

        for (int i = 1; i <= len1; i++) {
            currentRow[0] = i;
            for (int j = 1; j <= len2; j++) {
                int cost = (s1.charAt(i - 1) == s2.charAt(j - 1)) ? 0 : 1;
                currentRow[j] = Math.min(
                        Math.min(previousRow[j] + 1, currentRow[j - 1] + 1),
                        previousRow[j - 1] + cost
                );
            }
            // Swap rows
            int[] temp = previousRow;
            previousRow = currentRow;
            currentRow = temp;
        }

        return previousRow[len2];
    }

    /**
     * Calculate the similarity ratio between two strings.
     *
     * @param s1 First string
     * @param s2 Second string
     * @return Similarity ratio (0.0 to 1.0), where 1.0 means identical
     */
    public static double similarityRatio(String s1, String s2) {
        if (s1 == null || s2 == null) {
            throw new IllegalArgumentException("Input strings cannot be null");
        }

        if (s1.isEmpty() && s2.isEmpty()) {
            return 1.0;
        }

        if (s1.isEmpty() || s2.isEmpty()) {
            return 0.0;
        }

        int distance = calculate(s1, s2);
        int maxLength = Math.max(s1.length(), s2.length());
        return 1.0 - (double) distance / maxLength;
    }
}

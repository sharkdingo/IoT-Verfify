package cn.edu.nju.Iot_Verify.dto.board;

import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * Result of a targeted collection mutation.
 *
 * <p>The affected item explains what changed, while {@code currentItems} lets clients
 * replace a stale local collection with the authoritative post-mutation snapshot.</p>
 */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class CollectionMutationResultDto<T> {
    private String operation;
    private T affectedItem;
    private List<T> currentItems;
    private int currentCount;

    public static <T> CollectionMutationResultDto<T> of(String operation,
                                                         T affectedItem,
                                                         List<T> currentItems) {
        List<T> items = currentItems != null ? currentItems : List.of();
        return new CollectionMutationResultDto<>(operation, affectedItem, items, items.size());
    }
}

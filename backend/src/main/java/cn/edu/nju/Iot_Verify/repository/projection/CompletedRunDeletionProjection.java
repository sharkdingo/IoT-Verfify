package cn.edu.nju.Iot_Verify.repository.projection;

import java.time.LocalDateTime;

/** Minimal completed-run projection used by irreversible deletion previews. */
public interface CompletedRunDeletionProjection {

    Long getId();

    LocalDateTime getCreatedAt();

    LocalDateTime getCompletedAt();
}

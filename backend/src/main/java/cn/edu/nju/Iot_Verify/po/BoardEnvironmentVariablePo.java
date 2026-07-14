package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.Column;
import jakarta.persistence.Entity;
import jakarta.persistence.Id;
import jakarta.persistence.IdClass;
import jakarta.persistence.Index;
import jakarta.persistence.Table;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import lombok.NoArgsConstructor;
import lombok.Setter;
import lombok.ToString;

@Entity
@Table(name = "board_environment_variable", indexes = {
        @Index(name = "idx_board_env_user_id", columnList = "user_id")
})
@IdClass(BoardEnvironmentVariableId.class)
@Getter
@Setter
@ToString
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
@NoArgsConstructor
@AllArgsConstructor
@Builder
public class BoardEnvironmentVariablePo {

    @Id
    @Column(length = 100)
    @EqualsAndHashCode.Include
    private String name;

    @Id
    @Column(name = "user_id", nullable = false)
    @EqualsAndHashCode.Include
    private Long userId;

    @Column(name = "variable_value", length = 255)
    private String value;

    @Column(length = 50)
    private String trust;

    @Column(length = 50)
    private String privacy;
}

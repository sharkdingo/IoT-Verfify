package cn.edu.nju.Iot_Verify.po;

import java.io.Serializable;
import java.util.Objects;

public class BoardEnvironmentVariableId implements Serializable {

    private String name;
    private Long userId;

    public BoardEnvironmentVariableId() {
    }

    public BoardEnvironmentVariableId(String name, Long userId) {
        this.name = name;
        this.userId = userId;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        BoardEnvironmentVariableId that = (BoardEnvironmentVariableId) o;
        return Objects.equals(name, that.name) && Objects.equals(userId, that.userId);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name, userId);
    }
}

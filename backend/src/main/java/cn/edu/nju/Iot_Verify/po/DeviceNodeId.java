package cn.edu.nju.Iot_Verify.po;

import java.io.Serializable;
import java.util.Objects;

public class DeviceNodeId implements Serializable {

    private String id;
    private Long userId;

    public DeviceNodeId() {
    }

    public DeviceNodeId(String id, Long userId) {
        this.id = id;
        this.userId = userId;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        DeviceNodeId that = (DeviceNodeId) o;
        return Objects.equals(id, that.id) && Objects.equals(userId, that.userId);
    }

    @Override
    public int hashCode() {
        return Objects.hash(id, userId);
    }
}

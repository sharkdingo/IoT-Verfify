package cn.edu.nju.Iot_Verify.po;

import java.io.Serializable;
import java.util.Objects;

public class DeviceEdgeId implements Serializable {

    private String id;
    private Long userId;

    public DeviceEdgeId() {}

    public DeviceEdgeId(String id, Long userId) {
        this.id = id;
        this.userId = userId;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        DeviceEdgeId that = (DeviceEdgeId) o;
        return Objects.equals(id, that.id) && Objects.equals(userId, that.userId);
    }

    @Override
    public int hashCode() {
        return Objects.hash(id, userId);
    }
}

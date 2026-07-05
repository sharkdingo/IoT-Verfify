package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.po.TracePo;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class TraceMapperTest {

    private final TraceMapper mapper = new TraceMapper();

    private TracePo baseTrace(String requestJson) {
        TracePo po = new TracePo();
        po.setId(1L);
        po.setUserId(1L);
        po.setViolatedSpecId("s0");
        po.setRequestJson(requestJson);
        return po;
    }

    @Test
    void derivesAttackContextFromRequestJson() {
        TracePo po = baseTrace("{\"devices\":[{\"varName\":\"d1\",\"templateName\":\"t1\"}],"
                + "\"rules\":[],\"specs\":[],\"isAttack\":true,\"intensity\":7,\"enablePrivacy\":true}");

        TraceDto dto = mapper.toDto(po);

        assertEquals(Boolean.TRUE, dto.getAttack());
        assertEquals(7, dto.getIntensity());
        assertEquals(Boolean.TRUE, dto.getEnablePrivacy());
    }

    @Test
    void derivesDefaultsWhenFlagsAbsent() {
        // isAttack/enablePrivacy default false, intensity defaults to 3 per VerificationRequestDto.
        TracePo po = baseTrace("{\"devices\":[{\"varName\":\"d1\",\"templateName\":\"t1\"}],"
                + "\"rules\":[],\"specs\":[]}");

        TraceDto dto = mapper.toDto(po);

        assertEquals(Boolean.FALSE, dto.getAttack());
        assertEquals(3, dto.getIntensity());
        assertEquals(Boolean.FALSE, dto.getEnablePrivacy());
    }

    @Test
    void legacyTraceWithoutSnapshot_leavesContextNull() {
        // Traces recorded before the snapshot was saved must not fail mapping; derived fields stay null
        // so the frontend simply omits the labels.
        TracePo po = baseTrace(null);

        TraceDto dto = mapper.toDto(po);

        assertNull(dto.getAttack());
        assertNull(dto.getIntensity());
        assertNull(dto.getEnablePrivacy());
    }

    @Test
    void unparseableSnapshot_doesNotThrow_leavesContextNull() {
        TracePo po = baseTrace("{ not valid json ");

        TraceDto dto = assertDoesNotThrow(() -> mapper.toDto(po));

        assertNull(dto.getAttack());
        assertNull(dto.getIntensity());
        assertNull(dto.getEnablePrivacy());
    }
}

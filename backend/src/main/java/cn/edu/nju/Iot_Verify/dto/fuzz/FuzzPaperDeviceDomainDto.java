package cn.edu.nju.Iot_Verify.dto.fuzz;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.List;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FuzzPaperDeviceDomainDto {

    private String targetId;
    private String label;
    private String property;
    private Integer lowerBound;
    private Integer upperBound;

    @Builder.Default
    private List<String> legalValues = new ArrayList<>();
}

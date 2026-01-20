package cn.edu.nju.Iot_Verify.dto;

import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

@Data
@NoArgsConstructor
@AllArgsConstructor
public class RuleDto {
    private String id;
    private List<SourceEntryDto> sources;
    private String toId;
    private String toApi;
    private String templateLabel;
}





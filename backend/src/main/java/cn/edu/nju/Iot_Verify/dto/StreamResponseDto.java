package cn.edu.nju.Iot_Verify.dto;

import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@NoArgsConstructor
public class StreamResponseDto {
    private String content;

    public StreamResponseDto(String content) {
        this.content = content;
    }
    // Getter & Setter
    public String getContent() { return content; }
    public void setContent(String content) { this.content = content; }
}

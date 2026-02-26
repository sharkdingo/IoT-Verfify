package cn.edu.nju.Iot_Verify.client;

import dev.langchain4j.data.embedding.Embedding;
import dev.langchain4j.data.segment.TextSegment;
import dev.langchain4j.model.embedding.EmbeddingModel;
import dev.langchain4j.model.embedding.onnx.bgesmallenv15q.BgeSmallEnV15QuantizedEmbeddingModel;
import jakarta.annotation.PostConstruct;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.stereotype.Service;

import java.util.List;

@Getter
@Slf4j
@Service
public class EmbeddingClient {
  private EmbeddingModel embeddingModel;

  @PostConstruct
  public void init() {
    embeddingModel = new BgeSmallEnV15QuantizedEmbeddingModel();
    log.info("Initialized BGE embedding model");
  }

  public List<Embedding> embedAll(List<TextSegment> texts) {
    return embeddingModel.embedAll(texts).content();
  }
}
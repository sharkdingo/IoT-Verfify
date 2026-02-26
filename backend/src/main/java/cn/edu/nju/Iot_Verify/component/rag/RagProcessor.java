package cn.edu.nju.Iot_Verify.component.rag;

import cn.edu.nju.Iot_Verify.client.EmbeddingClient;
import dev.langchain4j.data.document.Document;
import dev.langchain4j.data.document.DocumentParser;
import dev.langchain4j.data.document.DocumentSplitter;
import dev.langchain4j.data.document.parser.TextDocumentParser;
import dev.langchain4j.data.document.splitter.DocumentSplitters;
import dev.langchain4j.data.embedding.Embedding;
import dev.langchain4j.rag.content.Content;
import dev.langchain4j.rag.query.Query;
import dev.langchain4j.data.segment.TextSegment;
import dev.langchain4j.rag.content.retriever.ContentRetriever;
import dev.langchain4j.rag.content.retriever.EmbeddingStoreContentRetriever;
import dev.langchain4j.store.embedding.EmbeddingStore;
import dev.langchain4j.store.embedding.inmemory.InMemoryEmbeddingStore;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.List;
import java.util.stream.Collectors;

import static dev.langchain4j.data.document.loader.FileSystemDocumentLoader.loadDocument;

@Component
@RequiredArgsConstructor
@Slf4j
public class RagProcessor {

    private final EmbeddingStore<TextSegment> embeddingStore = new InMemoryEmbeddingStore<>();
    private final EmbeddingClient embeddingClient;

    public void loadAndProcessDocument(String documentPath) {
        DocumentParser parser = new TextDocumentParser();
        Document document = loadDocument(documentPath, parser);

        DocumentSplitter splitter = DocumentSplitters.recursive(300, 0);
        List<TextSegment> segments = splitter.split(document);

        List<Embedding> embeddings = embeddingClient.embedAll(segments);
        embeddingStore.addAll(embeddings, segments);
    }

    public String processQuery(String userInput) {
        ContentRetriever retriever = EmbeddingStoreContentRetriever.builder()
                .embeddingStore(embeddingStore)
                .embeddingModel(embeddingClient.getEmbeddingModel())
                .maxResults(2)
                .minScore(0.5)
                .build();

        Query query = new Query(userInput);
        List<Content> relevantSegments = retriever.retrieve(query);
        return relevantSegments.stream()
                .map(Object::toString)
                .collect(Collectors.joining("\n"));
    }
}
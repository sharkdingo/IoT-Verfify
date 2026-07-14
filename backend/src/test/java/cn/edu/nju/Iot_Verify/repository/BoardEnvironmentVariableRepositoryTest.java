package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.BoardEnvironmentVariablePo;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.jdbc.AutoConfigureTestDatabase;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;

import java.util.List;
import java.util.Objects;

import static org.junit.jupiter.api.Assertions.assertEquals;

@DataJpaTest(properties = {
        "spring.jpa.database-platform=org.hibernate.dialect.H2Dialect",
        "spring.jpa.properties.hibernate.dialect=org.hibernate.dialect.H2Dialect",
        "spring.jpa.hibernate.ddl-auto=create-drop"
})
@AutoConfigureTestDatabase(replace = AutoConfigureTestDatabase.Replace.ANY)
class BoardEnvironmentVariableRepositoryTest {

    @Autowired
    private BoardEnvironmentVariableRepository repository;

    @Test
    void save_shouldPersistValueWithoutUsingReservedColumnName() {
        repository.save(Objects.requireNonNull(BoardEnvironmentVariablePo.builder()
                .userId(1L)
                .name("temperature")
                .value("22")
                .trust("trusted")
                .privacy("public")
                .build()));

        List<BoardEnvironmentVariablePo> saved = repository.findByUserIdOrderByNameAsc(1L);

        assertEquals(1, saved.size());
        assertEquals("22", saved.get(0).getValue());
    }
}

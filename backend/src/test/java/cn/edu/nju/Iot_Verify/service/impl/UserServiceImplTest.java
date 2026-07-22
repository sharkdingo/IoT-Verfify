package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.security.crypto.password.PasswordEncoder;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class UserServiceImplTest {

    @Mock private UserRepository userRepository;
    @Mock private PasswordEncoder passwordEncoder;

    @Test
    void register_shouldPersistCanonicalUsername() {
        UserServiceImpl service = new UserServiceImpl(userRepository, passwordEncoder);
        when(passwordEncoder.encode("password123")).thenReturn("encoded");
        when(userRepository.save(any(UserPo.class))).thenAnswer(invocation -> invocation.getArgument(0));

        UserPo user = service.register("13800138000", "  Alice  ", "password123");

        assertEquals("Alice", user.getUsername());
        verify(userRepository).existsByUsername("Alice");
    }

    @Test
    void register_shouldRevalidateLengthAfterTrimming() {
        UserServiceImpl service = new UserServiceImpl(userRepository, passwordEncoder);

        assertThrows(BadRequestException.class,
                () -> service.register("13800138000", "  a  ", "password123"));

        verify(userRepository, never()).save(any());
    }

    @Test
    void register_shouldRejectControlCharacters() {
        UserServiceImpl service = new UserServiceImpl(userRepository, passwordEncoder);

        assertThrows(BadRequestException.class,
                () -> service.register("13800138000", "Ali\nce", "password123"));
    }

    @Test
    void register_shouldRejectPhoneShapedUsername() {
        UserServiceImpl service = new UserServiceImpl(userRepository, passwordEncoder);

        assertThrows(BadRequestException.class,
                () -> service.register("13900139000", "13800138000", "password123"));

        verify(userRepository, never()).save(any());
    }
}

package cn.edu.nju.Iot_Verify.component.nusmv.executor;

import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.lang.reflect.Method;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class NusmvExecutorCommandTest {

    @SuppressWarnings("unchecked")
    private List<String> invokeBuildCommand(NusmvExecutor executor, File smvFile) throws Exception {
        Method method = NusmvExecutor.class.getDeclaredMethod("buildCommand", File.class);
        method.setAccessible(true);
        return (List<String>) method.invoke(executor, smvFile);
    }

    @Test
    void buildCommand_withPrefixOnUnix_wrapsInSingleShellCommand() throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setPath("/opt/NuSMV/bin/NuSMV");
        config.setCommandPrefix("wsl");

        NusmvExecutor executor = new NusmvExecutor(config);
        List<String> command = invokeBuildCommand(executor, new File("/tmp/model.smv"));

        assertEquals("sh", command.get(0));
        assertEquals("-c", command.get(1));
        assertEquals(3, command.size());
        assertTrue(command.get(2).contains("wsl"));
        assertTrue(command.get(2).contains("NuSMV"));
        assertTrue(command.get(2).contains("model.smv"));
    }

    @Test
    void buildCommand_withoutPrefixOnUnix_keepsRawExecutableAndArgs() throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setPath("/opt/NuSMV/bin/NuSMV");
        config.setCommandPrefix("");

        NusmvExecutor executor = new NusmvExecutor(config);
        List<String> command = invokeBuildCommand(executor, new File("/tmp/model.smv"));

        assertEquals(2, command.size());
        assertEquals("/opt/NuSMV/bin/NuSMV", command.get(0));
        assertEquals("/tmp/model.smv", command.get(1));
    }
}

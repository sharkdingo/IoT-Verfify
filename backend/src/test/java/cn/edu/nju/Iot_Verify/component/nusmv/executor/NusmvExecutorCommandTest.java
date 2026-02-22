package cn.edu.nju.Iot_Verify.component.nusmv.executor;

import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.lang.reflect.Method;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class NusmvExecutorCommandTest {

    private static final boolean IS_WINDOWS =
            System.getProperty("os.name").toLowerCase().contains("windows");

    @SuppressWarnings("unchecked")
    private List<String> invokeBuildCommand(NusmvExecutor executor, File smvFile, List<String> extraArgs) throws Exception {
        Method method = NusmvExecutor.class.getDeclaredMethod("buildCommand", File.class, List.class);
        method.setAccessible(true);
        return (List<String>) method.invoke(executor, smvFile, extraArgs);
    }

    @Test
    void buildCommand_withPrefix_wrapsInShellCommand() throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setPath("/opt/NuSMV/bin/NuSMV");
        config.setCommandPrefix("wsl");

        NusmvExecutor executor = new NusmvExecutor(config);
        List<String> command = invokeBuildCommand(executor, new File("/tmp/model.smv"), List.of());

        if (IS_WINDOWS) {
            assertEquals("cmd.exe", command.get(0));
            assertEquals("/c", command.get(1));
        } else {
            assertEquals("sh", command.get(0));
            assertEquals("-c", command.get(1));
        }
        assertEquals(3, command.size());
        assertTrue(command.get(2).contains("wsl"));
        assertTrue(command.get(2).contains("NuSMV"));
        assertTrue(command.get(2).contains("model.smv"));
    }

    @Test
    void buildCommand_withoutPrefix_keepsRawExecutableAndArgs() throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setPath("/opt/NuSMV/bin/NuSMV");
        config.setCommandPrefix("");

        NusmvExecutor executor = new NusmvExecutor(config);
        List<String> command = invokeBuildCommand(executor, new File("/tmp/model.smv"), List.of());

        assertEquals(2, command.size());
        assertEquals("/opt/NuSMV/bin/NuSMV", command.get(0));
        // File.getAbsolutePath() may differ on Windows vs Unix
        assertTrue(command.get(1).endsWith("model.smv"));
    }

    @Test
    void buildCommand_withExtraArgs_insertsBeforeSmvFile() throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setPath("/opt/NuSMV/bin/NuSMV");
        config.setCommandPrefix("");

        NusmvExecutor executor = new NusmvExecutor(config);
        List<String> command = invokeBuildCommand(executor, new File("/tmp/model.smv"), List.of("-int"));

        assertEquals(3, command.size());
        assertEquals("/opt/NuSMV/bin/NuSMV", command.get(0));
        assertEquals("-int", command.get(1));
        assertTrue(command.get(2).endsWith("model.smv"));
    }

    @Test
    void buildCommand_withPrefixAndExtraArgs_includesAllInShellString() throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setPath("/opt/NuSMV/bin/NuSMV");
        config.setCommandPrefix("wsl");

        NusmvExecutor executor = new NusmvExecutor(config);
        List<String> command = invokeBuildCommand(executor, new File("/tmp/model.smv"), List.of("-int"));

        assertEquals(3, command.size());
        String shellCmd = command.get(2);
        assertTrue(shellCmd.contains("wsl"));
        assertTrue(shellCmd.contains("-int"));
        assertTrue(shellCmd.contains("model.smv"));
    }
}

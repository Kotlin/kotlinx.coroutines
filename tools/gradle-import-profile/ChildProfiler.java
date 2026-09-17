package coroutines.profile;

import one.profiler.AsyncProfiler;
import java.io.InputStream;
import java.lang.management.ManagementFactory;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.Properties;

/** Java 8-compatible startup agent: instrument build JVMs, not JDK discovery probes. */
public final class ChildProfiler {
    public static void premain(String configuration) {
        Path directory = Paths.get(configuration).getParent();
        String pid = ManagementFactory.getRuntimeMXBean().getName().split("@", 2)[0];
        try {
            Properties settings = new Properties();
            try (InputStream stream = Files.newInputStream(Paths.get(configuration))) { settings.load(stream); }
            String command = System.getProperty("sun.java.command", "");
            String main = command.split("\\s+", 2)[0];
            boolean probe = main.equals("JavaProbe");
            String kind = probe ? "probe" : command.contains("KotlinCompileDaemon") ? "kotlin"
                : command.contains("GradleWorkerMain") ? "worker" : "child";
            String metadata = "{\"pid\":" + pid + ",\"kind\":" + quote(kind)
                + ",\"mainClass\":" + quote(main) + ",\"javaVersion\":" + quote(System.getProperty("java.runtime.version"))
                + ",\"javaHome\":" + quote(System.getProperty("java.home")) + "}";
            Files.write(directory.resolve("jvm-" + pid + ".json"), metadata.getBytes(StandardCharsets.UTF_8));
            if (probe) return;
            final AsyncProfiler profiler = AsyncProfiler.getInstance(settings.getProperty("library"));
            profiler.execute("start,event=cpu,alloc=" + settings.getProperty("alloc")
                + ",interval=" + settings.getProperty("cpu") + ",file=" + directory.resolve("jvm-%p.jfr"));
            Runtime.getRuntime().addShutdownHook(new Thread(() -> {
                try { profiler.execute("stop"); } catch (Exception ignored) { /* Already stopped by runner. */ }
            }, "import-profiler-flush"));
        } catch (Throwable error) {
            try { Files.write(directory.resolve("jvm-" + pid + ".agent-error.txt"), error.toString().getBytes(StandardCharsets.UTF_8)); }
            catch (Exception ignored) { }
            error.printStackTrace(System.err);
        }
    }

    private static String quote(String value) {
        return "\"" + value.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n").replace("\r", "\\r") + "\"";
    }
}

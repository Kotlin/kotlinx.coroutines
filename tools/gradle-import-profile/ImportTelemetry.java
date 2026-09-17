package coroutines.profile;

import com.google.gson.Gson;
import com.intellij.platform.diagnostic.telemetry.IJTracer;
import com.intellij.platform.diagnostic.telemetry.TelemetryManager;
import com.intellij.platform.diagnostic.telemetry.TracerLevel;
import io.opentelemetry.api.trace.SpanBuilder;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Context;
import io.opentelemetry.sdk.common.CompletableResultCode;
import io.opentelemetry.sdk.trace.*;
import io.opentelemetry.sdk.trace.data.SpanData;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Proxy;
import java.nio.file.*;
import java.util.*;

/** Records existing external-system spans without replacing the global OpenTelemetry SDK. */
final class ImportTelemetry implements AutoCloseable {
    private final TelemetryManager original = TelemetryManager.getInstance();
    private final List<Map<String, Object>> spans = Collections.synchronizedList(new ArrayList<>());
    private final SdkTracerProvider provider;
    private final TelemetryManager wrapper;
    private final Path output;

    ImportTelemetry(Path output) {
        this.output = output;
        provider = SdkTracerProvider.builder().addSpanProcessor(new SpanProcessor() {
            public void onStart(Context context, ReadWriteSpan span) { }
            public boolean isStartRequired() { return false; }
            public boolean isEndRequired() { return true; }
            public void onEnd(ReadableSpan span) {
                SpanData data = span.toSpanData();
                Map<String, Object> attributes = new TreeMap<>();
                data.getAttributes().forEach((key, value) -> attributes.put(key.getKey(), value));
                spans.add(Map.of("name", data.getName(), "start_ns", data.getStartEpochNanos(),
                    "end_ns", data.getEndEpochNanos(), "id", data.getSpanId(),
                    "parent", data.getParentSpanId(), "trace", data.getTraceId(),
                    "scope", data.getInstrumentationScopeInfo().getName(), "attributes", attributes));
            }
            public CompletableResultCode shutdown() { return CompletableResultCode.ofSuccess(); }
            public CompletableResultCode forceFlush() { return CompletableResultCode.ofSuccess(); }
        }).build();
        wrapper = (TelemetryManager) Proxy.newProxyInstance(TelemetryManager.class.getClassLoader(),
            new Class<?>[]{TelemetryManager.class}, (proxy, method, args) -> {
                if (method.getName().equals("getTracer") && args[0].toString().contains("external.system")) {
                    Tracer tracer = provider.get(args[0].toString());
                    return new IJTracer() {
                        public SpanBuilder spanBuilder(String name) { return tracer.spanBuilder(name); }
                        public SpanBuilder spanBuilder(String name, TracerLevel level) { return tracer.spanBuilder(name); }
                    };
                }
                try { return method.invoke(original, args); }
                catch (InvocationTargetException error) { throw error.getCause(); }
            });
        TelemetryManager.Companion.forceSetTelemetryManager(wrapper);
    }

    @Override public void close() throws Exception {
        if (TelemetryManager.getInstance() == wrapper) TelemetryManager.Companion.forceSetTelemetryManager(original);
        provider.close();
        synchronized (spans) { Files.writeString(output, new Gson().toJson(spans)); }
    }
}

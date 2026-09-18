# Capture an import trace

[Overview](../index.md) · [Span/export semantics](span-reference.md) · [Raw-data layout](../bin/README.md)

**Status:** a source-checked procedure, not a runtime-tested setup on this machine. No collector was listening at `localhost:16686` or `localhost:4318` during preparation; no services or imports were launched. The user subsequently supplied an existing Jaeger export, analyzed [separately](../measurements/jaeger-trace.md); it does not validate this local setup.

## Important correction to the supplied instructions

The original recipe says `gradle.daemon.opentelemetry.enabled`. In the inspected IntelliJ checkout, the registered extension checks **`gradle.daemon.opentelemetry.agent.enabled`**, declared default **false**. Use the key exposed by the IDE version actually running; do not silently assume the historical spelling works. See [T01–T02](../reference/sources.md). The [original recipe](../bin/user-telemetry-recipe.md) is preserved separately.

## 1. Collector

Use the supplied Jaeger all-in-one approach. The following minimal Compose configuration exposes only the UI and OTLP ports on loopback; the original extra legacy-protocol ports are not required for this recipe. Pin a tested image tag/digest and record it before comparing measurements; the unversioned image below matches the supplied starting point and is not a reproducibility guarantee.

Save as `docker-compose.yml` in a dedicated capture/setup directory:

```yaml
services:
  jaeger:
    image: jaegertracing/all-in-one
    environment:
      COLLECTOR_OTLP_ENABLED: "true"
    ports:
      - "127.0.0.1:16686:16686"
      - "127.0.0.1:4317:4317"
      - "127.0.0.1:4318:4318"
```

```sh
docker compose up -d
docker compose ps
docker compose logs --tail=100 jaeger
```

The older command spelling in the supplied recipe is `docker-compose up -d`. Check image/version-specific OTLP receiver support. Open `http://localhost:16686`; the receiver is `http://localhost:4318`. A GET to the receiver need not return 200: it accepts trace POSTs, so use collector logs and an actual trace to confirm delivery. Export traces before stopping an in-memory all-in-one collector; it is not durable storage.

## 2. IDE and daemon activation

1. In **Help → Edit Custom VM Options**, add:

   ```text
   -Didea.diagnostic.opentelemetry.otlp=http://localhost:4318
   ```

2. Restart the IDE at a convenient time so telemetry initialization sees the property. Record the restart as part of the run's cache-state preparation, not as unexplained timing noise.
3. Open **Registry** via Find Action and enable `gradle.daemon.opentelemetry.agent.enabled` for this source revision. Record both key and value with the IDE build.
4. Check endpoint precedence: `OTLP_ENDPOINT` overrides the JVM property, including an empty environment value. The implementation appends `/v1/traces`, so supply the base URL, not an already suffixed URL. Presence of `rdct.diagnostic.otlp` suppresses this endpoint/agent-injection path ([T03–T04](../reference/sources.md)).
5. Agent resolution must succeed: the inspected implementation obtains OpenTelemetry Java agent **2.8.0** under the IDE system directory's `otlp-agent` cache, downloading it if missing. Check proxy/network failures and IDE logs. Record the actual agent hash/version ([T05–T07](../reference/sources.md)).
6. Daemon JVM options now include a Java agent and telemetry configuration. This may change daemon compatibility and make the first telemetry-enabled import colder. Verify the actual process/options; do not stop all unrelated Gradle daemons to force a desired scenario.

IDE spans and daemon spans export **separately**. The IDE supplies parent context through `otel.trace.context`; daemon spans are not carried back as model payloads. Setting an IDE trace-file option alone does not establish a daemon trace file.

## 3. Run one clearly identified sync

- Record a run ID, start/end wall-clock time, IDE/KGP/Gradle/JDK versions and source/binary hashes, project path, flags, cache dimensions, network/offline state, indexing policy and background load.
- Trigger a single Gradle Sync. Preserve logs, warnings, failures and partial-import status.
- Record sync completion and model-application completion separately from indexing completion if the intended metric includes editor readiness.
- Wait for export and inspect Jaeger. The supplied “wait a minute or two” is a useful first attempt, **not a guarantee**: the IDE SDK processor has a one-minute **inactivity** timeout; another activity path uses five minutes; daemon agent flushing is separate.
- If needed, close the IDE normally after saving work to exercise shutdown flushing, as in the original recipe. Closing the IDE does not establish that a long-lived Gradle daemon has flushed. Verify both services/spans arrived rather than treating shutdown as a delivery receipt.

## 4. Find and preserve the trace

Search Jaeger using the actual reported service(s) and the sync time window. The supplied UI name pattern is `Progress: Importing '<Project Name>' Gradle Project` (the example used `Progress: Importing 'gradle' Gradle: Project`). These labels are version-dependent; also search the source-backed operation **`ExternalSystemSyncProjectTask`** and inspect its trace.

Check that the trace contains both IDE and Gradle-daemon activity with coherent parent/trace IDs. A missing service can mean disabled instrumentation, sampling, agent resolution failure, endpoint mismatch, buffering, lost context or export failure—not zero work.

Export the **full trace JSON**, not just a screenshot. Save under `import-overview/bin/captures/<run-id>/` along with a manifest, IDE/Gradle logs, collector logs, effective settings and any operation/CPU/allocation recordings. Preserve original units and IDs. Label missing spans, clock uncertainty and incomplete roots explicitly.

## 5. Fill gaps with operations and profiling

OTel scopes identify logical work and waits; they are not a complete Gradle build-operation trace or CPU profile. For scripts/buildSrc, hashing, transforms, network I/O, JIT/GC and task cache outcomes, capture Gradle operations and profiles alongside spans.

This repository already has `tools/gradle-import-profile/README.md` and the `./measure` helper. **Do not run it casually on a working checkout**: its documented protocol resets project build/cache directories, creates isolated Gradle state and temporarily changes indexing behavior. Review its controls first. Its default approximates cold project outputs with warm global caches and a warm IDE, not the profiler scenarios in the existing results. It writes outside the checkout by default; copy the selected run's complete raw files into `bin/captures/<run-id>/` if using it for this overview. Its local in-memory external-system telemetry wrapper can change the export path, so do not assume simultaneous Jaeger collection is unaffected.

Run unprofiled controls with equivalent state. Preserve overhead and instrumentation versions; never subtract an assumed constant overhead or treat profile samples as exact timers. See [interpretation rules](span-reference.md).
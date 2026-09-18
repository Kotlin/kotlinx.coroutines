# Supplied telemetry recipe (historical input, not verified for every version)

The user stated there was no public documentation and supplied this procedure. The original key spelling and Compose port list are retained here; see [the adapted recipe](../telemetry/collection.md) for source-verified differences.

## Infrastructure preconditions

Run required infrastructure services in a single docker-container by using docker-compose `docker-compose.yml`:

```yaml
version: "3.9"
services:
  jaeger:
    container_name: jaeger
    image: jaegertracing/all-in-one
    ports:
      - "6831:6831"
      - "6832:6832"
      - "5778:5778"
      - "16686:16686"
      - "4317:4317"
      - "4318:4318"
      - "14250:14250"
      - "14268:14268"
      - "14269:14269"
      - "9411:9411"
```

```sh
docker-compose up -d
```

Jaeger UI will be available on port `16686`.

## IDE preconditions

Enable collection in IDEA: **Help → Edit Custom VM Options…**

```text
-Didea.diagnostic.opentelemetry.otlp=http://localhost:4318
```

For Gradle-daemon telemetry, enable `gradle.daemon.opentelemetry.enabled` in Registry.

## How to

Run Gradle Sync; wait for Sync to end. Shut down the IDE to forcefully flush recorded telemetry or wait a minute or two for auto-flush. Open Jaeger and search for `Progress: Importing '%Project Name%' Gradle Project`. The supplied example was `Progress: Importing 'gradle' Gradle: Project`.

**Preservation note:** this page records the supplied instructions, not observed collection results. Its key name, export wait and shutdown assumptions are qualified in the adapted recipe and span reference.
package coroutines.profile;

import com.google.gson.Gson;
import com.google.gson.JsonObject;
import com.intellij.openapi.Disposable;
import com.intellij.openapi.actionSystem.*;
import com.intellij.openapi.application.ApplicationInfo;
import com.intellij.openapi.application.ApplicationManager;
import com.intellij.openapi.externalSystem.autoimport.ExternalSystemProjectTrackerSettings;
import com.intellij.openapi.externalSystem.importing.ImportSpecBuilder;
import com.intellij.openapi.externalSystem.model.ProjectSystemId;
import com.intellij.openapi.externalSystem.model.task.*;
import com.intellij.openapi.externalSystem.service.execution.ProgressExecutionMode;
import com.intellij.openapi.externalSystem.service.internal.ExternalSystemProcessingManager;
import com.intellij.openapi.externalSystem.service.notification.ExternalSystemProgressNotificationManager;
import com.intellij.openapi.externalSystem.service.project.manage.ProjectDataImportListener;
import com.intellij.openapi.externalSystem.util.ExternalSystemApiUtil;
import com.intellij.openapi.externalSystem.util.ExternalSystemUtil;
import com.intellij.openapi.fileEditor.FileDocumentManager;
import com.intellij.openapi.project.DumbAwareAction;
import com.intellij.openapi.project.DumbService;
import com.intellij.openapi.project.Project;
import com.intellij.openapi.project.ProjectManager;
import com.intellij.openapi.project.UnindexedFilesScannerExecutor;
import com.intellij.openapi.util.Disposer;
import com.intellij.openapi.ui.Messages;
import com.intellij.util.indexing.PerProjectIndexingQueue;
import com.intellij.util.indexing.UnindexedFilesScanner;
import com.intellij.util.indexing.UnindexedFilesScannerExecutorImpl;
import com.intellij.util.indexing.DumbModeWhileScanningTrigger;
import kotlinx.coroutines.CoroutineScope;
import kotlinx.coroutines.Job;
import org.jetbrains.plugins.gradle.service.execution.GradleExecutionContext;
import org.jetbrains.plugins.gradle.service.project.GradleExecutionHelperExtension;
import org.jetbrains.plugins.gradle.settings.GradleExecutionSettings;
import org.jetbrains.plugins.gradle.settings.GradleLocalSettings;
import org.jetbrains.plugins.gradle.settings.GradleSettings;
import org.jetbrains.plugins.gradle.settings.DistributionType;

import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;

/** Loaded through IDEA's ideScript command; no restart or installed plugin required. */
public final class IdeaBridge {
    private static final Gson JSON = new Gson();
    private static final ProjectSystemId GRADLE = new ProjectSystemId("GRADLE");
    private static final String ACTION = "Coroutines.ProfileColdGradleImport";
    private static final String SKIP_INDEXING = "idea.indexes.pretendNoFiles";
    private final Path state;
    private final Path tool;
    private final String python;
    private final String fingerprint;
    private final Project project;
    private final Disposable lifetime = Disposer.newDisposable("Coroutines import profiler");
    private volatile boolean closed;
    private volatile Session session;
    private AnAction action;

    private static final class Session {
        ImportTelemetry telemetry;
        String originalHome;
        String originalInstallation;
        DistributionType originalDistribution;
        boolean originalOffline;
        ExternalSystemProjectTrackerSettings.AutoReloadType originalReload;
        Path run;
        String agent;
        volatile boolean importing, callbackDone, modelDone;
        volatile ExternalSystemTaskId taskId;
        final Map<String, Object> events = new LinkedHashMap<>();
        Disposable listeners;
        final CountDownLatch resumeIndexing = new CountDownLatch(1);
        final CompletableFuture<Void> indexingPaused = new CompletableFuture<>();
        final CompletableFuture<Void> indexingResumed = new CompletableFuture<>();
        boolean pauseRequested;
        String originalSkipIndexing;
        boolean indexingGuardInstalled;
        Disposable scanFilter;
        final java.util.concurrent.atomic.AtomicInteger deferredScans = new java.util.concurrent.atomic.AtomicInteger();
        boolean scanningTriggerStopped;
        Project indexingProject;
        final List<Session> otherIndexingProjects = new ArrayList<>();
    }

    public static void install(String state, String tool, String root, String python, String fingerprint) throws Exception {
        Project project = Arrays.stream(ProjectManager.getInstance().getOpenProjects())
            .filter(p -> root.equals(p.getBasePath())).findFirst()
            .orElseThrow(() -> new IllegalStateException("Open this project in IDEA first: " + root));
        if (!ExternalSystemApiUtil.isInProcessMode(GRADLE))
            throw new IllegalStateException("This driver requires IDEA's in-process Gradle Tooling API mode");
        new IdeaBridge(Path.of(state), Path.of(tool), project, python, fingerprint).start();
    }

    private IdeaBridge(Path state, Path tool, Project project, String python, String fingerprint) {
        this.state = state; this.tool = tool; this.project = project; this.python = python; this.fingerprint = fingerprint;
    }

    private void start() throws Exception {
        Files.createDirectories(state.resolve("inbox"));
        Files.createDirectories(state.resolve("replies"));
        ApplicationManager.getApplication().invokeAndWait(() -> {
            ActionManager manager = ActionManager.getInstance();
            if (manager.getAction(ACTION) != null)
                throw new IllegalStateException("Profiler action already installed; uninstall the old driver first");
            action = new DumbAwareAction("Profile Cold Gradle Import", "Reset Gradle state and record CPU + allocations", null) {
                @Override public void actionPerformed(AnActionEvent e) {
                    try {
                        ProcessBuilder builder = new ProcessBuilder(python, tool.resolve("profile_import.py").toString(), "run", "--allow-concurrent", "--project", project.getBasePath())
                            .directory(tool.toFile()).redirectErrorStream(true)
                            .redirectOutput(ProcessBuilder.Redirect.appendTo(state.resolve("launcher.log").toFile()));
                        builder.environment().put("IMPORT_PROFILE_STATE", state.getParent().toString());
                        Process process = builder.start();
                        ApplicationManager.getApplication().executeOnPooledThread(() -> {
                            try {
                                if (process.waitFor() != 0) ApplicationManager.getApplication().invokeLater(() ->
                                    Messages.showErrorDialog(project, "Import profiling failed. Details: " + state.resolve("launcher.log"), "Gradle Import Profiler"));
                            } catch (InterruptedException ex) { Thread.currentThread().interrupt(); }
                        });
                    } catch (IOException ex) { throw new UncheckedIOException(ex); }
                }
            };
            manager.registerAction(ACTION, action);
            ((DefaultActionGroup) manager.getAction("ToolsMenu")).add(action);
        });
        Disposer.register(project, lifetime);
        heartbeat();
        Thread worker = new Thread(this::loop, "coroutines-import-profiler-control");
        worker.setDaemon(true);
        worker.start();
    }

    private void heartbeat() throws IOException {
        write(state.resolve("bridge.json"), Map.of("pid", ProcessHandle.current().pid(),
            "project", project.getBasePath(), "ideaBuild", ApplicationInfo.getInstance().getBuild().asString(),
            "javaVersion", System.getProperty("java.runtime.version"), "javaHome", System.getProperty("java.home"),
            "heartbeat", System.currentTimeMillis()));
    }

    private void loop() {
        long lastHeartbeat = System.currentTimeMillis();
        while (!closed && !project.isDisposed()) {
            try {
                try (var files = Files.list(state.resolve("inbox"))) {
                    for (Path file : files.filter(p -> p.toString().endsWith(".json")).sorted().toList()) {
                        Path reply = state.resolve("replies").resolve(file.getFileName());
                        try {
                            JsonObject request = JSON.fromJson(Files.readString(file), JsonObject.class);
                            write(reply, Map.of("ok", true, "result", command(request)));
                        } catch (Throwable t) {
                            StringWriter trace = new StringWriter(); t.printStackTrace(new PrintWriter(trace));
                            write(reply, Map.of("ok", false, "error", trace.toString()));
                        } finally { Files.deleteIfExists(file); }
                    }
                }
                if (!closed && System.currentTimeMillis() - lastHeartbeat >= 1000) {
                    heartbeat(); lastHeartbeat = System.currentTimeMillis();
                }
                Thread.sleep(100);
            } catch (Throwable t) {
                try { Files.writeString(state.resolve("bridge-error.log"), t + "\n", StandardOpenOption.CREATE, StandardOpenOption.APPEND); }
                catch (IOException ignored) { }
            }
        }
    }

    private Map<String, Object> command(JsonObject request) throws Exception {
        switch (request.get("command").getAsString()) {
            case "info": return info();
            case "prepare": {
                if (session != null) throw new IllegalStateException("Previous measurement has not been restored");
                checkIdle();
                Session s = new Session();
                ApplicationManager.getApplication().invokeAndWait(() -> {
                    GradleSettings settings = GradleSettings.getInstance(project);
                    var tracker = ExternalSystemProjectTrackerSettings.getInstance(project);
                    s.originalHome = settings.getServiceDirectoryPath();
                    var linked = settings.getLinkedProjectSettings(project.getBasePath());
                    s.originalInstallation = linked.getGradleHome();
                    s.originalDistribution = linked.getDistributionType();
                    s.originalOffline = settings.isOfflineWork();
                    s.originalReload = tracker.getAutoReloadType();
                    tracker.setAutoReloadType(ExternalSystemProjectTrackerSettings.AutoReloadType.NONE);
                    FileDocumentManager.getInstance().saveAllDocuments();
                });
                session = s;
                try {
                    checkIdle();
                    if (!request.has("indexing") || request.get("indexing").getAsString().equals("paused"))
                        pauseIndexing(s);
                }
                catch (Exception error) {
                    resumeIndexing(s);
                    ApplicationManager.getApplication().invokeAndWait(() ->
                        ExternalSystemProjectTrackerSettings.getInstance(project).setAutoReloadType(s.originalReload));
                    session = null;
                    throw error;
                }
                return info();
            }
            case "import": {
                checkIdle();
                Session s = Objects.requireNonNull(session, "Call prepare before import");
                if (s.importing) throw new IllegalStateException("An import is already running");
                s.run = Path.of(request.get("run").getAsString());
                s.agent = request.has("agent") ? request.get("agent").getAsString() : "";
                s.callbackDone = false; s.modelDone = false; s.events.clear();
                s.listeners = Disposer.newDisposable(lifetime, "Import measurement listeners");
                if (request.has("trace") && request.get("trace").getAsBoolean())
                    s.telemetry = new ImportTelemetry(s.run.resolve("idea-spans.json"));
                if (s.pauseRequested && !DumbService.getInstance(project).waitForSmartMode(20_000))
                    throw new IllegalStateException("IDEA did not reach smart mode with indexing deferred");
                project.getMessageBus().connect(s.listeners).subscribe(ProjectDataImportListener.TOPIC, new ProjectDataImportListener() {
                    @Override public void onImportStarted(String path) { if (matches(path)) event(s, "model_started"); }
                    @Override public void onImportFinished(String path) { if (matches(path)) event(s, "model_applied"); }
                    @Override public void onFinalTasksFinished(String path) {
                        if (matches(path)) { s.modelDone = true; event(s, "model_final_tasks_finished"); finishIfReady(s); }
                    }
                    @Override public void onImportFailed(String path, Throwable error) {
                        if (matches(path)) fail(s, "Model application failed: " + error);
                    }
                    @Override public void onImportFailed(String path) { if (matches(path)) fail(s, "Model application failed"); }
                });
                ExternalSystemProgressNotificationManager.getInstance().addNotificationListener(new ExternalSystemTaskNotificationListener() {
                    @Override public void onStart(String path, ExternalSystemTaskId id) {
                        if (matches(path) && id.getType() == ExternalSystemTaskType.RESOLVE_PROJECT) {
                            if (s.taskId != null && !s.taskId.equals(id)) { fail(s, "Unexpected overlapping import"); return; }
                            s.taskId = id; event(s, "gradle_task_started");
                        }
                    }
                    @Override public void onTaskOutput(ExternalSystemTaskId id, String text, boolean stdout) {
                        if (id.equals(s.taskId)) {
                            try { synchronized (s) { Files.writeString(s.run.resolve("import.log"), text, StandardOpenOption.CREATE, StandardOpenOption.APPEND); } }
                            catch (IOException ex) { fail(s, ex.toString()); }
                        }
                    }
                    @Override public void onFailure(String path, ExternalSystemTaskId id, Exception ex) { if (matches(path)) fail(s, ex.toString()); }
                    @Override public void onCancel(String path, ExternalSystemTaskId id) { if (matches(path)) fail(s, "Import cancelled"); }
                }, s.listeners);
                if (!s.agent.isEmpty()) {
                    GradleExecutionHelperExtension.EP_NAME.getPoint().registerExtension(new GradleExecutionHelperExtension() {
                        @Override public void configureSettings(GradleExecutionSettings settings, GradleExecutionContext context) {
                            if (context.getTaskId().findProject() == project && s.importing) {
                                // Gradle's daemon gets its agent via org.gradle.jvmargs. Build environment
                                // variables propagate the agent to Kotlin and worker JVMs from startup.
                                String previous = settings.getEnv().getOrDefault("JAVA_TOOL_OPTIONS", System.getenv().getOrDefault("JAVA_TOOL_OPTIONS", ""));
                                settings.addEnvironmentVariable("JAVA_TOOL_OPTIONS", (previous + " " + s.agent).trim());
                                event(s, "child_environment_configured");
                            }
                        }
                    }, s.listeners);
                }
                ApplicationManager.getApplication().invokeAndWait(() -> {
                    GradleSettings settings = GradleSettings.getInstance(project);
                    // The public GradleSettings setter publishes a settings-change
                    // event that schedules another sync even with auto-reload off.
                    // This temporary override must belong only to our explicit import.
                    GradleLocalSettings.getInstance(project).setGradleUserHome(request.get("gradleHome").getAsString());
                    settings.setOfflineWork(request.get("offline").getAsBoolean());
                    if (request.has("gradleInstallation") && !request.get("gradleInstallation").getAsString().isEmpty()) {
                        var linked = settings.getLinkedProjectSettings(project.getBasePath());
                        linked.setGradleHome(request.get("gradleInstallation").getAsString());
                        linked.setDistributionType(DistributionType.LOCAL);
                    }
                });
                s.taskId = null;
                s.importing = true;
                CompletableFuture<Void> callback = new CompletableFuture<>();
                callback.whenComplete((unused, error) -> {
                    if (error != null) fail(s, error.toString());
                    else { s.callbackDone = true; event(s, "sync_callback_finished"); finishIfReady(s); }
                });
                ImportSpecBuilder spec = new ImportSpecBuilder(project, GRADLE)
                    .use(ProgressExecutionMode.IN_BACKGROUND_ASYNC).withImportProjectData(true)
                    .withArguments(request.has("globalCaches") && request.get("globalCaches").getAsString().equals("warm")
                        ? "--info" : "--no-build-cache --no-configuration-cache --info")
                    .withCallback(callback).withActivateToolWindowOnStart(false);
                event(s, "import_requested");
                ExternalSystemUtil.refreshProject(project.getBasePath(), spec);
                return Map.of("started", true);
            }
            case "restore": {
                Session s = session;
                if (s != null) {
                    // Release first, including on cancellation or settings-restoration failure.
                    resumeIndexing(s);
                    if (s.importing) {
                        if (s.taskId != null) {
                            var task = ExternalSystemProcessingManager.getInstance().findTask(s.taskId);
                            if (task != null) task.cancel();
                        }
                        fail(s, "Stopped by runner");
                    }
                    if (s.telemetry != null) { s.telemetry.close(); s.telemetry = null; }
                    if (s.listeners != null) Disposer.dispose(s.listeners);
                    ApplicationManager.getApplication().invokeAndWait(() -> {
                        GradleSettings settings = GradleSettings.getInstance(project);
                        GradleLocalSettings.getInstance(project).setGradleUserHome(s.originalHome);
                        settings.setOfflineWork(s.originalOffline);
                        var linked = settings.getLinkedProjectSettings(project.getBasePath());
                        linked.setGradleHome(s.originalInstallation);
                        linked.setDistributionType(s.originalDistribution);
                        ExternalSystemProjectTrackerSettings.getInstance(project).setAutoReloadType(s.originalReload);
                    });
                    session = null;
                }
                return Map.of("restored", true);
            }
            case "close": {
                if (session != null) throw new IllegalStateException("Restore before uninstalling");
                ApplicationManager.getApplication().invokeAndWait(() -> {
                    ActionManager manager = ActionManager.getInstance();
                    ((DefaultActionGroup) manager.getAction("ToolsMenu")).remove(action);
                    manager.unregisterAction(ACTION);
                });
                closed = true; Disposer.dispose(lifetime); Files.deleteIfExists(state.resolve("bridge.json"));
                return Map.of("closed", true);
            }
            default: throw new IllegalArgumentException("Unknown command");
        }
    }

    private Map<String, Object> info() {
        GradleSettings settings = GradleSettings.getInstance(project);
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("pid", ProcessHandle.current().pid());
        result.put("driverFingerprint", fingerprint);
        result.put("project", project.getBasePath());
        result.put("openProjects", Arrays.stream(ProjectManager.getInstance().getOpenProjects())
            .map(Project::getBasePath).filter(Objects::nonNull).toList());
        result.put("gradleHome", settings.getServiceDirectoryPath());
        result.put("gradleVmOptions", settings.getGradleVmOptions());
        result.put("gradleDistribution", String.valueOf(settings.getLinkedProjectSettings(project.getBasePath()).getDistributionType()));
        result.put("gradleInstallation", settings.getLinkedProjectSettings(project.getBasePath()).getGradleHome());
        result.put("gradleJvm", settings.getLinkedProjectSettings(project.getBasePath()).getGradleJvm());
        result.put("ideaBuild", ApplicationInfo.getInstance().getBuild().asString());
        result.put("javaVersion", System.getProperty("java.runtime.version"));
        result.put("prepared", session != null);
        result.put("indexingPaused", session != null && session.pauseRequested &&
            session.indexingPaused.isDone() && !session.indexingResumed.isDone());
        result.put("dumbMode", DumbService.isDumb(project));
        result.put("scanningDeferred", session != null && session.scanFilter != null);
        result.put("contentIndexingDeferred", session != null && session.indexingGuardInstalled && Boolean.getBoolean(SKIP_INDEXING));
        result.put("skipIndexingProperty", System.getProperty(SKIP_INDEXING));
        result.put("pausedIndexingProjects", session == null || !session.pauseRequested ? List.of() :
            java.util.stream.Stream.concat(java.util.stream.Stream.of(session), session.otherIndexingProjects.stream())
                .map(s -> s.indexingProject.getBasePath()).toList());
        result.put("deferredScanningRequests", session == null ? 0 : session.deferredScans.get());
        result.put("actionInstalled", ActionManager.getInstance().getAction(ACTION) == action);
        return result;
    }

    private boolean matches(String path) { return project.getBasePath().equals(path); }

    private void pauseIndexing(Session s) throws Exception {
        pauseProjectIndexing(s, project);
        for (Project other : ProjectManager.getInstance().getOpenProjects()) {
            if (other == project || other.isDisposed()) continue;
            Session pause = new Session();
            s.otherIndexingProjects.add(pause);
            pauseProjectIndexing(pause, other);
        }
        // Drain the queues before enabling the guard: their observer otherwise
        // waits forever for files that a skipped indexer cannot consume.
        // VFS refresh can queue an indexer directly, bypassing PerProjectIndexingQueue.
        s.originalSkipIndexing = System.getProperty(SKIP_INDEXING);
        System.setProperty(SKIP_INDEXING, "true");
        s.indexingGuardInstalled = true;
        Disposer.register(lifetime, () -> restoreIndexingGuard(s));
        waitForIndexingIdle(project);
        for (Session pause : s.otherIndexingProjects) waitForIndexingIdle(pause.indexingProject);
    }

    private void waitForIndexingIdle(Project project) throws Exception {
        var scanner = UnindexedFilesScannerExecutor.getInstance(project);
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(120);
        while (DumbService.isDumb(project) || scanner.isRunning().getValue() || scanner.getHasQueuedTasks()) {
            if (System.nanoTime() > deadline)
                throw new IllegalStateException("IDEA scanning/indexing did not become idle before measurement");
            Thread.sleep(100);
        }
    }

    private void pauseProjectIndexing(Session s, Project project) throws Exception {
        s.indexingProject = project;
        var scanner = UnindexedFilesScannerExecutor.getInstance(project);
        // Suspending an active dumb task prevents Kotlin DSL's smart read action
        // from completing. Drain existing work outside the timed interval.
        waitForIndexingIdle(project);
        // A suspended queue still advertises pending scans as "running", which
        // blocks SmartModeScheduler and Kotlin DSL model refinement. Suppress
        // requests before they enter the queue, then replace them with a full
        // rescan after recording. No index contents or source files are dropped.
        s.scanFilter = Disposer.newDisposable("Deferred import scanning");
        ((UnindexedFilesScannerExecutorImpl) scanner).setTaskFilterInTest(s.scanFilter, task -> {
            s.deferredScans.incrementAndGet();
            return false;
        });
        // This IDEA service otherwise enters dumb mode when >20 files await
        // indexing, even when both work queues are held. Pause its one observer,
        // not the project/service scope, and resubscribe during restoration.
        var trigger = project.getService(DumbModeWhileScanningTrigger.class);
        var scopeField = DumbModeWhileScanningTrigger.class.getDeclaredField("coroutineScope");
        scopeField.setAccessible(true);
        var scope = (CoroutineScope) scopeField.get(trigger);
        Job serviceJob = Objects.requireNonNull(scope.getCoroutineContext().get(Job.Key));
        List<Job> observers = new ArrayList<>();
        serviceJob.getChildren().iterator().forEachRemaining(observers::add);
        if (observers.size() != 1)
            throw new IllegalStateException("Unexpected scanning observer topology: " + observers.size());
        Job observer = observers.get(0);
        observer.cancel(new CancellationException("Defer scanning during import profiling"));
        s.scanningTriggerStopped = true;
        long observerDeadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(20);
        while (!observer.isCompleted()) {
            if (System.nanoTime() > observerDeadline)
                throw new IllegalStateException("Scanning observer did not stop");
            Thread.sleep(10);
        }
        s.pauseRequested = true;
        Disposer.register(lifetime, () -> s.resumeIndexing.countDown());
        Thread holder = new Thread(() -> {
            try {
                project.getService(PerProjectIndexingQueue.class).disableFlushingDuring(() -> {
                        s.indexingPaused.complete(null);
                        try { s.resumeIndexing.await(); }
                        catch (InterruptedException e) { Thread.currentThread().interrupt(); }
                        return null;
                    });
                resumeQueues(s);
                s.indexingResumed.complete(null);
            } catch (Throwable error) {
                resumeQueues(s);
                s.indexingPaused.completeExceptionally(error);
                s.indexingResumed.completeExceptionally(error);
            }
        }, "coroutines-import-profiler-indexing-pause");
        holder.setDaemon(true);
        holder.start();
        s.indexingPaused.get(20, TimeUnit.SECONDS);
    }

    private void resumeIndexing(Session s) throws Exception {
        restoreIndexingGuard(s);
        Exception failure = null;
        List<Session> all = new ArrayList<>(s.otherIndexingProjects);
        all.add(s);
        for (Session pause : all) {
            try { resumeProjectIndexing(pause); }
            catch (Exception error) {
                if (failure == null) failure = error;
                else failure.addSuppressed(error);
            }
        }
        if (failure != null) throw failure;
    }

    private synchronized void restoreIndexingGuard(Session s) {
        if (!s.indexingGuardInstalled) return;
        if (s.originalSkipIndexing == null) System.clearProperty(SKIP_INDEXING);
        else System.setProperty(SKIP_INDEXING, s.originalSkipIndexing);
        s.indexingGuardInstalled = false;
    }

    private void resumeProjectIndexing(Session s) throws Exception {
        s.resumeIndexing.countDown();
        try {
            if (s.pauseRequested) s.indexingResumed.get(20, TimeUnit.SECONDS);
        } finally { resumeQueues(s); }
    }

    private synchronized void resumeQueues(Session s) {
        Project project = s.indexingProject;
        if (project == null || project.isDisposed()) {
            if (s.scanFilter != null) Disposer.dispose(s.scanFilter);
            s.scanFilter = null;
            return;
        }
        if (s.scanningTriggerStopped) {
            project.getService(DumbModeWhileScanningTrigger.class).subscribe();
            s.scanningTriggerStopped = false;
        }
        if (s.scanFilter != null) {
            Disposer.dispose(s.scanFilter);
            s.scanFilter = null;
            // A VFS-triggered indexer can be skipped even without a scanning request.
            new UnindexedFilesScanner(project, "Deferred scanning after import profiling").queue();
            project.getService(PerProjectIndexingQueue.class).flushNow("Import profiling finished");
        }
    }

    private void checkIdle() {
        for (ExternalSystemTaskType type : ExternalSystemTaskType.values())
            if (ExternalSystemProcessingManager.getInstance().hasTaskOfTypeInProgress(type, project))
                throw new IllegalStateException("Wait for the current IDEA build/import to finish: " + type);
    }

    private void event(Session s, String name) {
        synchronized (s) {
            s.events.put(name, System.currentTimeMillis());
            try { write(s.run.resolve("events.json"), s.events); }
            catch (IOException ex) { throw new UncheckedIOException(ex); }
        }
    }

    private void finishIfReady(Session s) {
        synchronized (s) {
            if (!s.importing || !s.callbackDone || !s.modelDone) return;
            event(s, "finished"); s.importing = false;
            try { write(s.run.resolve("result.json"), Map.of("ok", true, "events", s.events)); }
            catch (IOException ex) { throw new UncheckedIOException(ex); }
        }
    }

    private void fail(Session s, String error) {
        synchronized (s) {
            if (!s.importing) return;
            event(s, "failed"); s.importing = false;
            try { write(s.run.resolve("result.json"), Map.of("ok", false, "error", error, "events", s.events)); }
            catch (IOException ex) { throw new UncheckedIOException(ex); }
        }
    }

    private static void write(Path path, Object value) throws IOException {
        Path temp = path.resolveSibling(path.getFileName() + ".tmp");
        Files.writeString(temp, JSON.toJson(value));
        Files.move(temp, path, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE);
    }
}

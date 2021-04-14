/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow.scrabble.optimizations;

import io.reactivex.Flowable;
import io.reactivex.FlowableTransformer;
import io.reactivex.exceptions.Exceptions;
import io.reactivex.internal.fuseable.ConditionalSubscriber;
import io.reactivex.internal.fuseable.SimplePlainQueue;
import io.reactivex.internal.queue.SpscArrayQueue;
import io.reactivex.internal.subscriptions.SubscriptionHelper;
import io.reactivex.internal.util.BackpressureHelper;
import io.reactivex.plugins.RxJavaPlugins;
import org.reactivestreams.Publisher;
import org.reactivestreams.Subscriber;
import org.reactivestreams.Subscription;

import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Pattern;

final class FlowableSplit extends Flowable<String> implements FlowableTransformer<String, String> {

    final Publisher<String> source;

    final Pattern pattern;

    final int bufferSize;

    FlowableSplit(Publisher<String> source, Pattern pattern, int bufferSize) {
        this.source = source;
        this.pattern = pattern;
        this.bufferSize = bufferSize;
    }

    @Override
    public Publisher<String> apply(Flowable<String> upstream) {
        return new FlowableSplit(upstream, pattern, bufferSize);
    }

    @Override
    protected void subscribeActual(Subscriber<? super String> s) {
        source.subscribe(new SplitSubscriber(s, pattern, bufferSize));
    }

    static final class SplitSubscriber
            extends AtomicInteger
            implements ConditionalSubscriber<String>, Subscription {

        static final String[] EMPTY = new String[0];

        private static final long serialVersionUID = -5022617259701794064L;

        final Subscriber<? super String> downstream;

        final Pattern pattern;

        final SimplePlainQueue<String[]> queue;

        final AtomicLong requested;

        final int bufferSize;

        final int limit;

        Subscription upstream;

        volatile boolean cancelled;

        String leftOver;

        String[] current;

        int index;

        int produced;

        volatile boolean done;
        Throwable error;

        int empty;

        SplitSubscriber(Subscriber<? super String> downstream, Pattern pattern, int bufferSize) {
            this.downstream = downstream;
            this.pattern = pattern;
            this.bufferSize = bufferSize;
            this.limit = bufferSize - (bufferSize >> 2);
            this.queue = new SpscArrayQueue<String[]>(bufferSize);
            this.requested = new AtomicLong();
        }

        @Override
        public void request(long n) {
            if (SubscriptionHelper.validate(n)) {
                BackpressureHelper.add(requested, n);
                drain();
            }
        }

        @Override
        public void cancel() {
            cancelled = true;
            upstream.cancel();

            if (getAndIncrement() == 0) {
                current = null;
                queue.clear();
            }
        }

        @Override
        public void onSubscribe(Subscription s) {
            if (SubscriptionHelper.validate(this.upstream, s)) {
                this.upstream = s;

                downstream.onSubscribe(this);

                s.request(bufferSize);
            }
        }

        @Override
        public void onNext(String t) {
            if (!tryOnNext(t)) {
                upstream.request(1);
            }
        }

        @Override
        public boolean tryOnNext(String t) {
            String lo = leftOver;
            String[] a;
            try {
                if (lo == null || lo.isEmpty()) {
                    a = pattern.split(t, -1);
                } else {
                    a = pattern.split(lo + t, -1);
                }
            } catch (Throwable ex) {
                Exceptions.throwIfFatal(ex);
                this.upstream.cancel();
                onError(ex);
                return true;
            }

            if (a.length == 0) {
                leftOver = null;
                return false;
            } else
            if (a.length == 1) {
                leftOver = a[0];
                return false;
            }
            leftOver = a[a.length - 1];
            queue.offer(a);
            drain();
            return true;
        }

        @Override
        public void onError(Throwable t) {
            if (done) {
                RxJavaPlugins.onError(t);
                return;
            }
            String lo = leftOver;
            if (lo != null && !lo.isEmpty()) {
                leftOver = null;
                queue.offer(new String[] { lo, null });
            }
            error = t;
            done = true;
            drain();
        }

        @Override
        public void onComplete() {
            if (!done) {
                done = true;
                String lo = leftOver;
                if (lo != null && !lo.isEmpty()) {
                    leftOver = null;
                    queue.offer(new String[] { lo, null });
                }
                drain();
            }
        }

        void drain() {
            if (getAndIncrement() != 0) {
                return;
            }

            SimplePlainQueue<String[]> q = queue;

            int missed = 1;
            int consumed = produced;
            String[] array = current;
            int idx = index;
            int emptyCount = empty;

            Subscriber<? super String> a = downstream;

            for (;;) {
                long r = requested.get();
                long e = 0;

                while (e != r) {
                    if (cancelled) {
                        current = null;
                        q.clear();
                        return;
                    }

                    boolean d = done;

                    if (array == null) {
                        array = q.poll();
                        if (array != null) {
                            current = array;
                            if (++consumed == limit) {
                                consumed = 0;
                                upstream.request(limit);
                            }
                        }
                    }

                    boolean empty = array == null;

                    if (d && empty) {
                        current = null;
                        Throwable ex = error;
                        if (ex != null) {
                            a.onError(ex);
                        } else {
                            a.onComplete();
                        }
                        return;
                    }

                    if (empty) {
                        break;
                    }

                    if (array.length == idx + 1) {
                        array = null;
                        current = null;
                        idx = 0;
                        continue;
                    }

                    String v = array[idx];

                    if (v.isEmpty()) {
                        emptyCount++;
                        idx++;
                    } else {
                        while (emptyCount != 0 && e != r) {
                            if (cancelled) {
                                current = null;
                                q.clear();
                                return;
                            }
                            a.onNext("");
                            e++;
                            emptyCount--;
                        }

                        if (e != r && emptyCount == 0) {
                            a.onNext(v);

                            e++;
                            idx++;
                        }
                    }
                }

                if (e == r) {
                    if (cancelled) {
                        current = null;
                        q.clear();
                        return;
                    }

                    boolean d = done;

                    if (array == null) {
                        array = q.poll();
                        if (array != null) {
                            current = array;
                            if (++consumed == limit) {
                                consumed = 0;
                                upstream.request(limit);
                            }
                        }
                    }

                    boolean empty = array == null;

                    if (d && empty) {
                        current = null;
                        Throwable ex = error;
                        if (ex != null) {
                            a.onError(ex);
                        } else {
                            a.onComplete();
                        }
                        return;
                    }
                }

                if (e != 0L) {
                    BackpressureHelper.produced(requested, e);
                }

                empty = emptyCount;
                produced = consumed;
                missed = addAndGet(-missed);
                if (missed == 0) {
                    break;
                }
            }
        }
    }
}

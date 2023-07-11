/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow.scrabble.optimizations;

import io.reactivex.Flowable;
import io.reactivex.internal.fuseable.QueueFuseable;
import io.reactivex.internal.subscriptions.BasicQueueSubscription;
import io.reactivex.internal.subscriptions.SubscriptionHelper;
import io.reactivex.internal.util.BackpressureHelper;
import org.reactivestreams.Subscriber;

final class FlowableCharSequence extends Flowable<Integer> {

    final CharSequence string;

    FlowableCharSequence(CharSequence string) {
        this.string = string;
    }

    @Override
    public void subscribeActual(Subscriber<? super Integer> s) {
        s.onSubscribe(new CharSequenceSubscription(s, string));
    }

    static final class CharSequenceSubscription
            extends BasicQueueSubscription<Integer> {

        private static final long serialVersionUID = -4593793201463047197L;

        final Subscriber<? super Integer> downstream;

        final CharSequence string;

        final int end;

        int index;

        volatile boolean cancelled;

        CharSequenceSubscription(Subscriber<? super Integer> downstream, CharSequence string) {
            this.downstream = downstream;
            this.string = string;
            this.end = string.length();
        }

        @Override
        public void cancel() {
            cancelled = true;
        }

        @Override
        public void request(long n) {
            if (SubscriptionHelper.validate(n)) {
                if (BackpressureHelper.add(this, n) == 0) {
                    if (n == Long.MAX_VALUE) {
                        fastPath();
                    } else {
                        slowPath(n);
                    }
                }
            }
        }

        void fastPath() {
            int e = end;
            CharSequence s = string;
            Subscriber<? super Integer> a = downstream;

            for (int i = index; i != e; i++) {
                if (cancelled) {
                    return;
                }

                a.onNext((int)s.charAt(i));
            }

            if (!cancelled) {
                a.onComplete();
            }
        }

        void slowPath(long r) {
            long e = 0L;
            int i = index;
            int f = end;
            CharSequence s = string;
            Subscriber<? super Integer> a = downstream;

            for (;;) {

                while (e != r && i != f) {
                    if (cancelled) {
                        return;
                    }

                    a.onNext((int)s.charAt(i));

                    i++;
                    e++;
                }

                if (i == f) {
                    if (!cancelled) {
                        a.onComplete();
                    }
                    return;
                }

                r = get();
                if (e == r) {
                    index = i;
                    r = addAndGet(-e);
                    if (r == 0L) {
                        break;
                    }
                    e = 0L;
                }
            }
        }

        @Override
        public int requestFusion(int requestedMode) {
            return requestedMode & QueueFuseable.SYNC;
        }

        @Override
        public Integer poll() {
            int i = index;
            if (i != end) {
                index = i + 1;
                return (int)string.charAt(i);
            }
            return null;
        }

        @Override
        public boolean isEmpty() {
            return index == end;
        }

        @Override
        public void clear() {
            index = end;
        }
    }

}

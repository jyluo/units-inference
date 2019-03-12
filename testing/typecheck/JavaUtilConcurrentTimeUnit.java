import static java.util.concurrent.TimeUnit.*;

import java.util.concurrent.RejectedExecutionHandler;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import units.UnitsTools;
import units.qual.*;

class JavaUtilConcurrentTimeUnit {
    @SuppressWarnings("units")
    enum MyTimeUnit {
        NANOSECONDS,
        MICROSECONDS,
        @ms
        MILLISECONDS,
        @s SECONDS
    }

    void readFromEnumInSource() {
        @s MyTimeUnit u1 = MyTimeUnit.SECONDS;
        @ms MyTimeUnit u2 = MyTimeUnit.MILLISECONDS;

        MyTimeUnit u3 = MyTimeUnit.MICROSECONDS;
        MyTimeUnit u4 = MyTimeUnit.NANOSECONDS;
    }

    void test(long time, TimeUnit unit) throws Exception {
        @ms long milliseconds = unit.toMillis(time);
        Thread.sleep(milliseconds);
    }

    @s TimeUnit s = TimeUnit.SECONDS;
    @ms TimeUnit ms = TimeUnit.MILLISECONDS;
    @us TimeUnit us = TimeUnit.MICROSECONDS;
    @ns TimeUnit ns = NANOSECONDS;
    Thread t;

    void testConvert() {
        // :: error: (assignment.type.incompatible)
        ms = ns;
        // :: error: (assignment.type.incompatible)
        @ns TimeUnit s1 = TimeUnit.MICROSECONDS;
        // :: error: (assignment.type.incompatible)
        @us TimeUnit s2 = TimeUnit.MILLISECONDS;
        // :: error: (assignment.type.incompatible)
        @ms TimeUnit s3 = TimeUnit.SECONDS;
        // :: error: (assignment.type.incompatible)
        @s TimeUnit s4 = NANOSECONDS;

        // ensure the poly convert works
        @s long sec = s.convert(10L * UnitsTools.ns, NANOSECONDS);
        sec = TimeUnit.SECONDS.convert(10L * UnitsTools.ns, NANOSECONDS);
        @ms long ms = TimeUnit.MILLISECONDS.convert(10L * UnitsTools.min, TimeUnit.MINUTES);
        @us long us = TimeUnit.MICROSECONDS.convert(10L * UnitsTools.h, TimeUnit.HOURS);
        @ns long ns = NANOSECONDS.convert(10L * UnitsTools.day, TimeUnit.DAYS);
    }

    void testToTimeUnit() {
        @ns long d1 = s.toNanos(10);
        @us long d2 = s.toMicros(10);
        @ms long d3 = s.toMillis(10);
        @s long d4 = s.toSeconds(10);
        @min long d5 = s.toMinutes(10);
        @h long d6 = s.toHours(10);
        @day long d7 = s.toDays(10);
    }

    void testWaits() throws InterruptedException {
        s.timedWait("stuff", 100 * UnitsTools.s);
        // :: error: (units.differ)
        s.timedWait("stuff", 100 * UnitsTools.m);

        s.timedJoin(t, 100 * UnitsTools.s);
        // :: error: (units.differ)
        s.timedJoin(t, 100 * UnitsTools.m);

        s.sleep(100 * UnitsTools.s);
        // :: error: (units.differ)
        s.sleep(100 * UnitsTools.m);
    }

    ThreadPoolExecutor tpe;
    ThreadFactory tf;
    RejectedExecutionHandler reh;

    void testThreadPoolExecutor() throws InterruptedException {
        tpe = new ThreadPoolExecutor(0, 0, 10L * UnitsTools.s, TimeUnit.SECONDS, null);
        tpe = new ThreadPoolExecutor(0, 0, 10L * UnitsTools.s, TimeUnit.SECONDS, null, tf);
        tpe = new ThreadPoolExecutor(0, 0, 10L * UnitsTools.s, TimeUnit.SECONDS, null, reh);
        tpe = new ThreadPoolExecutor(0, 0, 10L * UnitsTools.s, TimeUnit.SECONDS, null, tf, reh);

        // :: error: (units.differ)
        tpe = new ThreadPoolExecutor(0, 0, 10L * UnitsTools.s, TimeUnit.DAYS, null);
        // :: error: (units.differ)
        tpe = new ThreadPoolExecutor(0, 0, 10L * UnitsTools.s, TimeUnit.DAYS, null, tf);
        // :: error: (units.differ)
        tpe = new ThreadPoolExecutor(0, 0, 10L * UnitsTools.s, TimeUnit.DAYS, null, reh);
        // :: error: (units.differ)
        tpe = new ThreadPoolExecutor(0, 0, 10L * UnitsTools.s, TimeUnit.DAYS, null, tf, reh);

        tpe.awaitTermination(10L * UnitsTools.s, TimeUnit.SECONDS);
        // :: error: (units.differ)
        tpe.awaitTermination(10L * UnitsTools.s, TimeUnit.DAYS);

        tpe.setKeepAliveTime(10L * UnitsTools.s, TimeUnit.SECONDS);
        // :: error: (units.differ)
        tpe.setKeepAliveTime(10L * UnitsTools.s, TimeUnit.DAYS);

        @s long s = tpe.getKeepAliveTime(TimeUnit.SECONDS);
        @ms long ms = tpe.getKeepAliveTime(TimeUnit.MILLISECONDS);
    }
}

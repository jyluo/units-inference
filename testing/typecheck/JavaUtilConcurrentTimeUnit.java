import units.UnitsTools;
import units.qual.*;

import java.util.concurrent.TimeUnit;
import static java.util.concurrent.TimeUnit.*;

class JavaUtilConcurrentTimeUnit {

    @SuppressWarnings("units") enum MyTimeUnit {
        NANOSECONDS, MICROSECONDS, @ms MILLISECONDS, @s SECONDS
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

    void test2() {
        @s TimeUnit s = TimeUnit.SECONDS;
        @ms TimeUnit ms = TimeUnit.MILLISECONDS;
        @us TimeUnit us = TimeUnit.MICROSECONDS;
        @ns TimeUnit ns = NANOSECONDS;

        // :: error: (assignment.type.incompatible)
        ms = ns;

        // ensure the poly convert works
        @s long seconds = s.convert(10L, NANOSECONDS);

        @s long secondsTwo = TimeUnit.SECONDS.convert(10L, NANOSECONDS);

        // convert 10 minutes to milliseconds
        @ms long milliseconds = TimeUnit.MILLISECONDS.convert(10L, TimeUnit.MINUTES);

        @us long microsec = TimeUnit.MICROSECONDS.convert(10L, TimeUnit.HOURS);

        @ns long nanosec = NANOSECONDS.convert(10L, TimeUnit.DAYS);
    }

    void bad() {
        // :: error: (assignment.type.incompatible)
        @ns TimeUnit s1 = TimeUnit.MICROSECONDS;
        // :: error: (assignment.type.incompatible)
        @us TimeUnit s2 = TimeUnit.MILLISECONDS;
        // :: error: (assignment.type.incompatible)
        @ms TimeUnit s3 = TimeUnit.SECONDS;
        // :: error: (assignment.type.incompatible)
        @s TimeUnit s4 = NANOSECONDS;
    }
}

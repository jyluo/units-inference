import static java.util.concurrent.TimeUnit.*;

import java.util.concurrent.TimeUnit;
import units.qual.*;

class JavaUtilConcurrentTimeUnit {

    void test(long time, TimeUnit unit) throws Exception {
        long milliseconds = unit.toMillis(time);
        Thread.sleep(milliseconds);
    }

    void test2() {
        TimeUnit s = TimeUnit.SECONDS;

        TimeUnit ms = TimeUnit.MILLISECONDS;

        TimeUnit us = TimeUnit.MICROSECONDS;

        TimeUnit ns = NANOSECONDS;

        @s long seconds = s.convert(10L, NANOSECONDS);

        // convert 10 minutes to milliseconds
        @ms long milliseconds = ms.convert(10L, TimeUnit.MINUTES);

        @us long microsec = us.convert(10L, TimeUnit.HOURS);

        @ns long nanosec = ns.convert(10L, TimeUnit.DAYS);
    }
}

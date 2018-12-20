import units.UnitsTools;
import units.qual.*;

import java.util.concurrent.TimeUnit;
import static java.util.concurrent.TimeUnit.*;

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

        long seconds = s.convert(10L, TimeUnit.NANOSECONDS);

        // convert 10 minutes to milliseconds
        long milliseconds = ms.convert(10L, TimeUnit.MINUTES);

        long microsec = us.convert(10L, TimeUnit.HOURS);

        long nanosec = ns.convert(10L, TimeUnit.DAYS);
    }
}

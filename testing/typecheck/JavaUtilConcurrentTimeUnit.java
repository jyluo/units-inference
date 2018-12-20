import units.UnitsTools;
import units.qual.*;

import java.util.concurrent.TimeUnit;
import static java.util.concurrent.TimeUnit.*;

class JavaUtilConcurrentTimeUnit {

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

        @s long seconds = s.convert(10L, TimeUnit.NANOSECONDS);

        // convert 10 minutes to milliseconds
        @ms long milliseconds = ms.convert(10L, TimeUnit.MINUTES);

        @us long microsec = us.convert(10L, TimeUnit.HOURS);

        @ns long nanosec = ns.convert(10L, TimeUnit.DAYS);
    }

    // enum MyTimeUnit {
    // @ms MILLISECONDS;
    // }
    //
    // void test3() {
    // @ms MyTimeUnit unit = MyTimeUnit.MILLISECONDS;
    // }
}

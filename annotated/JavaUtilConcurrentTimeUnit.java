import units.qual.Dimensionless;
import units.qual.ms;
import units.qual.s;
import units.qual.ns;
import units.qual.us;
import static java.util.concurrent.TimeUnit.*;

import java.util.concurrent.TimeUnit;
import units.qual.*;

@Dimensionless
class JavaUtilConcurrentTimeUnit {

    void test(@Dimensionless JavaUtilConcurrentTimeUnit this, @Dimensionless long time, @Dimensionless TimeUnit unit) throws Exception {
        @ms
        long milliseconds = unit.toMillis(time);
        Thread.sleep(milliseconds);
    }

    void test2(@Dimensionless JavaUtilConcurrentTimeUnit this) {
        @s
        TimeUnit s = TimeUnit.SECONDS;

        @ms
        TimeUnit ms = TimeUnit.MILLISECONDS;

        @us
        TimeUnit us = TimeUnit.MICROSECONDS;

        @ns
        TimeUnit ns = NANOSECONDS;

        @s long seconds = s.convert(((@Dimensionless long) (10L)), NANOSECONDS);

        // convert 10 minutes to milliseconds
        @ms long milliseconds = ms.convert(((@Dimensionless long) (10L)), TimeUnit.MINUTES);

        @us long microsec = us.convert(((@Dimensionless long) (10L)), TimeUnit.HOURS);

        @ns long nanosec = ns.convert(((@Dimensionless long) (10L)), TimeUnit.DAYS);
    }

    void testParams(@Dimensionless JavaUtilConcurrentTimeUnit this) {
        @s
        TimeUnit s_unit = TimeUnit.SECONDS;
        @ns
        TimeUnit ns_unit = NANOSECONDS;

        @ns
        long ns = ((@ns int) (1000));
        @s
        long s = ((@s int) (1000));

        // :: fixable-error: (argument.type.incompatible)
        TimeUnit.SECONDS.toMillis(s);
        // :: fixable-error: (argument.type.incompatible)
        TimeUnit.NANOSECONDS.toMillis(ns);

        // :: fixable-error: (argument.type.incompatible)
        ns_unit.toMillis(ns);
        // :: fixable-error: (argument.type.incompatible)
        s_unit.toMillis(s);
    }

    void testReturn(@Dimensionless JavaUtilConcurrentTimeUnit this, @s long s1, @s long s2) {
        @s
        TimeUnit s = TimeUnit.SECONDS;
        @ms
        TimeUnit ms = TimeUnit.MILLISECONDS;

        // :: fixable-error: (assignment.type.incompatible)
        s1 = s.convert(((@Dimensionless long) (10L)), NANOSECONDS);
        // :: fixable-error: (assignment.type.incompatible)
        s2 = TimeUnit.SECONDS.convert(((@Dimensionless long) (10L)), NANOSECONDS);
    }
}

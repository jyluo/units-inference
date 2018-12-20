import org.checkerframework.framework.qual.PolyAll;
import units.UnitsTools;
import units.qual.*;

import java.util.concurrent.TimeUnit;

class JavaUtilConcurrentTimeUnit {

    void test(long time, TimeUnit unit) throws Exception {
        @ms long milliseconds = unit.toMillis(time);
        Thread.sleep(milliseconds);
    }

    void test2() {
        @ms TimeUnit unit = TimeUnit.MILLISECONDS;
        
        @ns TimeUnit unit2 = TimeUnit.SECONDS;

        unit = unit2;
        
        // convert 10 minutes to milliseconds
        @ms long milliseconds = unit.convert(10L * UnitsTools.ms, TimeUnit.MINUTES);
    }

//    enum MyTimeUnit {
//        @ms MILLISECONDS;
//    }
//
//    void test3() {
//        @ms MyTimeUnit unit = MyTimeUnit.MILLISECONDS;
//    }
}

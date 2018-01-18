// import units.qual.*;
import org.checkerframework.checker.units.qual.*;

class Other {
    public Other() {
        @m int x = 5;
        @s int y = 10;
        calcSpeed(y);

        long ms = toInferMethod(System.currentTimeMillis());

    }

    @m int calcSpeed(@m int distance) {
        return distance;
    }

    long toInferMethod(long input) {
        return input;
    }
}
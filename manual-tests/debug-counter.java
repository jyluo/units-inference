
import static java.lang.Math.*;
import static java.lang.System.*;
import static java.lang.Thread.*;

class MethodCounter {

    public void test() {
        Math.cos(1);
        Math.sin(2);
        Math.tan(3);
        Math.asin(4);
        Math.acos(5);
        Math.atan(6);
        Math.atan2(7, 8);
        Math.sinh(9);
        Math.cosh(10);
        Math.tanh(11);
    }

    void test2() {
        cos(1);
        sin(2);
        tan(3);
        asin(4);
        acos(5);
        atan(6);
        atan2(7, 8);
        sinh(9);
        cosh(10);
        tanh(11);
    }

    void test3() throws InterruptedException {
        System.currentTimeMillis();
        System.nanoTime();
        Thread.sleep(10);
    }

    void test4() throws InterruptedException {
        currentTimeMillis();
        nanoTime();
        sleep(10);
    }
}

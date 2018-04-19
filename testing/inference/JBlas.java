import org.checkerframework.framework.qual.PolyAll;
import units.qual.*;
import units.UnitsTools;

class jBlasCases {
    void system() {
        long savedTime = System.currentTimeMillis();
        double seconds = (double) (System.currentTimeMillis() - savedTime) / 1e3;

        double t = System.nanoTime();
        System.out.printf("%.1fs\n", (System.nanoTime() - t) / 1e9);
    }

    double sinc(double x) {
        if (x == 0)
            return 1.0;
        else
            return Math.sin(Math.PI * x) / (Math.PI * x);
    }
}

class Timer {
    long startTime;
    long stopTime;

    long stop() {
        startTime = System.nanoTime();
        stopTime = System.nanoTime();
        return stopTime - startTime;
    }

    boolean ranFor(double seconds) {
        return (System.nanoTime() - startTime) / 1e9 >= seconds;
    }

    double elapsedSeconds() {
        return (stopTime - startTime) / 1e9;
    }
}


import units.qual.*;
import units.UnitsTools;

class Threads {
    void ThreadTest() throws InterruptedException {
        int msInferred = 10;
        int sleepTime = 10;
        long delta = 20;

        // :: fixable-error: (argument.type.incompatible)
        Thread.sleep(3000);

        // :: fixable-error: (argument.type.incompatible)
        Thread.sleep(msInferred);

        // :: fixable-error: (argument.type.incompatible)
        Thread.sleep(Math.max(sleepTime - delta, 0));

        int msInferred2 = 30;

        Thread t = new Thread();
        // :: fixable-error: (argument.type.incompatible)
        t.join(1000);

        // :: fixable-error: (argument.type.incompatible)
        t.join(msInferred2);
    }
}

import units.qual.*;

class Threads {

    void threadTest() throws InterruptedException {
        int msInferred = 10;
        int sleepTime = 10;
        long delta = 20;

        // :: fixable-error: (argument.type.incompatible)
        Thread.sleep(3000);

        // :: fixable-error: (argument.type.incompatible)
        Thread.sleep(msInferred);

        int msInferred2 = 30;

        Thread t = new Thread();
        // :: fixable-error: (argument.type.incompatible)
        t.join(1000);

        // :: fixable-error: (argument.type.incompatible)
        t.join(msInferred2);
    }
}

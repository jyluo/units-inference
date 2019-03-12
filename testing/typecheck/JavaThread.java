import units.qual.*;

class JavaThread {
    @ms long ms = System.currentTimeMillis();
    @ns int ns = (int) System.nanoTime();

    Thread t;

    void testThread() throws InterruptedException {
        Thread.sleep(ms);
        Thread.sleep(ms, ns);
        t.join(ms);
        t.join(ms, ns);

        // :: error: (argument.type.incompatible)
        Thread.sleep(ns);
        // :: error: (argument.type.incompatible)
        Thread.sleep(ns, ns);
        // :: error: (argument.type.incompatible)
        t.join(ns);
        // :: error: (argument.type.incompatible)
        t.join(ns, ns);
    }

    void testWait() throws InterruptedException {
        t.wait(ms);
        t.wait(ms, ns);
        // :: error: (argument.type.incompatible)
        t.wait(ns);
        // :: error: (argument.type.incompatible)
        t.wait(ns, ns);
    }
}

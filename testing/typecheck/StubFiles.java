import units.qual.*;

class StubFiles {
    void test() {
        // currentTimeMillis() is stubbed to return @ms long
        @ms long k = System.currentTimeMillis();

        // :: error: (assignment.type.incompatible)
        @UnitsBottom long l = System.currentTimeMillis();
    }
}

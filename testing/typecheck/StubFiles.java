import units.qual.*;

class StubFiles {

    public void Main() {
        // currentTimeMillis() is stubbed to return @ms long
        @ms long k = System.currentTimeMillis();

        // :: error: (assignment.type.incompatible)
        @UnitsBottom long l = System.currentTimeMillis();
    }
}

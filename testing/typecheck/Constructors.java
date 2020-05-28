import units.UnitsTools;
import units.qual.*;

class PolyUnitClass {
    @PolyUnit PolyUnitClass(@PolyUnit int x) {}
}

class MeterClass {
    // :: error: (super.invocation.invalid)
    @m MeterClass(@m int x) {}
}

class NoAnnotClass {
    NoAnnotClass(int x) {}
}

class Constructors {
    void polyUnitConstructorTest() {
        // :: error: (assignment.type.incompatible)
        @m PolyUnitClass puc1 = new PolyUnitClass(5);

        PolyUnitClass puc2 = new PolyUnitClass(5 * UnitsTools.m);

        // :: error: (constructor.invocation.invalid)
        PolyUnitClass puc3 = new @m PolyUnitClass(5);

        // :: error: (constructor.invocation.invalid)
        @m PolyUnitClass puc4 = new @m PolyUnitClass(5);

        // :: error: (constructor.invocation.invalid)
        PolyUnitClass puc5 = new @m PolyUnitClass(5 * UnitsTools.s);
    }

    void nonPolyConstructorTest() {
        // :: error: (argument.type.incompatible)
        @m MeterClass mc1 = new MeterClass(5);
        // :: error: (argument.type.incompatible)
        @m MeterClass mc2 = new @m MeterClass(5);

        @Dimensionless NoAnnotClass na1 = new NoAnnotClass(5);
    }
}

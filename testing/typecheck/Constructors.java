import org.checkerframework.framework.qual.PolyAll;
import units.UnitsTools;
import units.qual.*;

@UnknownUnits class PolyAllClass {
    @PolyAll PolyAllClass(@PolyAll int x) {}
}

class PolyUnitClass {
    @PolyUnit PolyUnitClass(@PolyUnit int x) {}
}

class MeterClass {
    @m MeterClass(@m int x) {}
}

class NoAnnotClass {
    NoAnnotClass(int x) {}
}

class Constructors {
    void polyAllConstructorTest() {
        // :: error: (assignment.type.incompatible)
        @m PolyAllClass pac1 = new PolyAllClass(5);

        PolyAllClass pac2 = new PolyAllClass(5 * UnitsTools.m);

        // :: error: (constructor.invocation.invalid)
        PolyAllClass pac3 = new @m PolyAllClass(5);

        // :: error: (constructor.invocation.invalid)
        @m PolyAllClass pac4 = new @m PolyAllClass(5);

        // :: error: (constructor.invocation.invalid)
        PolyAllClass pac5 = new @m PolyAllClass(5 * UnitsTools.s);
    }

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
        // :: error: (constructor.invocation.invalid)
        // :: error: (assignment.type.incompatible)
        @m MeterClass mc1 = new MeterClass(5);
        // :: error: (argument.type.incompatible)
        @m MeterClass mc2 = new @m MeterClass(5);

        @Dimensionless NoAnnotClass na1 = new NoAnnotClass(5);
    }
}

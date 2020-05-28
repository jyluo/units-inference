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
    // TODO: return check isn't quite correct for inner declared classes

    void polyUnitConstructorTest() {
        // propagate @m from assignment context
        // :: fixable-error: (assignment.type.incompatible)
        @m PolyUnitClass puc1 = new PolyUnitClass(5);

        // progagate @m from constructor arg
        PolyUnitClass puc2 = new PolyUnitClass(5 * UnitsTools.m);

        // propagate @m from constructor return type
        // :: fixable-error: (constructor.invocation.invalid)
        PolyUnitClass puc3 = new @m PolyUnitClass(5);

        // :: fixable-error: (constructor.invocation.invalid)
        @m PolyUnitClass puc4 = new @m PolyUnitClass(5);

        // :: fixable-error: (constructor.invocation.invalid)
        PolyUnitClass puc5 = new @m PolyUnitClass(5 * UnitsTools.s);
    }

    void nonPolyConstructorTest() {
        // :: fixable-error: (argument.type.incompatible)
        @m MeterClass mc1 = new MeterClass(5);
        // :: fixable-error: (argument.type.incompatible)
        @m MeterClass mc2 = new @m MeterClass(5);

        @Dimensionless NoAnnotClass na1 = new NoAnnotClass(5);
    }
}

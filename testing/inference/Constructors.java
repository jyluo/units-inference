import org.checkerframework.framework.qual.PolyAll;

import units.UnitsTools;
import units.qual.*;

class PolyAllClass {
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
    // TODO: return check isn't quite correct for inner declared classes
    // class PolyAllClass {
    //     @PolyAll PolyAllClass(@PolyAll int x) {}
    // }

    void polyAllConstructorTest() {
        // propagate @m from assignment context to the constructor arg
        // :: fixable-error: (assignment.type.incompatible)
        @m PolyAllClass pac1 = new PolyAllClass(5);

        // progagate @m from constructor arg to assignment context
        PolyAllClass pac2 = new PolyAllClass(5 * UnitsTools.m);

        // propagate @m from constructor return type to arg and assignment context
        // :: fixable-error: (constructor.invocation.invalid)
        PolyAllClass pac3 = new @m PolyAllClass(5);

        // :: fixable-error: (constructor.invocation.invalid)
        @m PolyAllClass pac4 = new @m PolyAllClass(5);
    }

    void polyUnitConstructorTest() {
        // propagate @m from assignment context to the constructor arg
        // :: fixable-error: (assignment.type.incompatible)
        @m PolyUnitClass puc1 = new PolyUnitClass(5);

        // progagate @m from constructor arg to assignment context
        PolyUnitClass puc2 = new PolyUnitClass(5 * UnitsTools.m);

        // propagate @m from constructor return type to arg and assignment context
        // :: fixable-error: (constructor.invocation.invalid)
        PolyUnitClass puc3 = new @m PolyUnitClass(5);

        // :: fixable-error: (constructor.invocation.invalid)
        @m PolyUnitClass puc4 = new @m PolyUnitClass(5);
    }

    void nonPolyConstructorTest() {
        // :: fixable-error: (argument.type.incompatible) :: fixable-error: (constructor.invocation.invalid) :: fixable-error: (assignment.type.incompatible)
        @m MeterClass mc1 = new MeterClass(5);
        // :: fixable-error: (argument.type.incompatible)
        @m MeterClass mc2 = new @m MeterClass(5);

        @Dimensionless NoAnnotClass na1 = new NoAnnotClass(5);
    }
}

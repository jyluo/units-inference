import org.checkerframework.framework.qual.PolyAll;

import units.UnitsTools;
import units.qual.*;

@UnknownUnits class PolyAllClass {
    @PolyAll PolyAllClass(@PolyAll int x) {
    }
    // @PolyAll PolyAllClass(@PolyAll PolyAllClass x) {}
}

class PolyUnitClass {
    @PolyUnit PolyUnitClass(@PolyUnit int x) {
    }
    // @PolyUnit PolyUnitClass(@PolyUnit PolyUnitClass x) {}
}

class MeterClass {
    @m MeterClass(@m int x) {
    }
}

class NoAnnotClass {
    NoAnnotClass(int x) {
    }
}

class Constructors {
    // TODO: return check isn't quite correct for inner declared classes
    // class PolyAllClass {
    // @PolyAll PolyAllClass(@PolyAll int x) {}
    // }

    void polyAllConstructorTest() {
        // propagate @m from assignment context
        // :: fixable-error: (assignment.type.incompatible)
        @m PolyAllClass pac1 = new PolyAllClass(5);

        // progagate @m from constructor arg
        PolyAllClass pac2 = new PolyAllClass(5 * UnitsTools.m);

        // propagate @m from constructor return type
        // :: fixable-error: (constructor.invocation.invalid)
        PolyAllClass pac3 = new @m PolyAllClass(5);

        // :: fixable-error: (constructor.invocation.invalid)
        @m PolyAllClass pac4 = new @m PolyAllClass(5);

        // :: fixable-error: (constructor.invocation.invalid)
        PolyAllClass pac5 = new @m PolyAllClass(5 * UnitsTools.s);
    }

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
        // :: fixable-error: (argument.type.incompatible) :: fixable-error:
        // (constructor.invocation.invalid) :: fixable-error:
        // (assignment.type.incompatible)
        @m MeterClass mc1 = new MeterClass(5);
        // :: fixable-error: (argument.type.incompatible)
        @m MeterClass mc2 = new @m MeterClass(5);

        @Dimensionless NoAnnotClass na1 = new NoAnnotClass(5);
    }

    // if polymorphic var slots are inserted then this test fails as there are
    // missing pairs of round brackets
    // void chainPolyConstructorTest() {
    // // propagate @m from assignment context
    // // :: fixable-error: (assignment.type.incompatible)
    // @m PolyAllClass pacc1 = new PolyAllClass(new PolyAllClass(5));
    //
    // // progagate @m from constructor arg
    // PolyAllClass pacc2 = new PolyAllClass(new PolyAllClass(5 *
    // UnitsTools.m));
    //
    // // propagate @m from constructor return type
    // // :: fixable-error: (constructor.invocation.invalid)
    // PolyAllClass pacc3 = new @m PolyAllClass(new PolyAllClass(5));
    //
    // // propagate @m from constructor return type
    // // :: fixable-error: (constructor.invocation.invalid)
    // PolyAllClass pacc4 = new PolyAllClass(new @m PolyAllClass(5));
    // }
}

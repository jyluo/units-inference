import org.checkerframework.framework.qual.PolyAll;
import units.qual.*;
import units.UnitsTools;

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

    void callTest() {
        // :: fixable-error: (assignment.type.incompatible)
        @m PolyAllClass pac1 = new PolyAllClass(5);
        // :: fixable-error: (constructor.invocation.invalid)
        @m PolyAllClass pac2 = new @m PolyAllClass(5);

        // :: fixable-error: (assignment.type.incompatible)
        @m PolyUnitClass puc1 = new PolyUnitClass(5);
        // :: fixable-error: (constructor.invocation.invalid)
        @m PolyUnitClass puc2 = new @m PolyUnitClass(5);
        
        // :: fixable-error: (argument.type.incompatible) :: fixable-error: (constructor.invocation.invalid) :: fixable-error: (assignment.type.incompatible)
        @m MeterClass mc1 = new MeterClass(5);
        // :: fixable-error: (argument.type.incompatible)
        @m MeterClass mc2 = new @m MeterClass(5);
    }
}
